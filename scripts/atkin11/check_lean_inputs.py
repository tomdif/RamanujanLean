"""Independent check that Atkin11.Inputs (as stated in RamanujanTau/Atkin11Defs.lean, with the seed data parsed
from RamanujanTau/Atkin11Data.lean) holds numerically: R2, the modular equation, and all 55 seeds, to q^N."""
import re, sys
from qs import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 120
M = 11*N + 700
f2i = etaq({11:3, 22:1, 1:-1, 2:-3}, 2, 2*M)
f3i = etaq({11:1, 22:3, 1:-3, 2:-1}, 3, 2*M)
g2 = f2i.U(2) - f3i
z = etaq({11:12, 1:-12}, 5, M)
g3 = (g2*g2 + 11*z) * (1 + g2).inv()
g4 = g2*g2 - g3; g6 = g2*g4
gi = [const(1, M), g2, g3, g4, g6]
def J(nu):
    a, i = divmod(nu, 5); r = gi[i]
    for _ in range(a): r = r*z
    return r
def trunc(s, n): return S(s.p, s.v, min(s.N, n))
def iszero(s, n):
    return all(s.coeff(k) == 0 for k in range(max(s.v, 0), n))
print("R2:", iszero(g3*g3 - (g2*g2*g2 - g2*g3 - z), N*5))
src = open('../../RamanujanTau/Atkin11Bound.lean').read()
E = {1: {1: 121, 2: 2662, 3: 14641, 5: 161051}, 2: {1: -11, 2: 968, 3: 11979, 5: 161051},
     3: {2: 242, 3: 5324, 5: 73205}, 4: {2: 22, 3: 1452, 5: 14641}, 5: {3: 242, 5: -1331},
     6: {3: 22, 5: -1331}, 7: {5: -121}, 8: {5: 121}, 9: {5: 55}, 10: {5: 11}, 11: {5: 1}}
for j, d in E.items():  # cross-check against the Lean source
    for b, c in d.items(): assert f"({b}, {c})" in src, (j, b, c)
phi = etaq({121:1, 1:-1}, 5, M)
rhs = const(0, M)
for j in range(11):
    e = const(0, M)
    for b, c in E[j+1].items(): e = e + c*J(b)
    rhs = rhs + ((-1)**j) * e.subs(11) * phi**(10-j)
print("modeq:", iszero(phi**11 - rhs, 300))
data = open('../../RamanujanTau/Atkin11Data.lean').read()
rows = {}
for m in re.finditer(r"def seedRow(\d+) : List \(Nat × Int\) := \[(.*?)\]\n", data):
    rows[int(m.group(1))] = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (-?\d+)\)", m.group(2))]
assert len(rows) == 55
ok = True
for lam in range(11):
    for i in range(5):
        lhs = (phi**lam * J(i)).U(11)
        r = const(0, M)
        for nu, c in rows[5*lam+i]: r = r + c*J(nu)
        good = iszero(lhs - r, N)
        ok = ok and good
        if not good: print("seed FAIL", lam, i)
print("all 55 seeds:", ok)
