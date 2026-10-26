"""Parse Paule-Radu's degree-55 modular equation F11(X,Y) (X=z(tau), Y=z(11 tau)) from RISC site;
check Corollary 5.6 valuations  v11[Y^k] a_i >= ceil((11k+i-55)/2), report sizes, and verify F11(z(q),z(q^11))=0 mod q^N."""
import re, sys
from sympy import symbols, Poly
from sympy.parsing.sympy_parser import parse_expr
X, Y = symbols("X Y")
s = open("dl/polynomial11_2.txt").read().strip().rstrip(";").split(":=")[1].replace(" ", "").replace("\n", "")
d = {}
def parse_inner(inner, i):
    for m in re.finditer(r'([+-]?)(\d*)\*?(Y(\^(\d+))?)?', inner):
        sg, c, yy, _, e = m.groups()
        if not c and not yy: continue
        c = int(c) if c else 1
        k = (int(e) if e else 1) if yy else 0
        d[(i, k)] = d.get((i, k), 0) + (-c if sg == '-' else c)
pos = 0
for m in re.finditer(r'([+-]?)\(([^()]*)\)\*X(\^(\d+))?', s):
    i = int(m.group(4)) if m.group(4) else 1
    inner = m.group(2)
    if m.group(1) == '-': raise SystemExit("unexpected sign")
    parse_inner(inner, i)
rest = re.sub(r'([+-]?)\(([^()]*)\)\*X(\^(\d+))?', '', s)
print("leftover outside parentheses:", rest)
for t in re.findall(r'[+-]?[^+-]+', rest):
    t = t.strip()
    if t in ("-Y^5",): d[(0, 5)] = d.get((0, 5), 0) - 1
    elif t in ("+X^55", "X^55"): d[(55, 0)] = 1
    else: raise SystemExit("unparsed " + t)
d = {k: v for k, v in d.items() if v != 0}
print("terms:", len(d), "deg_X:", max(i for i, k in d), "deg_Y:", max(k for i, k in d), "max digits:", max(len(str(abs(c))) for c in d.values()))
def v11(n):
    n = abs(int(n)); v = 0
    while n % 11 == 0: n //= 11; v += 1
    return v
viol = 0; slack = []
for (i, k), c in d.items():
    if i == 55: continue
    b = -((-(11*k + i - 55))//2)
    if v11(c) < b: viol += 1
    slack.append(v11(c) - b)
print("Cor 5.6 valuation bound violations:", viol, "| min slack:", min(slack))
krange = {}
for (i, k) in d:
    krange.setdefault(i, []).append(k)
print("Y-degree range of a_i for i=0,1,27,54:", [(i, min(krange[i]), max(krange[i])) for i in (0, 1, 27, 54)])
# numeric check: F(z(q), z(q^11)) = 0 mod q^N, exact, with flint
from qs import etaq
from flint import fmpz_poly
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
z = etaq({11: 12, 1: -12}, 5, N)
zp = [fmpz_poly([1])]; zq = fmpz_poly([int(c) for c in z.p.coeffs()]) * fmpz_poly([0]*5 + [1])
def trunc(p): return fmpz_poly(p.coeffs()[:N])
for i in range(55): zp.append(trunc(zp[-1]*zq))
ZY = [fmpz_poly([1])]; zyq = fmpz_poly([int(c) if j % 11 == 0 else 0 for j, c in enumerate(z.subs(11).p.coeffs())])
zyq = fmpz_poly(([0]*55 + [int(c) for c in z.subs(11).p.coeffs()])[:N])
for k in range(56): ZY.append(trunc(ZY[-1]*zyq))
acc = fmpz_poly([])
for (i, k), c in d.items():
    if 5*i + 55*k >= N: continue
    acc += trunc(zp[i]*ZY[k]) * int(c)
acc = trunc(acc)
print("F11(z(q), z(q^11)) == 0 mod q^%d:" % N, all(x == 0 for x in acc.coeffs()), "(only terms with 5i+55k<N contribute)")
