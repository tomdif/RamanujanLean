"""Independent high-precision verification of the core identities (A) modular equation, (B) structure relations,
(D) z(q) z(q^11) = phi^12, plus the j-invariant of the Weierstrass model 11 y^2 + 12 x y + y = 11 x^3 + x^2 (x=g2,y=g3)."""
import sys
from fractions import Fraction as Fr
from qs import *
from atkin_basis import basis
from induct_check import E
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
Bq = basis(N//11 + 30)          # basis at precision for q^11 substitution
B = basis(N + 30)
g = {1: B["g2"], 2: B["g3"], 3: B["g4"], 4: B["g6"]}
z = B["z"]
# (B) relations
r1 = g[1]*g[2] - (g[1]*g[1] - g[2] + 11*z)
r2 = g[2]*g[2] - (g[1]*g[1]*g[1] - g[1]*g[2] - z)
r3 = g[3] - (g[1]*g[1] - g[2]); r4 = g[4] - g[1]*g[3]
print("R1: g2 g3 = g2^2 - g3 + 11 z           :", r1.is_zero(), "mod q^%d" % r1.N)
print("R2: g3^2 = g2^3 - g2 g3 - z             :", r2.is_zero(), "mod q^%d" % r2.N)
print("g4 = g2^2 - g3, g6 = g2 g4               :", r3.is_zero() and r4.is_zero())
# (D)
phi = etaq({121: 1, 1: -1}, 5, N)
d = z*z.subs(11) - phi**12
print("z(q) z(q^11) = phi^12                    :", S(d.p, d.v, min(d.N, N)).is_zero())
# (A) phi^11 = sum (-1)^{j+1} e_j(q^11) phi^{11-j}
Jq = {0: const(1, N//11 + 30), 1: Bq["g2"], 2: Bq["g3"], 3: Bq["g4"], 5: Bq["z"]}
lhs = phi**11; rhs = None
pw = [const(1, N)]
for i in range(11): pw.append(pw[-1]*phi)
for j, e in E.items():
    ej = None
    for nu, c in e.items():
        t = c*Jq[nu]; ej = t if ej is None else ej + t
    term = ((-1)**(j+1))*ej.subs(11)*pw[11-j]
    rhs = term if rhs is None else rhs + term
dd = lhs - rhs
print("(A) degree-11 modular equation           :", dd.is_zero(), "mod q^%d" % dd.N)
# j-invariant
a1, a2, a3, a4, a6 = Fr(12, 11), Fr(1, 11), Fr(1, 11), Fr(0), Fr(0)
b2 = a1*a1 + 4*a2; b4 = 2*a4 + a1*a3; b6 = a3*a3 + 4*a6
b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
c4 = b2*b2 - 24*b4; Delta = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
print("j(11y^2+12xy+y=11x^3+x^2) =", c4**3/Delta, "; j(11a1) = -122023936/161051 =", Fr(-122023936, 161051))
