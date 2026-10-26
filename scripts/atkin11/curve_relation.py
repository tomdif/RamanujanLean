"""X0(11) in Atkin coordinates: g3 = (g2^2 + 11 z)/(1 + g2) (from R1), and R2 becomes a polynomial relation P(g2, z) = 0."""
from sympy import symbols, expand, factor, Poly
from qs import *
from atkin_basis import basis
x, Z = symbols("x z")
y = (x**2 + 11*Z)/(1 + x)
P = expand(((y**2 - (x**3 - x*y - Z))*(1 + x)**2).cancel())
print("P(g2,z) =", factor(P))
print("as poly in z:", Poly(P, Z).all_coeffs())
B = basis(1500)
g2, z = B["g2"], B["z"]
val = None
for (i, j), c in Poly(P, x, Z).as_dict().items():
    t = int(c) * (g2**i if i else const(1, 1500)) * (z**j if j else const(1, 1500))
    val = t if val is None else val + t
print("P(g2(q), z(q)) == 0 mod q^%d:" % val.N, val.is_zero())
g3 = (g2*g2 + 11*z) * (1 + g2).inv()
print("g3 == (g2^2+11z)/(1+g2):", (g3 - B["g3"]).is_zero())
