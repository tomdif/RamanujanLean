"""Atkin basis g2,g3,g4,g6 for M^0_Z(11) via Paule-Radu Thm 3.9 / (76)-(79),(100); verify integrality, leading terms,
and Atkin's witness identity L1 = U11(phi) = 11^4 z + 11 g2 + 2*11^2 g3 + 11^3 g4."""
import sys
from qs import *

def basis(N):
    M = 2*N + 40
    f2 = etaq({1:1, 2:3, 11:-3, 22:-1}, -2, M)
    f3 = etaq({1:3, 2:1, 11:-1, 22:-3}, -3, M)
    if2, if3 = f2.inv(), f3.inv()
    U2 = lambda x: x.U(2)
    g2 = U2(if2) - if3
    g3 = fmpq(4,11)*U2(if3) - fmpq(1,11)*if2
    g4 = if3*if3 + fmpq(1,2)*U2(if2*if2) - fmpq(1,2)*g3
    J3 = 11**3 * g3
    J4 = 11**4 * (if3*if3 + fmpq(1,2)*U2(if2*if2))
    J6 = 11**4 * (if2*if2 + 8*U2(if3*if3))
    z = etaq({11:12, 1:-12}, 5, M)
    g6 = fmpq(1, 11**6)*J6 - fmpq(8, 11**6)*J4 + fmpq(4, 11**5)*J3 + z
    cut = lambda x: S(x.p, x.v, min(x.N, N))
    return {k: cut(v) for k, v in dict(z=z, g2=g2, g3=g3, g4=g4, g6=g6).items()}

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    B = basis(N)
    for k, v in B.items():
        ok = all(c.q == 1 for c in v.p.coeffs())
        print(k, "integral to q^%d:" % v.N, ok, "| lead", v.lead(), "|", [int(v.coeff(n)) for n in range(0, 10)])
    # L1 = U11(phi), phi = q^5 E(q^121)/E(q)
    phi = etaq({121:1, 1:-1}, 5, 11*N + 11)
    L1 = phi.U(11)
    rhs = 11**4*B["z"] + 11*B["g2"] + 2*11**2*B["g3"] + 11**3*B["g4"]
    d = L1 - rhs
    print("L1 - (11^4 z + 11 g2 + 242 g3 + 1331 g4) == 0 mod q^%d:" % d.N, d.is_zero())
    # also check L1 = q * E(q^11) * sum p(11n+6) q^n
    from sympy.functions.combinatorial.numbers import partition as npartitions
    E11 = euler(11, N)
    P = S(fmpq_poly([int(npartitions(11*n+6)) for n in range(N)]), 1, N+1)
    print("L1 == q E(q^11) sum p(11n+6)q^n:", (L1 - E11*P).is_zero())
