"""11-dissection of Euler's product: E(q) = E(q^121) * ( sum_{r in {0,1,2,4,7}} q^r A_r(q^11) + q^5 ),
identify each A_r(Q) as +-Q^c * theta_a(Q)/theta_b(Q),  theta_a(Q) = (Q^a;Q^11)(Q^{11-a};Q^11)(Q^11;Q^11)."""
from qs import *
N = 4000
E = euler(1, N)
E121 = euler(121, N)
R = E * E121.inv()
comps = {}
for r in range(11):
    c = [R.coeff(11*m + r) for m in range(0, (N - r)//11)]
    comps[r] = S(fmpq_poly(c), 0, (N - r)//11)
nonzero = [r for r in range(11) if not comps[r].is_zero()]
print("nonzero residue classes:", nonzero)
M = N//11
def theta(a, M):
    # prod (1-Q^{11n+a})(1-Q^{11n+11-a})(1-Q^{11n+11})
    c = [0]*M; c[0] = 1
    p = fmpq_poly([1])
    for n in range(0, M):
        for e in (11*n + a, 11*n + 11 - a, 11*n + 11):
            if e < M: p = fmpq_poly((p * fmpq_poly([1] + [0]*(e-1) + [-1])).coeffs()[:M])
    return S(p, 0, M)
th = {a: theta(a, M) for a in range(1, 6)}
for r in nonzero:
    A = comps[r]
    found = []
    for a in range(1, 6):
        for b in range(1, 6):
            t = th[a] * th[b].inv()
            for sgn in (1, -1):
                for c in range(-3, 4):
                    cand = S(t.p * sgn, t.v + c, min(t.N + c, A.N))
                    d = A - cand
                    d = S(d.p, d.v, min(d.N, M - 5))
                    if d.is_zero(): found.append((sgn, c, a, b))
    print(f"r={r}: A_r = {A}  identified as (sign, Q-shift, a, b) with A_r = sign*Q^shift*theta_a/theta_b:", found)
