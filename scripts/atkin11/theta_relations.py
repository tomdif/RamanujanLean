"""Find low-degree polynomial relations among the 11-dissection components A_r(Q) (r=0,1,2,4,7) of E(q)/E(q^121)
with polynomial-in-Q coefficients (analog of the 4 relations hg1..hg4 among x,y,z in the 7-case).
A_0 = th4/th2, A_1 = -th2/th1, A_2 = -th5/th3, A_4 = -Q th1/th5, A_7 = th3/th4, th_a = (Q^a,Q^{11-a},Q^11;Q^11)_inf."""
import sys, itertools
from qs import *
from flint import nmod_mat, fmpq_poly
D = int(sys.argv[1]) if len(sys.argv) > 1 else 3; K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
M = 700
def theta(a, M):
    p = fmpq_poly([1])
    for n in range(0, M):
        for e in (11*n + a, 11*n + 11 - a, 11*n + 11):
            if e < M: p = fmpq_poly((p * fmpq_poly([1] + [0]*(e-1) + [-1])).coeffs()[:M])
    return S(p, 0, M)
th = {a: theta(a, M) for a in range(1, 6)}
A = {0: th[4]*th[2].inv(), 1: -1*th[2]*th[1].inv(), 2: -1*th[5]*th[3].inv(), 4: -1*S(th[1].p, 1, M+1)*th[5].inv(), 7: th[3]*th[4].inv()}
keys = [0, 1, 2, 4, 7]
mons = [m for d in range(0, D + 1) for m in itertools.combinations_with_replacement(keys, d)]
cols = []; names = []
for m in mons:
    t = const(1, M)
    for r in m: t = t * A[r]
    for k in range(K + 1):
        cols.append(S(t.p, t.v + k, t.N + k)); names.append((m, k))
p = 1000003
def md(x): return (int(x.p) % p) * pow(int(x.q) % p, -1, p) % p
rows = range(0, M - K - 5)
Mat = nmod_mat(len(rows), len(cols), [md(c.coeff(n)) for n in rows for c in cols], p)
X, nul = Mat.nullspace()
print(f"degree<= {D} in A's, Q-degree <= {K}: {len(cols)} monomials, nullity = {nul}")
# print relations with small coefficients (lift symmetric residues)
def lift(x): x = int(x); return x - p if x > p//2 else x
for j in range(nul):
    v = [lift(X[i, j]) for i in range(len(cols))]
    nz = [(names[i], v[i]) for i in range(len(cols)) if v[i] != 0]
    if len(nz) <= 8 and all(abs(c) < 10**4 for _, c in nz):
        print("  ", " + ".join(f"{c}*Q^{k}*" + "*".join(f"A{r}" for r in m) for (m, k), c in nz), "= 0")
