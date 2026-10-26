"""Which elements of V(q) lie in V(q^11)[phi] (no denominators)?  Nullspace mod p of
   sum_nu a_nu J_nu(q) - sum_{k=0}^{10} sum_mu c_{k,mu} J_mu(q^11) phi^k = 0 ."""
import sys
from qs import *
from gordon_matrix import Ctx
from flint import nmod_mat
NU0, NU1, MU0, MU1, NQ = map(int, sys.argv[1:6])
p = 1000003
ctxq = Ctx(NQ + 400); ctxQ = Ctx(NQ//11 + 200)
phi = etaq({121: 1, 1: -1}, 5, NQ + 1500)
pw = [const(1, NQ + 1500)]
for k in range(10): pw.append(pw[-1]*phi)
cols = []; names = []
for nu in range(NU0, NU1 + 1):
    cols.append(ctxq.J(nu, NQ + 300)); names.append(("q", nu))
for k in range(11):
    for mu in range(MU0, MU1 + 1):
        cols.append(ctxQ.J(mu, NQ//11 + 150).subs(11) * pw[k]); names.append(("Q", k, mu))
lo = min(c.v for c in cols); hi = NQ
def md(x): return (int(x.p) % p) * pow(int(x.q) % p, -1, p) % p
M = nmod_mat(hi - lo, len(cols), [md(c.coeff(n)) for n in range(lo, hi) for c in cols], p)
r = M.rank()
print("rows", hi - lo, "cols", len(cols), "rank", r, "nullity", len(cols) - r)
# nullspace and projection to J_nu(q), nu not = 0 mod 5
X, nul = M.nullspace()
nq = NU1 - NU0 + 1
proj = nmod_mat(nq, nul, [X[i, j] for i in range(nq) for j in range(nul)], p) if nul else None
if nul:
    print("rank of projection onto J_nu(q) coordinates:", proj.rank())
    gi = [i for i in range(nq) if (NU0 + i) % 5 != 0]
    P2 = nmod_mat(len(gi), nul, [X[i, j] for i in gi for j in range(nul)], p)
    print("rank of projection onto non-z-power coordinates (g-part):", P2.rank())
