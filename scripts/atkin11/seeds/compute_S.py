"""H2 data: P'(phi) * g_i(q) = S_i(phi) with S_i(Y) = sum_m Y^m sum_nu s_{i,m,nu} J_nu(q^11), for g_i = g2, g3, g4, g6.
Solved exactly from q-expansions (express_in_phi.py, dP mode); writes S.json."""
import sys, json
sys.path.insert(0, '..')
from qs import *
from gordon_matrix import Ctx
from induct_check import E
from flint import fmpq_mat

NU1 = int(sys.argv[1]) if len(sys.argv) > 1 else 40
NQ = int(sys.argv[2]) if len(sys.argv) > 2 else 2200
ctx = Ctx(NQ // 11 + 200)
phi = etaq({121: 1, 1: -1}, 5, NQ + 1200)
pw = {0: const(1, NQ + 1200)}
for k in range(1, 11): pw[k] = pw[k-1] * phi
CT = Ctx(NQ + 60)
Nloc = NQ // 11 + 50
dP = 11 * pw[10]
for j in range(1, 11):
    ej = None
    for nu, c in E[j].items():
        t = c * ctx.J(nu, Nloc)
        ej = t if ej is None else ej + t
    dP = dP + ((-1)**j * (11 - j)) * ej.subs(11) * pw[10 - j]
cols, names = [], []
for k in range(0, 11):
    for nu in range(0, NU1 + 1):
        cols.append(ctx.J(nu, NQ // 11 + 150).subs(11) * pw[k]); names.append((k, nu))
out = {}
for which in (1, 2, 3, 4):
    target = dP * CT.g[which]
    lo = min(c.v for c in cols + [target]); rows = list(range(lo, NQ - 1))
    A = fmpq_mat(len(rows), len(cols) + 1)
    for r, n in enumerate(rows):
        for j, c in enumerate(cols): A[r, j] = c.coeff(n)
        A[r, len(cols)] = target.coeff(n)
    R, rank = A.rref()
    assert rank == len(cols), ("rank", rank)
    sol = {}
    for i in range(rank):
        pc = next(j for j in range(len(cols) + 1) if R[i, j] != 0)
        assert pc < len(cols), "NO SOLUTION"
        sol[names[pc]] = R[i, len(cols)]
    S = [[0] * (NU1 + 1) for _ in range(11)]
    for (k, nu), c in sol.items():
        assert c.q == 1, ("non-integral", which, k, nu, c)
        S[k][nu] = int(c.p)
    mx = max(nu for (k, nu), c in sol.items() if c != 0)
    print("g index", which, ": nonzero", sum(1 for c in sol.values() if c != 0), "max nu", mx,
          "max digits", max(len(str(abs(x))) for row in S for x in row))
    assert mx < NU1 - 3, "window too small"
    out[which] = S
json.dump(out, open('S.json', 'w'))
