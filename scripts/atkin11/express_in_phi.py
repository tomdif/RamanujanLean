"""Test: is g_i(q) in  sum_{k=K0}^{K1} V(q^11) * phi(q)^k ?  Solve exactly for c_{k,nu} with
   g(q) = sum_{k,nu} c_{k,nu} J_nu(q^11) phi(q)^k ."""
import sys
from qs import *
from gordon_matrix import Ctx
from flint import fmpq_mat
which = int(sys.argv[1]); K0, K1 = int(sys.argv[2]), int(sys.argv[3]); NU0, NU1 = int(sys.argv[4]), int(sys.argv[5])
NQ = int(sys.argv[6]) if len(sys.argv) > 6 else 900
ctx = Ctx(NQ//11 + 200)
phi = etaq({121: 1, 1: -1}, 5, NQ + 1200)
phii = phi.inv()
pw = {0: const(1, NQ + 1200)}
for k in range(1, max(K1, 10) + 1): pw[k] = pw[k-1]*phi
for k in range(-1, min(K0, 0) - 1, -1): pw[k] = pw[k+1]*phii
CT = Ctx(NQ + 60); target = CT.g[which] if which < 5 else CT.z
if len(sys.argv) > 7 and sys.argv[7] == "dP":
    # multiply by P'(phi) = 11 phi^10 + sum_{j=1}^{10} (-1)^j (11-j) e_j(q^11) phi^{10-j}
    from induct_check import E
    Nloc = NQ//11 + 50
    dP = 11*pw[10]
    for j in range(1, 11):
        ej = None
        for nu, c in E[j].items():
            t = c*ctx.J(nu, Nloc)
            ej = t if ej is None else ej + t
        dP = dP + ((-1)**j*(11-j))*ej.subs(11)*pw[10-j]
    target = dP*target
    print("target = P'(phi) * g")
cols, names = [], []
for k in range(K0, K1 + 1):
    for nu in range(NU0, NU1 + 1):
        f = ctx.J(nu, NQ//11 + 150).subs(11) * pw[k]
        cols.append(f); names.append((k, nu))
lo = min(c.v for c in cols + [target]); hi = NQ - 1
rows = list(range(lo, hi))
A = fmpq_mat(len(rows), len(cols) + 1)
for r, n in enumerate(rows):
    for j, c in enumerate(cols):
        try: A[r, j] = c.coeff(n)
        except ValueError: raise SystemExit("precision too low for col %s" % (names[j],))
    A[r, len(cols)] = target.coeff(n)
if "--modp" in sys.argv:
    from flint import nmod_mat
    p = 1000003
    def md(x): return (int(x.p) % p) * pow(int(x.q) % p, -1, p) % p
    Am = nmod_mat(len(rows), len(cols), [md(A[r, j]) for r in range(len(rows)) for j in range(len(cols))], p)
    Ab = nmod_mat(len(rows), len(cols)+1, [md(A[r, j]) for r in range(len(rows)) for j in range(len(cols)+1)], p)
    print("mod p ranks: A=%d [A|b]=%d unknowns=%d -> %s" % (Am.rank(), Ab.rank(), len(cols), "SOLVABLE" if Am.rank()==Ab.rank() else "NO SOLUTION"))
    sys.exit(0)
R, rank = A.rref()
sol = {}
for i in range(rank):
    pc = next(j for j in range(len(cols) + 1) if R[i, j] != 0)
    if pc == len(cols): print("NO SOLUTION in this window"); sys.exit(0)
    sol[names[pc]] = R[i, len(cols)]
free = len(cols) - rank
print("solution found; rank %d / %d unknowns (free params %d), rows %d" % (rank, len(cols), free, len(rows)))
for (k, nu), c in sorted(sol.items()):
    if c != 0: print(f"  phi^{k} * J_{nu}(q^11): {c}")
