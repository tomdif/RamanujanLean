"""Is Atkin's g2 (and g3, z) a polynomial in the 11-dissection components A_r of E (theta quotients of level 11)?"""
import sys, itertools
from qs import *
from flint import nmod_mat, fmpq_poly
from atkin_basis import basis
D, K = int(sys.argv[1]), int(sys.argv[2]); which = sys.argv[3]
M = int(sys.argv[4]) if len(sys.argv) > 4 else 1200
def theta(a, M):
    p = fmpq_poly([1])
    for n in range(0, M):
        for e in (11*n + a, 11*n + 11 - a, 11*n + 11):
            if e < M: p = fmpq_poly((p * fmpq_poly([1] + [0]*(e-1) + [-1])).coeffs()[:M])
    return S(p, 0, M)
th = {a: theta(a, M) for a in range(1, 6)}
An = {0: th[4]*th[2].inv(), 1: -1*th[2]*th[1].inv(), 2: -1*th[5]*th[3].inv(), 4: -1*S(th[1].p, 1, M+1)*th[5].inv(), 7: th[3]*th[4].inv()}
B = basis(M)
target = B[which]
keys = [0, 1, 2, 4, 7]
cols = []; names = []
for d in range(0, D + 1):
    for m in itertools.combinations_with_replacement(keys, d):
        t = const(1, M)
        for r in m: t = t * An[r]
        for k in range(K + 1):
            cols.append(S(t.p, t.v + k, t.N + k)); names.append((m, k))
p = 1000003
def md(x): return (int(x.p) % p) * pow(int(x.q) % p, -1, p) % p
rows = range(0, M - K - 30)
A = nmod_mat(len(rows), len(cols), [md(c.coeff(n)) for n in rows for c in cols], p)
Ab = nmod_mat(len(rows), len(cols) + 1, [md(c.coeff(n)) for n in rows for c in cols + [target]], p)
print(f"{which} in span of A-monomials deg<={D}, Q^<= {K}?", "YES" if A.rank() == Ab.rank() else "NO", f"(rank {A.rank()} vs {Ab.rank()})")
