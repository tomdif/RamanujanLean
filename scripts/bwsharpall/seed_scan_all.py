#!/usr/bin/env python3
"""Seed survival (G5) and mod-ell cyclicity of L(1), prime by prime, in the
truncated Katz model of scripts/frontier/pattern/katzmat.py (precision ell^2).

For each prime p it records
  * s = dim K (kernel of D-bar on S_{p-1}), rank of Theta, whether the seed
    u0 is nonzero and whether Theta^s u0 != 0 (exact seed survival);
  * the Krylov rank of L-bar(1) under X-bar mod p (the precision-one rank,
    which is 24 = R-1 at p = 607) and R = floor((p+12)/24).

Numerical evidence only (bounded Katz model, cutoff N). Not a proof.
The algorithm is that of scripts/frontier/pattern/seed_survival_scan.py; the
cache is kept in scripts/bwsharpall/cache so that the shared cache is untouched.
"""
import os, sys, time, json
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'frontier' / 'pattern'))
from katzmat import get
from flint import nmod_mat, nmod_poly
import sympy

CACHE = str(HERE / 'cache')


def run(p, N):
    st = time.time(); d = get(p, 2, N, cachedir=CACHE); q = p * p; n = d['dN']
    d1 = d['dims'][1] - 1; ix = list(range(1, d1 + 1))
    U = nmod_mat(d['U'], q); D = nmod_mat(d['D'], q); X = D * U
    Uf = nmod_mat([[d['U'][i][j] % p for j in ix] for i in ix], p)
    Df = nmod_mat([[d['D'][i][j] % p for j in ix] for i in ix], p)
    ns, k = Df.nullspace(); Kb = [[int(ns[i, j]) for i in range(d1)] for j in range(k)]
    UV = Uf * Df; cols = []
    for j in range(d1):
        c = [int(UV[i, j]) for i in range(d1)]
        if nmod_mat(cols + [c], p).rank() > len(cols): cols.append(c)
    B = nmod_mat([[row[i] for row in cols + Kb] for i in range(d1)], p); assert B.rank() == d1
    Bi = B.inv(); r = len(cols)

    def project(vec):
        z = Bi * nmod_mat([[int(vec[i, 0]) % p] for i in ix], p)
        return [int(z[r + j, 0]) for j in range(k)]
    tc = []
    for col in Kb:
        l = nmod_mat([[0] for _ in range(n)], q)
        for i, x in zip(ix, col): l[i, 0] = x
        y = D * l; assert all(int(y[i, 0]) % p == 0 for i in range(n))
        w = nmod_mat([[int(y[i, 0]) // p] for i in range(n)], q)
        tc.append(project(U * w))
    T = nmod_mat([[tc[j][i] for j in range(k)] for i in range(k)], p)
    Xf = nmod_mat([[int(X[i, j]) % p for j in range(n)] for i in range(n)], p)
    cp = Xf.charpoly(); cs = list(map(int, cp.coeffs())); s0 = next(i for i, x in enumerate(cs) if x)
    g = nmod_poly(cs[s0:], p); xp = nmod_poly([0] * s0 + [1], p); gcd, a, b = xp.xgcd(g)
    assert gcd == nmod_poly([1], p)
    e = a * xp
    eco = list(map(int, e.coeffs()))
    L1 = nmod_mat([[d['D'][i][0]] for i in range(n)], q)

    def P0(v):
        out = nmod_mat([[0] for _ in range(n)], q)
        for c in reversed(eco): out = X * out + c * v
        return out
    z1 = P0(L1); z2 = P0(z1); z3 = P0(z2); ordinary = 3 * z2 - 2 * z3
    z = L1 - ordinary; uz = U * z; assert all(int(uz[i, 0]) % p == 0 for i in range(n))
    seed = project(nmod_mat([[int(uz[i, 0]) // p] for i in range(n)], q))
    seedv = nmod_mat([[x] for x in seed], p); last = seedv
    for _ in range(k): last = T * last
    alive = any(int(last[i, 0]) for i in range(k))
    # Krylov rank of L-bar(1) under X-bar (precision-one rank)
    v = nmod_mat([[int(L1[i, 0]) % p] for i in range(n)], p); vecs = []
    R = (p + 12) // 24
    for _ in range(R + 2):
        vecs.append([int(v[i, 0]) for i in range(n)]); v = Xf * v
    kry = nmod_mat(vecs, p).rank()
    res = dict(prime=p, katz_cutoff=N, s=k, R=R, unit_rank=r, theta_rank=T.rank(),
               seed_nonzero=any(seed), survives=alive, krylov_rank_L1=kry,
               seconds=round(time.time() - st, 1))
    print(res, flush=True)
    return res


if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2]); out = Path(sys.argv[3])
    N = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    results = json.loads(out.read_text())['results'] if out.exists() else []
    done = {r['prime'] for r in results}
    for p in sympy.primerange(lo, hi + 1):
        if p in done: continue
        results.append(run(p, N))
        out.write_text(json.dumps({'status': 'numerical, truncated Katz model (cutoff N); not a proof',
                                   'results': results}, indent=1) + '\n')
