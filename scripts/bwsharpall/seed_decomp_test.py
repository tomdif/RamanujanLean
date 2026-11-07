#!/usr/bin/env python3
"""Exploratory: split the seed u0 of L(1) along the exact identity
   L(1) = W * U(Delta^delta)  (mod ell^2),  W = (q^ell;q^ell)/(q;q)^ell = 1 + ell*w,
and ask whether the classical part G = U(Delta^delta) (as a weight-0 Katz series,
G/E^((ell+1)/2)) carries the seed, or the correction. Numerical only."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'frontier' / 'pattern'))
from katzmat import Katz
from flint import nmod_mat, nmod_poly

def seeds(p, N=3):
    K = Katz(p, 2, N); q = p * p
    Um, Dm = K.matrices(); n = K.dN
    U = nmod_mat(Um.tolist(), q); D = nmod_mat(Dm.tolist(), q); X = D * U
    d1 = K.dims[1] - 1; ix = list(range(1, d1 + 1))
    Uf = nmod_mat([[int(Um[i, j]) % p for j in ix] for i in ix], p)
    Df = nmod_mat([[int(Dm[i, j]) % p for j in ix] for i in ix], p)
    ns, k = Df.nullspace(); Kb = [[int(ns[i, j]) for i in range(d1)] for j in range(k)]
    UV = Uf * Df; cols = []
    for j in range(d1):
        c = [int(UV[i, j]) for i in range(d1)]
        if nmod_mat(cols + [c], p).rank() > len(cols): cols.append(c)
    B = nmod_mat([[row[i] for row in cols + Kb] for i in range(d1)], p); Bi = B.inv(); r = len(cols)
    def project(vec):
        z = Bi * nmod_mat([[int(vec[i, 0]) % p] for i in ix], p)
        return [int(z[r + j, 0]) for j in range(k)]
    Xf = nmod_mat([[int(X[i, j]) % p for j in range(n)] for i in range(n)], p)
    cp = Xf.charpoly(); cs = list(map(int, cp.coeffs())); s0 = next(i for i, x in enumerate(cs) if x)
    g = nmod_poly(cs[s0:], p); xp = nmod_poly([0] * s0 + [1], p); gcd, a, b = xp.xgcd(g)
    eco = list(map(int, (a * xp).coeffs()))
    def P0(v):
        out = nmod_mat([[0] for _ in range(n)], q)
        for c in reversed(eco): out = X * out + c * v
        return out
    def seed(vec):
        v = nmod_mat([[x % q] for x in vec], q)
        z1 = P0(v); z2 = P0(z1); z3 = P0(z2); z = v - (3 * z2 - 2 * z3); uz = U * z
        if any(int(uz[i, 0]) % p for i in range(n)): return 'not-in-V'
        return project(nmod_mat([[int(uz[i, 0]) // p] for i in range(n)], q))
    L1 = [int(Dm[i, 0]) for i in range(n)]
    # G = U(Delta^delta) / E^((p+1)/2), weight 0
    qq = K.pw(K.eta, p * p); el2 = [0] * K.L
    for j in range(0, K.L, p * p): el2[j] = int(K.eta[j // (p * p)])
    ratio = K.mul(qq, K.inv(K.P(el2)))
    DD = K.mul(K.Phi, ratio)
    G = K.mul(K.U(DD), K.pw(K.Einv, (p + 1) // 2), K.LQ)
    Gv = K.decompose(G)
    sL = seed(L1); sG = seed(Gv)
    diff = [(int(a) - int(b)) % q for a, b in zip(L1, Gv)]
    return dict(p=p, s=k, seed_L1=sL, seed_G=sG, seed_diff=seed(diff))

if __name__ == '__main__':
    for p in map(int, sys.argv[1:]):
        print(seeds(p), flush=True)
