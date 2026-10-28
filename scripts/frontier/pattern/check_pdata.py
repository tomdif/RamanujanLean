# validate Katz-matrix iteration against direct partition data
import sys, os, numpy as np
from katzmat import Katz
from flint import nmod_mat
p, PR, N, pfile, pm = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
pdat = np.fromfile(pfile, dtype=np.uint64); NMAX = len(pdat) - 1
K = Katz(p, PR, N)
# eta sanity
import sympy
Um, Dm = K.matrices()
mod = p ** pm
def Eser(L, step=1):
    E = [0] * L
    for k in range(-3000, 3001):
        e = step * (k * (3 * k - 1) // 2)
        if 0 <= e < L: E[e] += (1 if k % 2 == 0 else -1)
    return E
def Lform(b, L):
    r = (-pow(p, -b, 24)) % 24
    shift = p if b % 2 == 1 else 1
    off = (r + shift) // 24
    S = [0] * L; ok = 0
    for k in range(L):
        n = 24 * k + r; m = (p ** b * n + 1) // 24; e = k + off
        if e < L:
            if m > NMAX: break
            S[e] = int(pdat[m]) % mod; ok = e + 1
    E = Eser(L, shift)
    c = [0] * L
    for i, x in enumerate(S):
        if x:
            for j in range(L - i): c[i + j] = (c[i + j] + x * E[j]) % mod
    return c[:ok]
v = nmod_mat(K.dN, 1, [1] + [0] * (K.dN - 1), K.mod)
for b in range(1, 7):
    v = (Dm if b % 2 else Um) * v
    vec = [int(v[i, 0]) for i in range(K.dN)]
    f = K.series(vec, 400)
    direct = Lform(b, 400)
    n = len(direct)
    if n == 0: print(b, 'no data'); continue
    mism = [i for i in range(n) if (int(f[i]) - direct[i]) % mod]
    vals = []
    print(f'b={b}: compared {n} coeffs mod {p}^{pm}: mismatches {len(mism)}', mism[:5], flush=True)
