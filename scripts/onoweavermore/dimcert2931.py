#!/usr/bin/env python3
"""Dimension-one certificate for W = {b in M_{2lam}(Gamma0(6)) : U2 b = e2 b, U3 b = e3 b} at
ell = 29, 31 (weights 26, 28), on the repo's basis evenSeries lam i, with basis coefficients
through q^P. Greedy square row system L0 (rank via mod-p elimination), K = d * L0^{-1} exactly."""
import sys
from fractions import Fraction
from math import lcm
sys.path.insert(0, __file__.rsplit('/', 1)[0] + '/../atkinsporadic')
from dimone_cert import basis
from sympy import legendre_symbol

PR = (1 << 61) - 1
def rank_mod(rows):
    M = [[x % PR for x in r] for r in rows]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; inv = pow(M[rk][c], PR - 2, PR)
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c] * inv % PR
                M[i] = [(a - f * b) % PR for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def inverse(A):
    n = len(A); M = [[Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]; p = M[c][c]; M[c] = [x / p for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return [r[n:] for r in M]

def certificate(ell, P):
    lam = (ell - 3) // 2; n = 2 * lam + 1
    e2 = legendre_symbol(2, ell) * 2 ** ((ell - 5) // 2)
    e3 = legendre_symbol(3, ell) * 3 ** ((ell - 5) // 2)
    E = basis(lam, P)
    cand = [((0, 1), [E[i][1] for i in range(n)])]
    for m in range(0, P // 2 + 1): cand.append(((1, m), [E[i][2 * m] - e2 * E[i][m] for i in range(n)]))
    for m in range(0, P // 3 + 1): cand.append(((2, m), [E[i][3 * m] - e3 * E[i][m] for i in range(n)]))
    chosen = []
    for lab, row in cand:
        if rank_mod([r for _, r in chosen] + [row]) > len(chosen): chosen.append((lab, row))
        if len(chosen) == n: break
    if len(chosen) < n: return None
    L0 = [r for _, r in chosen]; inv = inverse(L0)
    d = lcm(*[x.denominator for r in inv for x in r])
    K = [[int(x * d) for x in r] for r in inv]
    for i in range(n):
        for j in range(n):
            assert sum(K[i][r] * L0[r][j] for r in range(n)) == (d if i == j else 0)
    return dict(lam=lam, n=n, e2=e2, e3=e3, rows=[l for l, _ in chosen], K=K, d=d, E=[e[:P + 1] for e in E])

if __name__ == '__main__':
    for ell in [29, 31]:
        for P in range(28, 120, 2):
            c = certificate(ell, P)
            if c: print(ell, 'P', P, 'd', c['d'], 'rows', c['rows'], 'maxdig', max(len(str(abs(x))) for r in c['K'] for x in r)); break
