"""Finite certificate that W = {f in M_{2lam}(Gamma0(6)) : U2 f = e2 f, U3 f = e3 f} has
f(1) = 0 => f = 0, on the repo's eta basis evenSeries lam i = A^(lam-i/2-i%2) B^(i%2) C^(i/2).
Finds the smallest precision M and an integer left inverse K of the relation matrix L (K L = d I)."""
import sys
from fractions import Fraction
from sympy import Matrix, legendre_symbol, ilcm

def euler(d, M):  # prod (1 - q^{dn}) to degree M
    s = [0]*(M+1); s[0] = 1
    n = 1
    while d*n <= M:
        k = d*n
        for i in range(M, k-1, -1):
            s[i] -= s[i-k]
        n += 1
    return s
def mul(a, b, M):
    c = [0]*(M+1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j in range(0, M+1-i):
            c[i+j] += x*b[j]
    return c
def pw(a, k, M):
    r = [1]+[0]*M
    for _ in range(k): r = mul(r, a, M)
    return r
def inv(a, M):  # a[0] = 1
    r = [0]*(M+1); r[0] = 1
    for n in range(1, M+1):
        r[n] = -sum(a[i]*r[n-i] for i in range(1, n+1))
    return r
NUM = {0: (0, 2, 12, 3, 2), 1: (1, 2, 4, 6, 4), 2: (2, 1, 2, 6, 12)}
DEN = {0: (1, 6, 6, 4), 1: (1, 2, 3, 2), 2: (2, 4, 3, 6)}
def eta(s, d, k, e, r, M):
    x = mul(pw(euler(d, M), k, M), pw(euler(e, M), r, M), M)
    return ([0]*s + x)[:M+1]
def w2(a, M):
    n = eta(*NUM[a], M); d = eta(0, *DEN[a], M)
    return mul(n, inv(d, M), M)
CHK = {0: [1, 6, 15, 24, 33, 36, 33, 48, 69, 78, 90, 72, 51, 84, 120, 144, 141, 108, 87],
       1: [0, 1, 2, 1, 4, 6, 2, 8, 8, 1, 12, 12, 4, 14, 16, 6, 16, 18, 2],
       2: [0, 0, 1, -2, 3, 0, -1, 0, 7, -8, 6, 0, 1, 0, 8, -12, 15, 0, -7]}
for a in range(3): assert w2(a, 18) == CHK[a], a

def basis(lam, M):
    A, B, C = w2(0, M), w2(1, M), w2(2, M)
    out = []
    for i in range(2*lam+1):
        out.append(mul(mul(pw(A, lam - i//2 - i % 2, M), pw(B, i % 2, M), M), pw(C, i//2, M), M))
    return out

def rows(ell, M):
    lam = (ell-3)//2
    e2 = legendre_symbol(2, ell) * 2**((ell-5)//2)
    e3 = legendre_symbol(3, ell) * 3**((ell-5)//2)
    E = basis(lam, M)
    R = [[E[i][1] for i in range(2*lam+1)]]
    lab = [('c1', 1)]
    for m in range(0, M//2+1):
        R.append([E[i][2*m] - e2*E[i][m] for i in range(2*lam+1)]); lab.append(('u2', m))
    for m in range(0, M//3+1):
        R.append([E[i][3*m] - e3*E[i][m] for i in range(2*lam+1)]); lab.append(('u3', m))
    return R, lab, E

if __name__ == '__main__':
    for ell in [13, 17, 19, 23]:
        lam = (ell-3)//2
        for M in range(2*lam, 200):
            R, lab, E = rows(ell, M)
            L = Matrix(R)
            if L.rank() == 2*lam+1:
                break
        print(ell, 'lam', lam, 'M', M, 'rows', len(R))

def certificate(ell, M=28):
    """Greedy square subsystem L0 (n x n) of the relation rows and K = d * L0^{-1} (integer)."""
    lam = (ell-3)//2; n = 2*lam+1
    R, lab, E = rows(ell, M)
    chosen = []; cur = Matrix.zeros(0, n)
    for r, row in enumerate(R):
        trial = cur.col_join(Matrix([row]))
        if trial.rank() > cur.rows:
            cur = trial; chosen.append(r)
        if cur.rows == n: break
    assert cur.rows == n
    inv = cur.inv()
    d = ilcm(*[x.q for x in inv])
    K = (inv * d).applyfunc(int)
    assert K * cur == d * Matrix.eye(n)
    return lam, n, [lab[r] for r in chosen], [list(map(int, cur.row(i))) for i in range(n)], \
        [list(map(int, K.row(i))) for i in range(n)], int(d), E
