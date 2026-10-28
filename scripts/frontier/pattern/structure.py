# mod-l structure of U, D, X=DU on the Katz block B_1 = S_{l-1}, and block-valuation table
import sys, sympy
from katzmat import Katz, dimM
from zmod import val
from flint import nmod_mat

def rank_mod(M, p):
    if not M or not M[0]: return 0
    return nmod_mat(len(M), len(M[0]), [x % p for r in M for x in r], p).rank()

def matmul(A, B, mod):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) % mod for j in range(len(B[0]))] for i in range(len(A))]

def analyze(p, PR=4, N=7):
    K = Katz(p, PR, N); Um, Dm = K.matrices(); mod = K.mod
    U = [[int(x) for x in r] for r in Um.tolist()]; D = [[int(x) for x in r] for r in Dm.tolist()]
    d = K.dims[1] - K.dims[0]
    I1 = list(range(K.dims[0], K.dims[1]))
    sub = lambda M: [[M[i][j] for j in I1] for i in I1]
    U11, D11 = sub(U), sub(D)
    X = matmul(D, U, mod); X11 = sub(X)
    out = dict(p=p, d=d, rkU=rank_mod(U11, p), rkD=rank_mod(D11, p), rkX=rank_mod(X11, p))
    pw = X11; rks = []
    for k in range(1, d + 2):
        rks.append(rank_mod(pw, p)); pw = matmul(pw, X11, mod)
    out['rkXpow'] = rks
    cp = nmod_mat(d, d, [x % p for r_ in X11 for x in r_], p).charpoly()
    fa = cp.factor()[1]
    out['charpolyX_mod_l'] = ' * '.join(f'({str(f)})^{k}' if k > 1 else f'({str(f)})' for f, k in fa)
    # block valuation table: min val of block (i,j) of U and D, i,j = Katz indices 1..N
    def blk(M):
        T = []
        for i in range(1, N + 1):
            row = []
            for j in range(1, N + 1):
                row.append(min([val(M[a][b], p, PR) for a in range(K.dims[i - 1], K.dims[i]) for b in range(K.dims[j - 1], K.dims[j])], default=PR))
            T.append(row)
        return T
    out['Ublk'] = blk(U); out['Dblk'] = blk(D)
    return out

if __name__ == '__main__':
    for p in sympy.primerange(int(sys.argv[1]), int(sys.argv[2]) + 1):
        o = analyze(p)
        print(f"l={p} d={o['d']} rank mod l on S_(l-1): U {o['rkU']} D {o['rkD']} X {o['rkX']}  rank X^k: {o['rkXpow']} charpoly(Xbar|S) = {o['charpolyX_mod_l']}", flush=True)
        if len(sys.argv) > 3:
            print(' U blocks', o['Ublk'][:4]); print(' D blocks', o['Dblk'][:4])
