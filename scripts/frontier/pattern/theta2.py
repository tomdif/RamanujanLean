# Second-order operator Theta on Kbar = ker(Dbar | S_{l-1}) (even side), and the starting vector u0.
#   Theta(u) = pi_K( [ U( D(u~)/l ) ] mod l , block 1 ),  pi_K = projection S = U(V) + K along Ubar(V), V = Im Dbar.
#   u0 = pi_K? -- no: u0 = (U z / l) mod l where z = e_Z L(1); computed here as
#        u_k := block-1 reduction of U X^k z / l^{k+1}, with z = L(1) - e_Y L(1), e_Y = lim X^{n!} (Katz model).
# Prints rank Theta, charpoly, and whether Theta^k u0 != 0 for k < dim K + 2.
import sys, sympy
from katzmat import Katz
from flint import nmod_mat

def run(p, PR=4, N=7):
    K = Katz(p, PR, N); Um, Dm = K.matrices(); mod = K.mod
    U = [[int(x) for x in r] for r in Um.tolist()]; D = [[int(x) for x in r] for r in Dm.tolist()]
    n = K.dN; I1 = list(range(K.dims[0], K.dims[1])); d = len(I1)
    mv = lambda M, v: [sum(M[i][k] * v[k] for k in range(n)) % mod for i in range(n)]
    sub = lambda M: [[M[i][j] % p for j in I1] for i in I1]
    U11, D11 = nmod_mat(sub(U), p), nmod_mat(sub(D), p)
    # kernel of D11 and image V of D11
    def nullspace(M):
        X, nul = M.nullspace(); cols = [[int(X[i, j]) for i in range(M.ncols())] for j in range(nul)]
        return cols
    Kb = nullspace(D11)
    # basis of Ubar(V): columns of U11*D11, independent
    UV = U11 * D11
    cols = [[int(UV[i, j]) for i in range(d)] for j in range(d)]
    # pick independent columns
    basisUV = []
    for c in cols:
        T = basisUV + [c]
        if nmod_mat(len(T), d, [x for r in T for x in r], p).rank() == len(T): basisUV = T
    Bfull = basisUV + Kb  # basis of S (should be d vectors)
    Bm = nmod_mat(d, d, [Bfull[j][i] for i in range(d) for j in range(d)], p)
    ok = (Bm.rank() == d)
    Binv = Bm.inv() if ok else None
    def projK(s):  # coordinates in K basis
        c = Binv * nmod_mat(d, 1, s, p)
        return [int(c[len(basisUV) + i, 0]) for i in range(len(Kb))]
    def lift(svec):
        v = [0] * n
        for a, i in enumerate(I1): v[i] = svec[a]
        return v
    def theta(kvec):
        s = [sum(kvec[i] * Kb[i][a] for i in range(len(Kb))) % p for a in range(d)]
        w = mv(D, lift(s))
        assert all(x % p == 0 for x in w), 'D u~ not divisible by l'
        w = [x // p for x in w]
        u = mv(U, w)
        return projK([u[i] % p for i in I1])
    k = len(Kb)
    Th = [theta([1 if i == j else 0 for i in range(k)]) for j in range(k)]
    Thm = nmod_mat(k, k, [Th[j][i] for i in range(k) for j in range(k)], p) if k else None
    # u_k from L(1): z = L(1) - e_Y L(1).  e_Y via X^{M}, M = big multiple of group exponents
    X = [[sum(D[i][t] * U[t][j] for t in range(n)) % mod for j in range(n)] for i in range(n)]
    Xm = nmod_mat(X, mod) if False else nmod_mat(n, n, [x for r in X for x in r], mod)
    L1 = mv(D, [1] + [0] * (n - 1))
    # X^{e} with e = (p^f - 1) * p^PR * lcm-ish : use e = prod_{f<=d} (p^f-1) * p^(PR+2)
    e = p ** (PR + 2)
    for f in range(1, d + 1): e *= (p ** f - 1)
    P = nmod_mat(n, n, [1 if i == j else 0 for i in range(n) for j in range(n)], mod); B = Xm; ee = e
    while ee:
        if ee & 1: P = P * B
        B = B * B; ee >>= 1
    y = P * nmod_mat(n, 1, L1, mod)
    z = [(L1[i] - int(y[i, 0])) % mod for i in range(n)]
    out = []
    zk = z
    for kk in range(PR - 1):
        uk = mv(U, zk)
        if not all(x % p ** (kk + 1) == 0 for x in uk): out.append(('notdiv', kk)); break
        red = [(uk[i] // p ** (kk + 1)) % p for i in I1]
        out.append(projK(red) if ok else red)
        zk = mv(X, zk)
    return dict(p=p, d=d, dimK=k, basis_ok=ok, rankTheta=Thm.rank() if k else 0,
                charpolyTheta=str(Thm.charpoly().factor()) if k else '', u=out)

if __name__ == '__main__':
    for p in sympy.primerange(int(sys.argv[1]), int(sys.argv[2]) + 1):
        o = run(p, int(sys.argv[3]) if len(sys.argv) > 3 else 4, int(sys.argv[4]) if len(sys.argv) > 4 else 7)
        print(o, flush=True)
