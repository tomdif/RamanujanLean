# Memory-lean exact mod-l computation of Xbar = Dbar o Ubar on the FULL space Sbar = S_{l-1}(F_l)
# (and Dbar on Mbar = F_l*1 + Sbar), via composition, needing q-expansions only to ~ (d+extra)*l terms
# (about 7*10^4 at l = 859) instead of l^2 R (~2.6*10^7) as in halfint.py.
#
# Soundness (all mod l, on q-expansions):
#   * Ubar(sum a_n q^n) = sum a_{ln} q^n maps Sbar -> Sbar (U == T_l on M_{l-1} mod l).
#   * Dbar(f) = U(Phi f), Phi = eta(l^2 z)/eta(z) = q^delta * prod(1-q^{l^2 n}) * sum p(n) q^n.
#     We only use coefficients of Phi*f below index l^2, where prod(1-q^{l^2 n}) == 1, so
#     coeff_n(Dbar f) = coeff_{l n - delta}( P * f ),  P = sum p(n) q^n.   Dbar(Mbar) in V subset Sbar (Lemma 2).
#   * Basis of Sbar: f_i = Delta^i E4^(a-3i) E6 (k = l-1 == 6 mod 12 for l = 859; general a,b chosen per i),
#     f_i = q^i + O(q^{i+1}), so a form in Sbar is determined by coefficients 1..d (unitriangular solve).
#   * V = Delta^t S_{k'} = span{f_{t+1}, ..., f_d} when the same E4/E6 recipe is used (checked below).
#   Extra coefficients d+1..d+EXTRA are used to verify that Ubar f and Dbar f really lie in Sbar.
import sys, time, sympy
import numpy as np
from flint import nmod_poly, nmod_mat

def dimS(k):
    if k < 12 or k % 2: return 0
    return k // 12 - (1 if k % 12 == 2 else 0)

def eis(k, L, p):
    B = sympy.bernoulli(k); c = sympy.Rational(-2 * k) / B
    cn = int(c.p) * pow(int(c.q), -1, p) % p
    sg = [0] * L
    for d in range(1, L):
        dk = pow(d, k - 1, p)
        for n in range(d, L, d): sg[n] += dk
    return nmod_poly([1] + [cn * (sg[n] % p) % p for n in range(1, L)], p)

def pent(L, p):
    e = [0] * L; k = 0
    while True:
        done = True
        for kk in ((k, -k) if k else (0,)):
            x = kk * (3 * kk - 1) // 2
            if x < L: e[x] += (1 if kk % 2 == 0 else -1); done = False
        if done and k > 0: break
        k += 1
    return nmod_poly([x % p for x in e], p)

def inv(f, L, p):
    g = nmod_poly([pow(int(f[0]), -1, p)], p); n = 1
    while n < L:
        n = min(2 * n, L)
        fg = nmod_poly((f * g).coeffs()[:n], p)
        g = nmod_poly((g * (nmod_poly([2], p) - fg)).coeffs()[:n], p)
    return g

def coeffs(f, L):
    c = [int(x) for x in f.coeffs()[:L]]; return c + [0] * (L - len(c))

def mat(rows, cols, f, p):
    return nmod_mat(rows, cols, [f(i, j) % p for i in range(rows) for j in range(cols)], p)

def analyze(l, EXTRA=12):
    p = l; T0 = time.time()
    j = l % 24; t = (l - j) // 24; rho = (j * l - 1) // 24; kp = (l + j - 2) // 2
    delta = (l * l - 1) // 24; d = dimS(l - 1); R = (l + 12) // 24; r = dimS(kp)
    k = l - 1; NC = d + EXTRA                      # number of q-coefficients of images we read
    L = l * NC + 1                                 # q-expansion length needed
    assert L < l * l, 'need L < l^2 so that eta(l^2 z) == 1 in range'
    print(f'l={l} j={j} t={t} rho={rho} kp={kp} delta={delta} d={d} R={R} r={r} L={L}', flush=True)
    tr = lambda f: nmod_poly(f.coeffs()[:L], p)
    eta = pent(L, p); P = inv(eta, L, p)
    e24 = nmod_poly([1], p); b = eta; n = 24
    while n:
        if n & 1: e24 = tr(e24 * b)
        b = tr(b * b); n >>= 1
    Delta = tr(nmod_poly([0, 1], p) * e24)
    E4 = eis(4, L, p); E6 = eis(6, L, p)
    print(f'  series done {time.time()-T0:.1f}s', flush=True)
    # basis f_i = Delta^i E4^a_i E6^b_i of S_k, i = 1..d  (b_i in {0,1,2} minimal)
    def ab(w):
        for bb in range(3):
            if w - 6 * bb >= 0 and (w - 6 * bb) % 4 == 0: return (w - 6 * bb) // 4, bb
        raise ValueError
    recipe = [ab(k - 12 * i) for i in range(1, d + 1)]
    E4pows = {0: nmod_poly([1], p)}
    need = sorted(set(a for a, _ in recipe))
    cur = nmod_poly([1], p); ca = 0
    for a in need:
        while ca < a: cur = tr(cur * E4); ca += 1
        E4pows[a] = cur
    E6pows = [nmod_poly([1], p), E6, tr(E6 * E6)]
    F = []; Dp = nmod_poly([1], p)
    for i in range(1, d + 1):
        Dp = tr(Dp * Delta); a, bb = recipe[i - 1]
        F.append(coeffs(tr(tr(Dp * E4pows[a]) * E6pows[bb]), L))
    print(f'  basis done {time.time()-T0:.1f}s', flush=True)
    # V-recipe check: Delta^t * (basis of S_{k'} with same recipe) = f_{t+1..d}
    recipe_kp = [ab(kp - 12 * i) for i in range(1, r + 1)]
    V_is_tail = (r == d - t) and all(recipe_kp[i - 1] == recipe[t + i - 1] for i in range(1, r + 1))
    # triangular coordinate map on first d coeffs (unitriangular B[n][i] = coeff_n(f_i))
    B = mat(d, d, lambda n, i: F[i][n + 1], p); Binv = B.inv()
    def coords_and_check(cols):  # cols: list of length-NC coefficient vectors (n=1..NC)
        C = mat(d, len(cols), lambda n, c: cols[c][n], p)
        X = Binv * C
        Bx = mat(NC, d, lambda n, i: F[i][n + 1], p) * X   # re-expand to NC coeffs
        ok = all(int(Bx[n, c]) == cols[c][n] % p for n in range(NC) for c in range(len(cols)))
        return X, ok
    # Ubar on Sbar
    Ucols = [[F[i][l * n] for n in range(1, NC + 1)] for i in range(d)]
    Um, okU = coords_and_check(Ucols)
    # Dbar on Mbar: basis [1, f_1..f_d];  coeff_n(Dbar f) = coeff_{l n - delta}(P f)
    Pc = coeffs(P, L); Pn = np.array(Pc, dtype=np.int64)
    def Dcol(fc):
        fn = np.array(fc, dtype=np.int64); out = []
        for n in range(1, NC + 1):
            m = l * n - delta
            out.append(0 if m < 0 else int(np.dot(fn[:m + 1], Pn[m::-1]) % p))
        return out
    Dcols = [[(Pc[l * n - delta] if l * n - delta >= 0 else 0) for n in range(1, NC + 1)]]  # Dbar(1) = Lbar(1)
    for i in range(d):
        Dcols.append(Dcol(F[i]))
    print(f'  D columns done {time.time()-T0:.1f}s', flush=True)
    Dm, okD = coords_and_check(Dcols)          # d x (d+1), column 0 = Dbar(1)
    lowzero = all(Dcols[c][n] % p == 0 for c in range(d + 1) for n in range(t))  # ord >= t+1
    DS = mat(d, d, lambda a, b_: int(Dm[a, b_ + 1]), p)  # Dbar on Sbar
    X = DS * Um
    rkX = X.rank(); rkD_S = DS.rank(); rkD_M = Dm.rank(); rkU = Um.rank()
    # X(V) in V and Xi = X|V on V = span f_{t+1..d}
    XV_in_V = all(int(X[a, c]) == 0 for a in range(t) for c in range(t, d))
    XS_in_V = all(int(X[a, c]) == 0 for a in range(t) for c in range(d))
    Xi = mat(d - t, d - t, lambda a, c: int(X[t + a, t + c]), p)
    detXi = int(Xi.det()); rkXi = Xi.rank()
    # powers of X
    pw = X; rks = []
    for _ in range(d + 1): rks.append(pw.rank()); pw = pw * X
    Xd = X
    for _ in range(d - 1): Xd = Xd * X
    rkXd = Xd.rank()
    aug = nmod_mat(d, 2 * d + 1, [int(Xd[a, c]) if c < d else int(Dm[a, c - d]) for a in range(d) for c in range(2 * d + 1)], p)
    rk_aug = aug.rank()
    d_l_zero = (rk_aug == rkXd)
    # Krylov rank of Lbar(1) = Dbar(1) under X (lives in V)
    v = nmod_mat(d, 1, [int(Dm[a, 0]) for a in range(d)], p)
    K = []; cur = v
    for _ in range(d + 1): K.append([int(cur[a, 0]) for a in range(d)]); cur = X * cur
    kry = nmod_mat(len(K), d, [x for row in K for x in row], p).rank()
    cpX = X.charpoly(); cpXi = Xi.charpoly()
    faXi = cpXi.factor()[1]
    geo = []
    I = mat(d - t, d - t, lambda a, c: 1 if a == c else 0, p)
    for f, e in faXi:
        if e > 1:
            A = mat(d - t, d - t, lambda a, c: 0, p); Pw = I
            for cc in [int(c) for c in f.coeffs()]: A = A + Pw * cc; Pw = Pw * Xi
            geo.append((str(f), e, (d - t) - A.rank()))
    # x-adic valuation of charpoly(X|Sbar)
    cX = [int(c) for c in cpX.coeffs()]; val0 = next(i for i, c in enumerate(cX) if c)
    res = dict(l=l, d=d, R=R, r=r, t=t, L=L, V_is_tail=V_is_tail, okU=okU, okD=okD, lowzero=lowzero,
               XV_in_V=XV_in_V, XS_in_V=XS_in_V, rkU=rkU, rkD_S=rkD_S, rkD_M=rkD_M, rkX=rkX,
               rkXi=rkXi, detXi_nonzero=detXi != 0, detXi=detXi, rkXpow=rks, rkXd=rkXd, rk_aug=rk_aug,
               d_l_zero=d_l_zero, krylov=kry, val0_charpolyX=val0, repeated=geo,
               charpolyXi=' * '.join(f'({f})^{e}' if e > 1 else f'({f})' for f, e in faXi),
               secs=round(time.time() - T0, 1))
    return res

if __name__ == '__main__':
    for l in [int(a) for a in sys.argv[1:]]:
        o = analyze(l)
        for kk, vv in o.items(): print(f'  {kk}: {vv}', flush=True)
        print(flush=True)
