# Mod-l key operator Xi = Xbar|V_odd in half-integral-weight coordinates.
#   j = l mod 24, t = (l-j)/24, rho = (j l - 1)/24, k' = (l+j-2)/2, delta = (l^2-1)/24.
#   V_odd = Delta^t S_{k'}  (mod l),  Xi(G) = U_{l^2}(Delta^{j delta} G) = eta^j U_{l^2}(G/eta^j)  = T_{l^2} on
#   S_{(l-2)/2}(SL2Z, nu_eta^{-l}).
#   Coordinates: W(G) = coefficients n=1..r of G*P_j, P_j = prod(1-q^n)^{-j}.
#   W(Xi G)_n = coeff_{l^2 n - j delta}(G*P_j).   W(Lbar(1)/Delta^t)_n = p(l n - rho) mod l.
# Output: r, R=floor((l+12)/24), det, charpoly factorization, Krylov rank of Lbar(1) (= mod-l stable rank).
import sys, sympy
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

def analyze(l, verbose=False):
    p = l; j = l % 24; t = (l - j) // 24; rho = (j * l - 1) // 24; kp = (l + j - 2) // 2
    delta = (l * l - 1) // 24; r = dimS(kp); R = (l + 12) // 24
    L = l * l * r - j * delta + 1
    tr = lambda f: nmod_poly(f.coeffs()[:L], p)
    eta = pent(L, p)                      # prod(1-q^n)
    P1 = inv(eta, L, p)
    Pj = nmod_poly([1], p)
    for _ in range(j): Pj = tr(P1 * Pj)
    e24 = nmod_poly([1], p); b = eta; n = 24
    while n:
        if n & 1: e24 = tr(e24 * b)
        b = tr(b * b); n >>= 1
    Delta = tr(nmod_poly([0, 1], p) * e24)
    E4 = eis(4, L, p); E6 = eis(6, L, p)
    # basis G_i = Delta^i E4^a E6^b, weight kp, i = 1..r ; multiply by Pj right away
    cols_W = []; cols_A = []
    DPj = Pj  # Delta^0 * Pj
    for i in range(1, r + 1):
        DPj = tr(Delta * DPj)
        w = kp - 12 * i
        for b in range(3):
            if w - 6 * b >= 0 and (w - 6 * b) % 4 == 0: a = (w - 6 * b) // 4; break
        F = DPj
        for _ in range(a): F = tr(E4 * F)
        for _ in range(b): F = tr(E6 * F)
        c = F.coeffs(); c += [0] * (L - len(c))
        cols_W.append([int(c[n]) for n in range(1, r + 1)])
        cols_A.append([int(c[l * l * n - j * delta]) for n in range(1, r + 1)])
        if verbose: print('basis', i, '/', r, flush=True)
    Bm = nmod_mat(r, r, [cols_W[jj][ii] for ii in range(r) for jj in range(r)], p)
    Am = nmod_mat(r, r, [cols_A[jj][ii] for ii in range(r) for jj in range(r)], p)
    M = Am * Bm.inv()
    # partition numbers mod l up to l r
    LP = l * r + 1
    pp = eta.coeffs()[:LP]
    pv = inv(nmod_poly(pp, p), LP, p).coeffs(); pv += [0] * (LP - len(pv))
    v = [int(pv[l * n - rho]) for n in range(1, r + 1)]
    # Krylov rank
    vec = nmod_mat(r, 1, v, p); K = []
    cur = vec
    for _ in range(r + 1):
        K.append([int(cur[i, 0]) for i in range(r)]); cur = M * cur
    Km = nmod_mat(r + 1, r, [x for row in K for x in row], p)
    cp = M.charpoly(); fa = cp.factor()[1]
    geo = []
    for f, e in fa:
        if e > 1:
            cs = [int(c) for c in f.coeffs()]
            A = nmod_mat(r, r, [0] * (r * r), p); P = nmod_mat(r, r, [1 if a == b else 0 for a in range(r) for b in range(r)], p)
            for c in cs:
                A = A + P * c; P = P * M
            geo.append((str(f), e, r - A.rank()))
    print('repeated factors (factor, alg mult, dim ker f(M)):', geo, flush=True)
    return dict(l=l, d=dimS(l - 1), r=r, R=R, det=int(M.det()), rank=M.rank(), krylov=Km.rank(),
                factors=[(str(f), e) for f, e in fa], M=M, v=v)

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for l in sympy.primerange(lo, hi + 1):
        o = analyze(l)
        sqf = all(e == 1 for _, e in o['factors'])
        print(f"l={l} d={o['d']} r={o['r']} R={o['R']} rankXi={o['rank']} det!=0:{o['det']!=0} "
              f"squarefree:{sqf} krylov(L1)={o['krylov']} charpoly={' * '.join(f'({f})^{e}' if e>1 else f'({f})' for f,e in o['factors'])}",
              flush=True)
