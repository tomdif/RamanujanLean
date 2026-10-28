# Katz-coordinate matrices of U and D (Boylan-Webb operators) at level 1, prime p, precision p^PR,
# Katz indices 0..N.  Coordinates: t in [0, dN), dN = dim M_{N(p-1)}; coordinate t belongs to Katz
# index i(t) (dim M_{(i-1)(p-1)} <= t < dim M_{i(p-1)}), basis element m_t / E^{i(t)}, where m_t is
# the t-th fully reduced Miller basis element of M_{i(t)(p-1)}  (B_i = span of the top Miller elements).
import sys, sympy, pickle, os
from fractions import Fraction
from flint import nmod_poly, nmod_mat, fmpz_mod_poly_ctx

def dimM(k):
    if k < 0 or k % 2 or k == 2: return 0
    return k // 12 + (0 if k % 12 == 2 else 1)

def sigma(n, k):
    s = 0; d = 1
    while d * d <= n:
        if n % d == 0:
            s += d ** k
            if d * d != n: s += (n // d) ** k
        d += 1
    return s

class Katz:
    def __init__(s, p, PR, N, verbose=False):
        s.p, s.PR, s.N = p, PR, N
        mod = p ** PR; s.mod = mod
        k1 = p - 1; s.k1 = k1
        s.dims = [dimM(i * k1) for i in range(N + 1)]
        dN = s.dims[N]; s.dN = dN
        s.idx = []
        for t in range(dN):
            i = next(i for i in range(N + 1) if s.dims[i] > t); s.idx.append(i)
        s.delta = (p * p - 1) // 24
        LQ = dN + 2; s.LQ = LQ
        L = p * LQ + 2; s.L = L
        if mod < 2 ** 63:
            P = lambda lst: nmod_poly(lst, mod)
        else:
            C = fmpz_mod_poly_ctx(mod)
            P = lambda lst: C([int(x) for x in lst])
        s.P = P
        def tr(f, n=L): return P(f.coeffs()[:n])
        s.tr = tr
        def mul(a, b, n=L): return tr(a * b, n)
        s.mul = mul
        def eis(k):
            B = sympy.bernoulli(k); c = Fraction(-2 * k) / Fraction(B.p, B.q); out = [1]
            for n in range(1, L):
                vv = c * sigma(n, k - 1); out.append(vv.numerator * pow(vv.denominator, -1, mod) % mod)
            return P(out)
        # sigma is slow for L ~ 1e4 * k; use a divisor-sum sieve instead
        def eis_fast(k):
            B = sympy.bernoulli(k); c = Fraction(-2 * k) / Fraction(B.p, B.q)
            cn = c.numerator * pow(c.denominator, -1, mod) % mod
            sg = [0] * L
            for d in range(1, L):
                dk = pow(d, k - 1, mod)
                for n in range(d, L, d): sg[n] += dk
            return P([1] + [cn * (sg[n] % mod) % mod for n in range(1, L)])
        E4 = eis_fast(4); E6 = eis_fast(6); E = eis_fast(p - 1)
        s.E = E
        e = [0] * L
        k = 0
        while True:
            done = True
            for kk in (k, -k) if k else (0,):
                x = kk * (3 * kk - 1) // 2
                if x < L: e[x] += (1 if kk % 2 == 0 else -1); done = False
            if done and k > 0: break
            k += 1
        eta = P([x % mod for x in e]); s.eta = eta
        def pw(f, n):
            r = P([1]); b = f
            while n:
                if n & 1: r = mul(r, b)
                b = mul(b, b); n >>= 1
            return r
        s.pw = pw
        def inv(f):
            c0 = int(f[0]); g = P([pow(c0, -1, mod)]); n = 1
            while n < L:
                n = min(2 * n, L)
                fg = tr(f * g, n); g = tr(g * (P([2]) - fg), n)
            return g
        s.inv = inv
        Delta = mul(P([0, 1]), pw(eta, 24))
        # Miller bases for weights i*k1, i=0..N  (fully reduced: m_t = q^t + O(q^{d}))
        D4 = [P([1])]; D6 = [P([1])]; DD = [P([1])]
        maxw = N * k1
        def getpow(lst, base, n):
            while len(lst) <= n: lst.append(mul(lst[-1], base))
            return lst[n]
        s.miller = {}
        for i in range(N + 1):
            kk = i * k1; d = s.dims[i]; base = []
            for a in range(d):
                r = kk - 12 * a
                for c in range(3):
                    if r - 6 * c >= 0 and (r - 6 * c) % 4 == 0: b = (r - 6 * c) // 4; break
                base.append(mul(mul(getpow(DD, Delta, a), getpow(D4, E4, b)), getpow(D6, E6, c)))
            # reduce (upper-triangular, unit leading coeffs)
            for t in range(d - 1, -1, -1):
                for u in range(t):
                    c = int(base[u][t])
                    if c: base[u] = base[u] - base[t] * c
            s.miller[i] = base
            if verbose: print('miller', i, d, flush=True)
        # E * miller((i-1)k1), truncated to LQ, for decomposition
        s.EM = {i: [mul(m, E, LQ) for m in s.miller[i - 1]] for i in range(1, N + 1)}
        s.millerLQ = {i: [tr(m, LQ) for m in s.miller[i]] for i in range(N + 1)}
        Einv = inv(E); s.Einv = Einv
        s.EinvP = [P([1])]
        for i in range(N): s.EinvP.append(mul(s.EinvP[-1], Einv))
        s.EN = tr(pw(E, N), LQ)
        # Phi = q^delta prod(1-q^{p^2 n}) / prod(1-q^n)
        el2 = [0] * L
        for j in range(0, L, p * p): el2[j] = int(eta[j // (p * p)])
        t_ = mul(P(el2), inv(eta))
        s.Phi = P([0] * s.delta + t_.coeffs()[:L - s.delta])
        s.basis = [s.miller[s.idx[t]][t] for t in range(dN)]

    def U(s, f):  # q-series length >= p*LQ -> length LQ
        c = f.coeffs(); p = s.p
        return s.P([int(c[p * n]) if p * n < len(c) else 0 for n in range(s.LQ)])

    def decompose(s, F):
        """F: weight-0 q-series (length>=dN). Returns Katz coordinate vector (length dN) of F,
        computed as Katz decomposition of E^N F (assumed classical of weight N k1)."""
        G = s.tr(F * s.EN, s.LQ); out = [0] * s.dN; mod = s.mod
        for i in range(s.N, 0, -1):
            EM = s.EM[i]; c = []
            R = G
            for t in range(len(EM)):
                ct = int(R[t]) if t < R.length() else 0
                c.append(ct)
                if ct: R = R - EM[t] * ct
            for t in range(s.dims[i - 1], s.dims[i]):
                out[t] = int(R[t]) if t < R.length() else 0
            G = s.P([0])
            for t in range(len(c)):
                if c[t]: G = G + s.millerLQ[i - 1][t] * c[t]
        out[0] = int(G[0]) if G.length() else 0
        return out

    def series(s, vec, n=None):
        """weight-0 q-series of Katz vector, to length n (default L)"""
        n = n or s.L
        f = s.P([0])
        for t, c in enumerate(vec):
            if c % s.mod: f = f + s.tr(s.basis[t] * s.EinvP[s.idx[t]], n) * c
        return s.tr(f, n)

    def matrices_list(s):
        Ucols = []; Dcols = []
        for t in range(s.dN):
            g = s.mul(s.basis[t], s.EinvP[s.idx[t]])
            Ucols.append(s.decompose(s.U(g)))
            Dcols.append(s.decompose(s.U(s.mul(g, s.Phi))))
        n = s.dN
        return [[Ucols[j][i] for j in range(n)] for i in range(n)], [[Dcols[j][i] for j in range(n)] for i in range(n)]

    def matrices(s, verbose=False):
        Ucols = []; Dcols = []
        for t in range(s.dN):
            g = s.mul(s.basis[t], s.EinvP[s.idx[t]])
            Ucols.append(s.decompose(s.U(g)))
            Dcols.append(s.decompose(s.U(s.mul(g, s.Phi))))
            if verbose and t % 20 == 0: print('col', t, '/', s.dN, flush=True)
        Um = nmod_mat(s.dN, s.dN, [Ucols[j][i] for i in range(s.dN) for j in range(s.dN)], s.mod)
        Dm = nmod_mat(s.dN, s.dN, [Dcols[j][i] for i in range(s.dN) for j in range(s.dN)], s.mod)
        return Um, Dm

def get(p, PR, N, cachedir=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache')):
    os.makedirs(cachedir, exist_ok=True)
    fn = os.path.join(cachedir, f'katz_{p}_{PR}_{N}.pkl')
    if os.path.exists(fn):
        d = pickle.load(open(fn, 'rb'))
        return d
    K = Katz(p, PR, N)
    Um, Dm = K.matrices()
    d = dict(p=p, PR=PR, N=N, dN=K.dN, idx=K.idx, dims=K.dims,
             U=[[int(x) for x in row] for row in Um.tolist()],
             D=[[int(x) for x in row] for row in Dm.tolist()])
    pickle.dump(d, open(fn, 'wb'))
    return d

if __name__ == '__main__':
    import time
    p, PR, N = map(int, sys.argv[1:4])
    t0 = time.time(); K = Katz(p, PR, N, verbose=False); t1 = time.time()
    print('setup', t1 - t0, 'dN', K.dN, 'L', K.L)
    Um, Dm = K.matrices(); print('mats', time.time() - t1)
