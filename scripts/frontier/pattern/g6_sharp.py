# Gap closure for BL_SHARPNESS_PROOF.md (G6 + all-m sharpness), 2026-10-28.
#
# For a prime l and Katz model (precision l^PR, Katz indices 0..N):
#  (1) env_exponent: the certified agreement exponent e(l,N) of section "Gap closure" (T2): the model's L(b)
#      equal the true Katz coordinates of L(b) mod l^min(PR,e) for EVERY b, and the true coordinates of index
#      > N vanish mod l^e.  Uses only the column bounds (UB), (DB) and the envelopes alpha, beta.
#      theta_ok: the analogous margins for the operator Theta (needs >= 2, >= 1, >= 1).
#  (2) checks that the computed U, D block valuations respect (UB)/(DB) (sanity check of the model).
#  (3) Omega(m) = stable odd module mod l^m, as Z/l^m-module: Smith invariants (list of m - a_i),
#      mu(m) = minimal number of generators, phi(m) = number of free (Z/l^m) summands.
#  (4) b_l(m) (combined chain, = min(2k_o+1, 2k_e+2)) for m <= min(PR, e).
#  (5) Theta on Kbar = ker Dbar and u0bar (definition of section 4.2), rank / charpoly of Theta.
import sys, time, sympy
from katzmat import Katz
from zmod import smith
from flint import nmod_mat, fmpz_mat

def cdiv(a, b): return -((-a) // b)

def bounds(p):
    s = (p + 1) // 2
    al = lambda i: cdiv(p * i - 2, p + 1)
    be = lambda i: cdiv(p * i - 2 - s, p + 1)
    u = lambda i, j: cdiv(p * i - j, p + 1) - 1
    d = lambda i, j: cdiv(p * i - j - s, p + 1) - 1
    return s, al, be, u, d

def env_exponent(p, N):
    """returns dict with (E1,E2,E3) for the D-step and U-step, and the overall e = min of all."""
    s, al, be, u, d = bounds(p)
    g = lambda gam, j: (max(0, gam(j) - 1) if j >= 1 else 0)
    out = {}
    for name, gin, gout, t, j0 in (('D', al, be, d, 0), ('U', be, al, u, 1)):
        E1 = min(g(gin, j) + t(N + 1, j) for j in range(j0, N + 1))
        E2 = 10 ** 9; j = N + 1
        while True:
            E2 = min(E2, g(gin, j) + t(1, j))
            # for j' > j: g + t(1,j') >= ((p-1) j' + p - 2 - s)/(p+1) - 2 >= ceil((p-1)(j+1)/(p+1)) - 2
            if cdiv((p - 1) * (j + 1), p + 1) - 2 >= E2: break
            j += 1
        E3 = gout(N + 1) - 1
        out[name] = (E1, E2, E3)
    out['e'] = min(min(v) for k, v in out.items() if k in ('D', 'U'))
    # Theta margins: w = D(u~)/l, u~ in block 1 (integral).  Need
    #  (a) d(N+1,1) >= 2 (model w correct mod l at indices <= N; true w at indices > N is integral),
    #  (b) u(N+1,j) >= 1 for 1 <= j <= N (U-column errors vanish mod l),
    #  (c) for j > N: (d(j,1) - 1) + u(1,j) >= 1 (tail of w does not reach block 1 mod l).
    a_ = d(N + 1, 1); b_ = min(u(N + 1, j) for j in range(1, N + 1))
    c_ = 10 ** 9; j = N + 1
    while True:
        c_ = min(c_, d(j, 1) - 1 + u(1, j))
        if cdiv((p - 1) * (j + 1), p + 1) - 4 >= c_: break   # crude: d(j,1)-1+u(1,j) >= ((p-1)j - s - 1)/(p+1) - 3
        j += 1
    out['theta_margins'] = (a_, b_, c_)
    out['theta_ok'] = a_ >= 2 and b_ >= 1 and c_ >= 1
    return out

def val(x, p, cap):
    if x == 0: return cap
    c = 0
    while x % p == 0 and c < cap: x //= p; c += 1
    return c

def check_column_bounds(K, U, D):
    """min over in-model blocks (i,j) of [computed valuation - bound]; must be >= 0 (or the block is
    zero mod l^PR).  Bounds: (UB) u(i,j), (DB) d(i,j); entries are only known mod l^PR."""
    p, PR, N = K.p, K.PR, K.N
    s, al, be, u, d = bounds(p)
    worst = {}
    for name, M, t in (('U', U, u), ('D', D, d)):
        w = 10 ** 9
        for i in range(1, N + 1):
            for j in range(0, N + 1):
                lo_i, hi_i = K.dims[i - 1], K.dims[i]
                lo_j, hi_j = (0, 1) if j == 0 else (K.dims[j - 1], K.dims[j])
                v = min(val(M[a][b], p, PR) for a in range(lo_i, hi_i) for b in range(lo_j, hi_j))
                bd = t(i, j)
                if v < PR: w = min(w, v - max(bd, 0))
        worst[name] = w
    return worst

def matvec(M, v, mod):
    return [sum(a * b for a, b in zip(row, v)) % mod for row in M]

def stable_span(vs, start, step, p, m, maxlen):
    """sizes of span{vs[start], vs[start+step], ...} with exact Krylov stopping; returns (size, invariants)"""
    cols = []; last = -1
    j = start
    while j < len(vs) and len(cols) <= maxlen:
        cols.append(vs[j]); inv = smith(cols, p, m); sz = sum(m - e for e in inv)
        if sz == last: return sz, inv
        last = sz; j += step
    return None, None

def analyze(p, PR, N, do_theta=True, verbose=True):
    t0 = time.time()
    env = env_exponent(p, N)
    K = Katz(p, PR, N); Um, Dm = K.matrices(); mod = K.mod
    U = [[int(x) for x in r] for r in Um.tolist()]; D = [[int(x) for x in r] for r in Dm.tolist()]
    n = K.dN; d = K.dims[1] - K.dims[0]; R = (p + 12) // 24
    res = dict(p=p, PR=PR, N=N, dN=n, d=d, R=R, env=env, setup_s=round(time.time() - t0, 1))
    res['colbound_slack'] = check_column_bounds(K, U, D)
    e = min(PR, env['e'])
    res['certified_precision'] = e
    # chain L(b), b = 0..B
    B = 2 * (R + e + 3) + 4
    vs = [[1] + [0] * (n - 1)]
    for b in range(1, B + 1):
        vs.append(matvec(D if b % 2 else U, vs[-1], mod))
    # Omega(m) and b(m)
    om = {}; bm = {}
    for m in range(1, e + 1):
        # stable odd module: start at b = 2(m-1)+1 (section 4.1: v(X^k z) >= k+1), Krylov-exact stopping
        sz, inv = stable_span(vs, 2 * (m - 1) + 1, 2, p, m, R + 2)
        invs = sorted([m - x for x in inv], reverse=True) if inv is not None else None
        mu = len(invs) if invs is not None else None
        phi = sum(1 for x in invs if x == m) if invs is not None else None
        om[m] = dict(invariants=invs, mu=mu, phi=phi, log_size=sz)
        # b(m): least b with s(b) == s(b+2)
        s_ = {}
        for b in range(1, min(B, 2 * m + 4) + 1):
            s_[b] = stable_span(vs, b, 2, p, m, R + 2)[0]
        bm[m] = next((b for b in range(1, len(s_) - 1) if s_.get(b) is not None and s_.get(b) == s_.get(b + 2)), None)
    res['Omega'] = om; res['b'] = bm
    if do_theta:
        I1 = list(range(K.dims[0], K.dims[1]))
        U11 = nmod_mat(d, d, [U[i][j] % p for i in I1 for j in I1], p)
        D11 = nmod_mat(d, d, [D[i][j] % p for i in I1 for j in I1], p)
        Xn, nul = D11.nullspace()
        Kb = [[int(Xn[i, j]) for i in range(d)] for j in range(nul)]
        UV = U11 * D11
        basisUV = []
        for jcol in range(d):
            c = [int(UV[i, jcol]) for i in range(d)]
            T = basisUV + [c]
            if nmod_mat(len(T), d, [x for r in T for x in r], p).rank() == len(T): basisUV = T
        Bfull = basisUV + Kb
        Bm = nmod_mat(d, d, [Bfull[j][i] for i in range(d) for j in range(d)], p)
        ok = Bm.rank() == d and len(basisUV) == R
        res['splitting_ok'] = ok; res['dimK'] = len(Kb)
        if ok:
            Binv = Bm.inv()
            def projK(svec):
                c = Binv * nmod_mat(d, 1, [x % p for x in svec], p)
                return [int(c[len(basisUV) + i, 0]) for i in range(len(Kb))]
            def theta(kvec):
                svec = [sum(kvec[i] * Kb[i][a] for i in range(len(Kb))) % p for a in range(d)]
                v = [0] * n
                for a, i in enumerate(I1): v[i] = svec[a]
                w = matvec(D, v, mod)
                assert all(x % p == 0 for x in w)
                w = [x // p for x in w]
                uu = matvec(U, w, mod)
                return projK([uu[i] for i in I1])
            k = len(Kb)
            cols = [theta([1 if i == j else 0 for i in range(k)]) for j in range(k)]
            Th = nmod_mat(k, k, [cols[j][i] for i in range(k) for j in range(k)], p)
            res['rankTheta'] = Th.rank()
            res['charpolyTheta'] = str(Th.charpoly().factor())
            # u0bar certificate via b(2) = 3  <=>  u0bar != 0   (section "Gap closure", T3)
            res['u0_nonzero_via_b2'] = (bm.get(2) == 3) if 2 in bm else None
    res['total_s'] = round(time.time() - t0, 1)
    if verbose: print(res, flush=True)
    return res

if __name__ == '__main__':
    PR = int(sys.argv[3]); N = int(sys.argv[4]); th = (len(sys.argv) <= 5 or sys.argv[5] != 'notheta')
    for p in sympy.primerange(int(sys.argv[1]), int(sys.argv[2]) + 1):
        analyze(p, PR, N, th)
