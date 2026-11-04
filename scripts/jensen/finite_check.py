"""
Exact finite-range verification for the partition Jensen polynomials
    J^{d,n}(X) = sum_{j=0}^d C(d,j) p(n+j) X^j.
(1) exact real-root counts (sympy count_roots: exact integer Sturm/Vincent, no floating point) for 1 <= n < n0(d);
(2) for d = 6, 7: rational sign-alternation certificates for N(d) <= n < n0(d) (each verified exactly in
    integer arithmetic) and a Laguerre-inequality failure certificate at n = N(d) - 1, written to certs_d*.json.
Usage: python3 finite_check.py
"""
import json, sys
from math import comb
from fractions import Fraction as Fr
import sympy as sp
import mpmath as mp

N0 = {2: 200, 3: 380, 4: 643, 5: 973, 6: 1259, 7: 1676}   # tail certificate start (tail_cert.py)
NMAX = max(N0.values()) + 10
p = [0]*(NMAX+1); p[0] = 1
for n in range(1, NMAX+1):
    s = 0; k = 1
    while True:
        g1 = k*(3*k-1)//2
        if g1 > n: break
        g2 = k*(3*k+1)//2
        t = p[n-g1] + (p[n-g2] if g2 <= n else 0)
        s += t if k % 2 else -t
        k += 1
    p[n] = s
assert p[100] == 190569292 and p[1000] == 24061467864032622473692149727991

X = sp.Symbol('X')
def coeffs(d, n): return [comb(d, j)*p[n+j] for j in range(d+1)]
def J_at(cs, x):   # exact value at rational x
    return sum(c*x**j for j, c in enumerate(cs))

def count_real(d, n):
    return sp.Poly(list(reversed(coeffs(d, n))), X).count_roots()

def sign_cert(d, n):
    cs = coeffs(d, n)
    mp.mp.dps = 120
    rts = sorted(mp.re(r) for r in mp.polyroots(list(reversed(cs)), maxsteps=400, extraprec=400))
    pts = [rts[0] - (rts[1]-rts[0])/2] + [(rts[i]+rts[i+1])/2 for i in range(d-1)] + [rts[-1] + (rts[-1]-rts[-2])/2]
    qs = []
    for i, x in enumerate(pts):
        gap = (rts[1]-rts[0])/4 if i == 0 else ((rts[-1]-rts[-2])/4 if i == d else (rts[i]-rts[i-1])/4)
        lim = 10
        while True:
            q = Fr(mp.nstr(x, 60)).limit_denominator(lim)
            if abs(mp.mpf(q.numerator)/q.denominator - x) < gap: break
            lim *= 10
        qs.append(q)
    # exact verification: increasing, alternating signs, rightmost positive (even degree: leftmost sign (-1)^d)
    assert all(qs[i] < qs[i+1] for i in range(d)) and qs[-1] < 0
    for i, q in enumerate(qs):
        v = J_at(cs, q)
        assert v != 0 and (v > 0) == ((d - i) % 2 == 0), (d, n, i)
    return [(-q.numerator, q.denominator) for q in qs]   # X_i = -a_i/b_i

def laguerre_cert(d, n):
    """rational x0 with (d-1) J'(x0)^2 - d J(x0) J''(x0) < 0 (impossible for real-rooted J)."""
    cs = coeffs(d, n)
    P = sp.Poly(list(reversed(cs)), X); P1 = P.diff(X); P2 = P1.diff(X)
    L = sp.Poly((d-1)*P1**2 - d*P*P2, X)
    mp.mp.dps = 80
    rts = mp.polyroots(list(reversed(cs)), maxsteps=400, extraprec=400)
    best = None
    for r in rts:
        if abs(mp.im(r)) > 0:
            for t in [mp.re(r)]:
                for lim in [10**k for k in range(1, 30)]:
                    q = Fr(mp.nstr(t, 60)).limit_denominator(lim)
                    val = L.eval(sp.Rational(q.numerator, q.denominator))
                    if val < 0:
                        best = q; break
                if best is not None: break
        if best is not None: break
    assert best is not None
    return (-best.numerator, best.denominator)

if __name__ == '__main__':
    res = {}
    for d in range(2, 8):
        last = None
        for n in range(1, N0[d]):
            if count_real(d, n) != d: last = n
        res[d] = last
        print('d=%d: exact root counts for 1 <= n < %d; last non-hyperbolic n = %s  (=> N(d) = %s in the'
              ' "hyperbolic for all n >= N" convention, given the tail certificate from n0 = %d)'
              % (d, N0[d], last, last+1, N0[d]), flush=True)
    for d in (6, 7):
        Nd = res[d] + 1
        certs = {n: sign_cert(d, n) for n in range(Nd, N0[d])}
        fail = laguerre_cert(d, Nd - 1)
        json.dump({'d': d, 'N': Nd, 'n0': N0[d], 'fail_n': Nd-1, 'laguerre_x0': fail,
                   'sign_certs': certs}, open('certs_d%d.json' % d, 'w'))
        maxden = max(b for c in certs.values() for (a, b) in c)
        print('d=%d: %d sign certificates verified exactly (max denominator %d); Laguerre failure at n=%d, x0=%s'
              % (d, len(certs), maxden, Nd-1, fail), flush=True)
