"""
Certified (ball-arithmetic, python-flint arb) proof that the degree-d partition Jensen polynomial
    J^{d,n}(X) = sum_{j=0}^d C(d,j) p(n+j) X^j
is hyperbolic for every integer n with U(n) = pi*sqrt((2/3)(n-1/24)) >= U_start.

Only input about p(n): the explicit bound proved in Lean (Rademacher.p_sub_main_le, n >= 2)
    |p(m) - M(m)| <= K e^{U_m/2},   M(m) = K e^{U_m} (U_m - 1)/(2 U_m^3).
See docs/JENSEN_THRESHOLDS.md for the argument; summary:
  f(s) = log M(n+s) (real s), A = f'(0), delta^2 = -f''(0)/2, phi(s) = f(s)-f(0)-A s,
  w_j = p(n+j) e^{-A j}/M(n) = e^{phi(j)} (1+eps_j),
  J(e^{-A}(delta x - 1)) = M(n) delta^d G(x),  G(x) = sum_k C(d,k) gamma_k x^{d-k} (delta x - 1)^k,
  gamma_k = Delta^k w(0)/delta^k  (Newton forward-difference identity),
  Delta^k g(0) = int_0^k M_k g^{(k)}  (B-spline Peano kernel; mean k/2, variance k/12), so
  gamma_k in [e^{phi}Y_k(Phi)](k/2) + (k/24) delta^2 hull_{[0,k]} e^{phi}Y_{k+2}(Phi) + [-2^k epsmax/delta^k, +],
  with (e^phi)^{(k)} = e^phi Y_k(phi',...,phi^{(k)}) (complete Bell) and Phi_m = phi^{(m)}/delta^m enclosed in
  ball arithmetic from the exact rational functions R_m (derivs.py).
  If G alternates in sign on d+1 increasing points, J has d distinct (negative) real roots.
Usage: python3 tail_cert.py d U_start [adaptive]   (boxes in U = U(n) cover [U_start, oo), the last one infinite)
"""
import sys
from math import comb
import flint
from flint import arb, ctx
import sympy as sp
from derivs import Rlist, h as hs, a as asym

ctx.prec = 200
PI = arb.pi()
A = 2*PI**2/3

def mk_R(mmax):
    Rs = Rlist(mmax)
    funcs = {}
    for m, R in Rs.items():
        num, den = sp.fraction(sp.together(R))
        pn = sp.Poly(sp.expand(num), hs, asym)
        pd = sp.Poly(sp.expand(den), hs, asym)
        def ev(P, hv):
            s = arb(0)
            for (i, j), c in P.terms():
                s += arb(sp.Rational(c).p)/arb(sp.Rational(c).q) * hv**i * A**j
            return s
        funcs[m] = (lambda pn, pd: (lambda hv: ev(pn, hv)/ev(pd, hv)))(pn, pd)
    return funcs

def bell(xs, k):
    # complete Bell polynomials Y_0..Y_k, xs[1..k]
    Y = [arb(1)]
    for n in range(k):
        Y.append(sum((comb(n, i)*Y[n-i]*xs[i+1] for i in range(n+1)), arb(0)))
    return Y

def target(d):
    # gamma_k limits: Y_k(0,-2,0,...) ; T(x) = sum C(d,k) Y_k (-1)^k x^{d-k}
    xs = [arb(0)]*(d+1); xs[2] = arb(-2)
    Y = bell(xs, d)
    return [int(Y[k].unique_fmpz()) for k in range(d+1)]

def test_points(d):
    tk = target(d)
    x = sp.Symbol('x')
    T = sum(comb(d, k)*tk[k]*(-1)**k*x**(d-k) for k in range(d+1))
    roots = sorted(float(r) for r in sp.Poly(T, x).nroots())
    pts = [roots[0] - 1.0] + [(roots[i]+roots[i+1])/2 for i in range(d-1)] + [roots[-1] + 1.0]
    return [sp.Rational(round(p*64), 64) for p in pts], T, x

def certify_box(Ulo, Uhi, d, Rf, pts, detail=None):
    """True iff the sign pattern of G at pts is certified for all n with U(n) in [Ulo, Uhi] (Uhi=None: inf).

    gamma_k = Delta^k w(0)/delta^k is enclosed through the Peano-kernel (B-spline) form
        Delta^k w(0) = int_0^k M_k(t) w^{(k)}(t) dt,  M_k >= 0, int M_k = 1, mean k/2, variance k/12,
    so, Taylor-expanding w^{(k)} about c = k/2 (the linear term integrates to 0),
        gamma_k in w^{(k)}(c)/delta^k + (k/24) delta^2 * hull_{t in [0,k]} w^{(k+2)}(t)/delta^{k+2}.
    """
    Ulo = arb(Ulo)
    inf = Uhi is None
    h0 = (arb(0).union(1/Ulo)) if inf else ((1/arb(Uhi)).union(1/Ulo))
    Q = -Rf[2](h0)/2                                    # delta^2 U0^3
    sq = Q.sqrt()
    def U0pow(e):   # range of U0^e, e <= 0
        if e == 0: return arb(1)
        lo = arb(0) if inf else arb(Uhi)**e
        return lo.union(Ulo**e)
    def rho_range(slo, shi):   # range of U_s/U0 for s in [slo, shi]
        lo = arb(1) if (inf or slo == 0) else (1 + A*slo/arb(Uhi)**2).sqrt()
        return lo.union((1 + A*shi/Ulo**2).sqrt())
    def Phis(slo, shi, mmax):
        rs = rho_range(slo, shi); rt = rho_range(0, shi)
        hsr = (arb(0) if inf else 1/(arb(Uhi)*rt.upper())).union(1/Ulo)   # h at U_s or U_theta
        sint = arb(slo).union(arb(shi))
        R2t = Rf[2](hsr)
        P = [None]*(mmax+1)
        P[0] = (sint**2/2) * R2t * rt**(-3) * U0pow(-3)          # phi(s) = s^2/2 f''(theta)
        P[1] = sint * R2t/sq * rt**(-3) * U0pow(-1.5)            # phi'(s) = s f''(theta)
        for m in range(2, mmax+1):
            P[m] = Rf[m](hsr)/Q**(arb(m)/2) * rs**(1-2*m) * U0pow(1-arb(m)/2)
        return P
    assert float(Ulo) > 3*d + 10
    delta = sq * U0pow(-1.5)
    gam = [arb(1)]
    for k in range(1, d+1):
        c = arb(k)/2
        Pc = Phis(c, c, k)
        main = Pc[0].exp() * bell(Pc, k)[k]
        Pw = Phis(0, k, k+2)
        rem = arb(k)/24 * delta**2 * Pw[0].exp() * bell(Pw, k+2)[k+2]
        gam.append(main + arb(0).union(rem))
    # error part: eps <= 2U^3/(U-1) e^{-U/2};  eps/delta^k = eps U0^{3k/2}/Q^{k/2}; decreasing in U for U>=Ulo
    for k in range(d+1):
        Ek = arb(2)**k * 2*Ulo**3/(Ulo-1)*(-Ulo/2).exp() * Ulo**(arb(3*k)/2) / Q**(arb(k)/2)
        gam[k] = gam[k] + (-Ek).union(Ek)
    if pts is None:   # adaptive test points: separate the roots of the midpoint polynomial
        import numpy as np
        dm = float(delta.mid()); gm = [float(g.mid()) for g in gam]
        coeffs = np.zeros(d+1)
        for k in range(d+1):
            pk = np.polynomial.polynomial.polypow([-1.0, dm], k)
            term = comb(d, k)*gm[k]*np.polymul([1.0] + [0.0]*0, pk)
            coeffs[d-k:d-k+len(term)] += term[:d+1-(d-k)]
        r = np.roots(coeffs[::-1])
        if np.max(np.abs(r.imag)) > 1e-9: return False, 'complex midpoint roots'
        r = np.sort(r.real)
        g0 = r[1]-r[0]; g1 = r[-1]-r[-2]
        ps = [r[0]-g0/2] + [(r[i]+r[i+1])/2 for i in range(d-1)] + [r[-1]+g1/2]
        pts = [sp.Rational(int(round(p*1024)), 1024) for p in ps]
    worst = None
    for i, xp in enumerate(pts):
        xv = arb(xp.p)/xp.q
        G = sum((comb(d, k)*gam[k]*xv**(d-k)*(delta*xv-1)**k for k in range(d+1)), arb(0))
        if detail is not None: detail.append(G)
        want = (-1)**(d - i)   # sign of T at pts[i]: leading coeff +, so rightmost point +
        if not (G*want > 0):
            return False, (i, G)
        m = (G*want).lower()
        worst = m if worst is None or m < worst else worst
    return True, worst

def U_of(n):
    return float((A*(arb(n) - arb(1)/24)).sqrt())

def n_of_U(U):
    # least integer n with U(n) >= U
    import math
    n = math.ceil(float(U)**2/float(A) + 1/24) - 2
    while U_of(n) < U: n += 1
    return n

if __name__ == '__main__':
    d = int(sys.argv[1]); Ustart = float(sys.argv[2])
    Rf = mk_R(d+2)
    pts, T, x = test_points(d)
    if len(sys.argv) > 3 and sys.argv[3] == 'adaptive': pts = None
    print('d =', d, ' target T(x) =', T)
    if pts is not None: print('test points', pts, ' T(pts) =', [float(T.subs(x, p)) for p in pts])
    U = Ustart; nb = 0; step = 0.01; minw = None
    while True:
        if nb % 20 == 0:
            ok, w = certify_box(U, None, d, Rf, pts)
            if ok:
                print('tail box [%.6g, inf) OK, margin %.4g' % (U, float(w.lower()))); break
        while True:
            ok, w = certify_box(U, U*(1+step), d, Rf, pts)
            if ok: break
            step /= 2
            if step < 1e-7: print('FAIL near U =', U); sys.exit(1)
        minw = w if minw is None or w < minw else minw
        nb += 1; U = U*(1+step); step = min(step*2, 0.05)
    print('finite boxes:', nb, ' min margin', float(minw.lower()) if minw is not None else None)
    print('CERTIFIED: J^{%d,n} hyperbolic for all n with U(n) >= %g, i.e. all n >= %d' % (d, Ustart, n_of_U(Ustart)))
