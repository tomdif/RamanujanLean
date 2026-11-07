# Prototype of the Lean-checkable tail scheme (Taylor at 0, Leibniz recurrence, (u,omega) polynomials)
import sys
from math import comb, factorial
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 200
PI = arb.pi(); A = 2*PI**2/3

def deriv_data(P):   # P: dict (p,q)->Fr ; returns (1/2) u d/dU P
    out = {}
    for (p, q), c in P.items():
        for key, cc in (((p+2, q), -Fr(p)*c/2), ((p+1, q+1), -Fr(q)*c/2)):
            if cc: out[key] = out.get(key, 0) + cc
    return {k: v for k, v in out.items() if v}
def Plist(mmax):
    P = {1: {(1, 0): Fr(1, 2), (1, 1): Fr(1, 2), (2, 0): Fr(-3, 2)}}
    for m in range(1, mmax): P[m+1] = deriv_data(P[m])
    return P
def Qeval(Pm, m, u, om):   # P_m(U) = u^{2m-1} Q_m(u, omega)
    s = arb(0)
    for (p, q), c in Pm.items():
        e = p + q - (2*m - 1); assert e >= 0
        s += arb(c.numerator)/c.denominator * u**e * om**q
    return s
def ar(x):
    if isinstance(x, Fr): return arb(x.numerator)/x.denominator
    return arb(x)
def U(lo, hi): return ar(lo).union(ar(hi))
def D(k, i): return sum((-1)**(k-j)*comb(k, j)*j**i for j in range(k+1))

adaptive = False
def box(tlo, thi, d, L, pts, P, Keps=60):
    inf = (tlo == 0)
    t0 = U(tlo, thi); u0 = t0**2
    om0 = U(1/(1-ar(tlo)**2), 1/(1-ar(thi)**2))
    c2 = -Qeval(P[2], 2, u0, om0)/2; sq = c2.sqrt()
    delta = A*sq*t0**3
    Km = d + L
    def c2pow(m): return c2**(m//2) * (sq if m % 2 else 1)
    Phi0 = [arb(0), arb(0), arb(-2)] + [Qeval(P[m], m, u0, om0)/c2pow(m)*t0**(m-2) for m in range(3, Km+1)]
    def rec(Ph, g0, n):
        g = [g0]
        for k in range(n):
            g.append(sum((comb(k, i)*g[k-i]*Ph[i+1] for i in range(k+1)), arb(0)))
        return g
    g0 = rec(Phi0, arb(1), Km)
    rhomax = (1 + A*d*ar(thi)**4).sqrt()
    us = U(ar(tlo)**2/rhomax, ar(thi)**2); oms = U(1, 1/(1-ar(thi)**2)); ratio = U(1/rhomax, 1)
    R2 = Qeval(P[2], 2, us, oms)
    sI = U(0, d)
    Phs = [None]*(Km+1)
    Phs[0] = sI**2/2*A**2*ratio**3*t0**6*R2
    Phs[1] = sI*A*ratio**3*t0**3*R2/sq
    for m in range(2, Km+1):
        Phs[m] = Qeval(P[m], m, us, oms)/c2pow(m)*ratio**(2*m-1)*t0**(m-2)
    e0 = U(1 + Phs[0].lower(), 1)
    gs = rec(Phs, e0, Km)
    gam = [arb(1)]
    for k in range(1, d+1):
        K = d + L
        main = sum((arb(D(k, i))/factorial(i)*delta**(i-k)*g0[i] for i in range(k, K)), arb(0))
        rem = sum(comb(k, j)*arb(j)**K for j in range(k+1))/factorial(K)*delta**(K-k)*abs(gs[K]).upper()
        gam.append(main + U(-rem, rem))
    # epsilon term
    for k in range(d+1):
        if inf:
            # |eps_j| delta^-k <= 4 K! 2^K U0^{2-K+3k/2} / (a sq)^k ;  U0^{-1}=t0^2
            E = 4*factorial(Keps)*arb(2)**Keps*ar(thi)**(2*Keps-4-3*k)/(A*sq.lower())**k
        else:
            Ulo = 1/ar(thi)**2; Uhi = 1/ar(tlo)**2
            x = Ulo/2; S = sum((x**i/factorial(i) for i in range(Keps+1)), arb(0))
            E = 2*(Uhi*rhomax)**3/(Ulo-1)/S / (A*sq.lower()*ar(tlo)**3)**k
        E = arb(2)**k*E
        gam[k] = gam[k] + U(-E.upper(), E.upper())
    if pts is None or adaptive:
        import numpy as np
        dm = float(delta.mid()); gm = [float(g.mid()) for g in gam]
        coeffs = np.zeros(d+1)
        for k in range(d+1):
            pk = np.polynomial.polynomial.polypow([-1.0, dm], k)
            coeffs[d-k:d+1] += comb(d, k)*gm[k]*pk
        r = np.roots(coeffs[::-1])
        if np.max(np.abs(r.imag)) > 1e-9: return False, -1, None
        r = np.sort(r.real)
        ps = [r[0]-(r[1]-r[0])/2] + [(r[i]+r[i+1])/2 for i in range(d-1)] + [r[-1]+(r[-1]-r[-2])/2]
        pts = [Fr(int(round(p*256)), 256) for p in ps]
        global last_pts
        last_pts = pts
    res = []
    for i, xp in enumerate(pts):
        xv = ar(xp)
        G = sum((comb(d, k)*gam[k]*xv**(d-k)*(delta*xv-1)**k for k in range(d+1)), arb(0))
        want = (-1)**(d-i)
        if not (G*want > 0): return False, i, G
        res.append((G*want).lower())
    return True, min(res), None

if __name__ == '__main__':
    if len(sys.argv) > 4: adaptive = True
    d = int(sys.argv[1]); Ustart = float(sys.argv[2]); L = int(sys.argv[3])
    P = Plist(d + L)
    print('monomials per P_m:', [len(P[m]) for m in sorted(P)])
    pts = {6: [Fr(-365,64), Fr(-59,16), Fr(-113,64), 0, Fr(113,64), Fr(59,16), Fr(365,64)]}[d] if d == 6 else None
    if pts is None:
        import sympy as sp
        x = sp.Symbol('x'); T = sp.hermite(d, x/2)  # proportional to T_d
        r = sorted(float(z) for z in sp.Poly(T, x).nroots())
        ps = [r[0]-(r[1]-r[0])/2] + [(r[i]+r[i+1])/2 for i in range(d-1)] + [r[-1]+(r[-1]-r[-2])/2]
        pts = [Fr(round(p*64), 64) for p in ps]
    print('pts', pts)
    tmax = Fr(1)/Fr(Ustart).limit_denominator(1000)**0  # placeholder
    import math
    t = 1/math.sqrt(Ustart); boxes = []
        # grow geometric boxes downward from t until infinite box works
    thi = Fr(t).limit_denominator(10**6); nb = 0; step = 0.01
    while True:
        okinf, minf, _ = box(0, thi, d, L, pts, P)
        if okinf: print('infinite box [0, %s] OK (U >= %.1f) margin %.3g' % (thi, float(1/thi**2), float(minf))); break
        while True:
            tlo = Fr(float(thi)*(1-step)).limit_denominator(10**6)
            ok, m, G = box(tlo, thi, d, L, pts, P)
            if ok: break
            step /= 2
            if step < 1e-5: print('FAIL at t=', float(thi), 'U=', float(1/thi**2), G); sys.exit(1)
        nb += 1; boxes.append((tlo, thi)); thi = tlo; step = min(step*1.5, 0.05)
    print('finite boxes', nb)
