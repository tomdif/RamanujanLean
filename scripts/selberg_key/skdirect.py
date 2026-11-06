"""End-to-end check of the SK chain at T = 400 (zgrid.txt): measured (1/T) int_T^{2T} I(t)^2,
I(t) = int_t^{t+h} Z|M|^2, versus the prediction (1/T) int_T^{2T} du int_{-h}^{h}(h-|v|) 2Re A(v, log(u/2pi)) dv.
Both normalized by h^2.  Usage: python3 skdirect.py y [y ...]  (y=1: no mollifier)."""
import sys, io, numpy as np, post
d = np.loadtxt(io.StringIO(open('zgrid.txt').read().replace(' E', 'E'))); t = d[:, 0]; Z = d[:, 1]; dt = t[1] - t[0]
T = 400.0; logT = np.log(T)
tau = dict((int(a), float(b)) for a, b in (l.split() for l in open('taup.txt')))
def alpha(n):
    a = 1.0; p = 2
    while n > 1:
        if n % p == 0:
            e = 0
            while n % p == 0: n //= p; e += 1
            l = tau[p] / p**5.5; P = [1, -l, 1] + [0] * 10; A = [1.0] + [0.0] * 10
            for k in range(1, 11): A[k] = (P[k] - sum(A[i] * A[k - i] for i in range(1, k))) / 2
            a *= A[e]
        p += 1
    return a
for y in [int(a) for a in sys.argv[1:]] or [1]:
    if y == 1: w = np.ones_like(t)
    else:
        b = [0.0] + [alpha(n) * (1 - np.log(n) / np.log(y)) for n in range(1, y + 1)]
        w = np.abs(sum(b[n] * n**-0.5 * np.exp(-1j * t * np.log(n)) for n in range(1, y + 1)))**2
    F = Z * w; cF = np.concatenate([[0], np.cumsum((F[1:] + F[:-1]) / 2 * dt)])
    if y > 1: vv, S, S0 = post.load(y)
    for K in (1, 2, 4, 8):
        h = K / logT; k = int(round(h / dt))
        i0 = np.searchsorted(t, T); i1 = np.searchsorted(t, 2 * T)
        I = cF[i0 + k:i1 + 1 + k] - cF[i0:i1 + 1]
        meas = np.trapz(I**2, t[i0:i1 + 1]) / T
        us = np.linspace(T, 2 * T, 81); ws = np.linspace(0, h, 401)[1:]
        if y == 1: Sw = S0w = np.ones_like(ws)
        else: Sw, S0w = post.interp(vv, S, ws), post.interp(vv, S0, ws)
        pr = []
        for u in us:
            L = np.log(u / (2 * np.pi)); ph = np.exp(-1j * ws * L)
            A = post.r0 / (1j * ws) * (np.exp(-ws**2 / 4) * S0w - ph * Sw) + post.gR * ph * Sw
            f = (h - ws) * 2 * A.real; f = np.concatenate([[2 * f[0] - f[1]], f])
            pr.append(2 * np.trapz(f, np.concatenate([[0], ws])))
        pred = np.trapz(pr, us) / T
        print('y=%3d K=%d h=%.3f  measured/h^2=%.4f  predicted/h^2=%.4f  ratio=%.3f' % (y, K, h, meas / h**2, pred / h**2, meas / pred))
