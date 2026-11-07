"""Direct end-to-end check of the diagonal formula: lag correlation of the actual F = Z |M|^2,
C(v) = (1/T) int_T^{2T} F(u) F(u+v) du  (Z from zgrid.gp, T = 400),
against the prediction 2 <Re A(v, log(u/2pi))>_u of docs/SELBERG_KEY.md section 3.
y = 1: S = S0 = 1.  y > 1: S, S0 from sk.c output S_y<y>.txt (run with vmax >= 3)."""
import sys, numpy as np, post
import io
d = np.loadtxt(io.StringIO(open('zgrid.txt').read().replace(' E', 'E'))); t = d[:, 0]; Z = d[:, 1]; dt = t[1] - t[0]
T = 400.0
tau = dict((int(a), float(b)) for a, b in (l.split() for l in open('taup.txt')))
def spf(n):
    p = 2
    while p * p <= n:
        if n % p == 0: return p
        p += 1
    return n
def alpha(n):
    a = 1.0
    while n > 1:
        p = spf(n); e = 0
        while n % p == 0: n //= p; e += 1
        l = tau[p] / p**5.5; P = [1, -l, 1] + [0] * 10; A = [1.0] + [0.0] * 10
        for k in range(1, 11): A[k] = (P[k] - sum(A[i] * A[k - i] for i in range(1, k))) / 2
        a *= A[e]
    return a
for y in [int(a) for a in sys.argv[1:]] or [1]:
    if y == 1: w = np.ones_like(t)
    else:
        b = [0.0] + [alpha(n) * (1 - np.log(n) / np.log(y)) for n in range(1, y + 1)]
        M = sum(b[n] * n**-0.5 * np.exp(-1j * t * np.log(n)) for n in range(1, y + 1))
        w = np.abs(M)**2
    F = Z * w
    i0 = np.searchsorted(t, T); i1 = np.searchsorted(t, 2 * T)
    u = t[i0:i1 + 1]; Lu = np.log(u / (2 * np.pi))
    if y > 1: vv, S, S0 = post.load(y)
    print('=== y = %d ===   (v, C(v) measured, prediction 2<Re A>, ratio)' % y)
    for k in list(range(0, 300, 20)):
        v = k * dt
        C = np.trapz(F[i0:i1 + 1] * F[i0 + k:i1 + 1 + k], u) / T
        if v == 0:
            vv0 = 1e-6
        else:
            vv0 = v
        if y == 1: Sv = S0v = 1.0
        else: Sv, S0v = post.interp(vv, S, np.array([vv0]))[0], post.interp(vv, S0, np.array([vv0]))[0]
        A = post.r0 / (1j * vv0) * (np.exp(-vv0**2 / 4) * S0v - np.exp(-1j * vv0 * Lu) * Sv) + post.gR * np.exp(-1j * vv0 * Lu) * Sv
        P = np.trapz(2 * A.real, u) / T
        print('  v=%.2f  C=%9.4f  pred=%9.4f  ratio=%.3f' % (v, C, P, C / P if abs(P) > 1e-9 else float('nan')))
