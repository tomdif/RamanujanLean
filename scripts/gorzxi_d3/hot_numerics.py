# Level-4 numerics for the degree-3 case (Dimitrov-Lucas higher-order Turan inequalities).
# gamma(n) = 32 n!/(2n)! int_0^oo u^{2n} Phi(u) du  (GORZXiEff.gamma_eq_mom).
# Composite Gauss-Legendre with a single evaluation of Phi at all nodes; all moments share the nodes.
import mpmath as mp, sys, pickle
mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 60
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
pi = mp.pi
def Phi(u):
    s = mp.mpf(0)
    for k in range(1, 10):
        c = pi * k * k
        s += (2 * c * c * mp.exp(mp.mpf(9) / 2 * u) - 3 * c * mp.exp(mp.mpf(5) / 2 * u)) * mp.exp(-c * mp.exp(2 * u))
    return s
# Gauss-Legendre nodes on [-1,1]
deg = int(sys.argv[3]) if len(sys.argv) > 3 else 40
xs, ws = [], []
P = lambda x: mp.legendre(deg, x)
for i in range(1, deg + 1):
    x = mp.cos(pi * (i - mp.mpf(1) / 4) / (deg + mp.mpf(1) / 2))
    for _ in range(100):
        p0, p1 = mp.mpf(1), x
        for k in range(2, deg + 1):
            p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
        dp = deg * (x * p1 - p0) / (x * x - 1)
        dx = p1 / dp
        x -= dx
        if abs(dx) < mp.mpf(10) ** (-mp.mp.dps + 5): break
    p0, p1 = mp.mpf(1), x
    for k in range(2, deg + 1):
        p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
    dp = deg * (x * p1 - p0) / (x * x - 1)
    xs.append(x); ws.append(2 / ((1 - x * x) * dp * dp))
U = 7; M = 140
nodes, wts = [], []
for j in range(M):
    a = mp.mpf(U) * j / M; b = mp.mpf(U) * (j + 1) / M
    for x, w in zip(xs, ws):
        nodes.append((a + b) / 2 + (b - a) / 2 * x); wts.append(w * (b - a) / 2)
fw = [w * Phi(u) for u, w in zip(nodes, wts)]
u2 = [u * u for u in nodes]
b = []
cur = fw[:]
for n in range(N + 4):
    b.append(mp.fsum(cur))
    cur = [c * v for c, v in zip(cur, u2)]
g = [32 * mp.factorial(n) / mp.factorial(2 * n) * b[n] for n in range(N + 4)]
pickle.dump([str(x) for x in g], open(sys.argv[4] if len(sys.argv) > 4 else '/dev/null', 'wb'))
print("gamma(0)=", mp.nstr(g[0], 15), " gamma(10)=", mp.nstr(g[10], 15), " (GORZ 1.63233804903e-17)")
if N >= 100: print("gamma(100)=", mp.nstr(g[100], 15), " (GORZ 6.57772637858e-205)")
worstQ = (0, None); bad = []
for m in range(1, N + 1):
    T0 = g[m] ** 2 - g[m - 1] * g[m + 1]; T1 = g[m + 1] ** 2 - g[m] * g[m + 2]
    S = g[m] * g[m + 1] - g[m - 1] * g[m + 2]
    Q = S * S / (4 * T0 * T1)
    if T0 <= 0 or T1 <= 0 or Q > 1: bad.append(m)
    if Q > worstQ[0]: worstQ = (Q, m)
    if m in (1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000) or m == N:
        print("m=%5d  Q=S^2/(4T0T1)=%s  m*Q=%s" % (m, mp.nstr(Q, 8), mp.nstr(m * Q, 8)))
print("HOT failures:", bad, " max Q =", mp.nstr(worstQ[0], 10), "at m =", worstQ[1])
# Lipschitz form: a_n = 1 - g_n g_{n+2}/g_{n+1}^2 (Turan defect), Lam_n = a_n^{-1/2};
# HOT at centre m=n+1  <=>  |Lam_{n+1} - Lam_n| <= 1   (given a_n, a_{n+1} > 0).
a = [1 - g[n] * g[n + 2] / g[n + 1] ** 2 for n in range(N + 1)]
print("min Turan defect a_n:", mp.nstr(min(a), 10), " min n*a_n:", mp.nstr(min((n + 1) * a[n] for n in range(N + 1)), 10))
Lam = [x ** (-mp.mpf(1) / 2) for x in a]
dL = [Lam[n + 1] - Lam[n] for n in range(N)]
print("max dLam =", mp.nstr(max(dL), 12), "at n =", dL.index(max(dL)), "; min dLam =", mp.nstr(min(dL), 12), "at n =", dL.index(min(dL)))
for n in (0, 1, 2, 3, 5, 10, 30, 100, 300, 1000, 3000):
    if n < N: print("n=%5d a_n=%s Lam_n=%s dLam=%s sqrt(n+1)*dLam=%s" % (n, mp.nstr(a[n], 10), mp.nstr(Lam[n], 10), mp.nstr(dL[n], 10), mp.nstr(mp.sqrt(n + 1) * dL[n], 8)))
