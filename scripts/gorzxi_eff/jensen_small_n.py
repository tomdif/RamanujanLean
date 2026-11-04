# Level-4: hyperbolicity of J^{d,n}_gamma for 2<=d<=8, 0<=n<=N, gamma(n) = 32 n!/(2n)! int_0^oo u^{2n} Phi.
# Exact Sturm counts (sympy, rational coefficients from 45-digit values).
import mpmath as mp, sys
import sympy as sp
mp.mp.dps = 50
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
pi = mp.pi


def Phi(u):
    s = mp.mpf(0)
    for k in range(1, 8):
        c = pi * k * k
        s += (2 * c * c * mp.exp(4.5 * u) - 3 * c * mp.exp(2.5 * u)) * mp.exp(-c * mp.exp(2 * u))
    return s


def mom(n):
    f = lambda u: u ** (2 * n) * Phi(u)
    pts = [mp.mpf(i) / 8 for i in range(0, 49)]
    return mp.quad(f, pts)


b = [mom(n) for n in range(N + 9)]
g = [32 * mp.factorial(n) / mp.factorial(2 * n) * b[n] for n in range(N + 9)]
print("gamma(0..3) =", [mp.nstr(x, 12) for x in g[:4]])
print("gamma(10) =", mp.nstr(g[10], 12), " (GORZ: 1.63233804903e-17)")
if N >= 100:
    print("gamma(100) =", mp.nstr(g[100], 12), " (GORZ: 6.57772637858e-205)")
X = sp.symbols('X')
bad = []
for d in range(2, 9):
    for n in range(0, N + 1):
        s = g[n + 1] / g[n]  # rescale X -> X/s
        coeffs = [mp.binomial(d, j) * g[n + j] / g[n] / s ** j for j in range(d + 1)]
        P = sp.Poly(sum(sp.Rational(mp.nstr(c, 45)) * X ** j for j, c in enumerate(coeffs)), X)
        r = P.count_roots()
        if r != d:
            bad.append((d, n, r))
    print("d =", d, "checked n = 0..%d" % N, "failures so far:", len(bad), flush=True)
print("FAILURES:", bad)
