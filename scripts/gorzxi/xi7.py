# Level-4 sanity check of the Stein moment route used in GORZXi/XiStein+XiMoments (u = log t variable).
# M = F index, c root of (pi e^c - 1/4) c = M, lam1 = pi e^{c-1}, lam2 = M/c^2,
# S_q = int_0^oo (u-c)^{2q} u^M e^{u/4 - pi e^u} du  (log-scaled, scipy).
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
def S(M, c, q, theta=False):
    lp = lambda u: M*np.log(u) + u/4 - np.pi*np.exp(u)
    l0 = lp(c)
    def f(u):
        th = 1.0 + (sum(np.exp(-np.pi*(k*k-1)*np.exp(u)) for k in range(2, 6)) if theta else 0.0)
        return (u-c)**(2*q) * np.exp(lp(u)-l0) * th
    return quad(f, 1e-12, c+30, points=[c-1, c, c+1], limit=400, epsabs=0, epsrel=1e-11)[0]
for M in [10, 40, 200, 1000, 10**4, 10**5]:
    c = brentq(lambda x: (np.pi*np.exp(x)-0.25)*x - M, 0.1, np.log(M+1)+1)
    l1, l2 = np.pi*np.exp(c-1), M/c**2
    s = [S(M, c, q) for q in range(0, 9)]
    I_ok = all(l2*s[q+1] <= (2*q+1)*s[q]*(1+1e-9) for q in range(0, 4))
    II_ok = all(l1*s[q+1] <= ((2*q+1)*s[q] + l1*s[2*q+2])*(1+1e-9) for q in range(0, 3))
    st = [S(M, c, q, True) for q in (0, 2)]
    print(f"M={M} c={c:.3f} c<=log(M+1):{c<=np.log(M+1)} lam1={l1:.3g} lam2={l2:.3g} lam1<=lam2^2:{l1<=l2**2}"
          f" (I):{I_ok} (II):{II_ok}")
    print("   lam1^q S_q/S_0 (q=1..4):", [round(l1**q*s[q]/s[0], 4) for q in range(1, 5)],
          " theta/clean S0,S2:", round(st[0]/s[0], 8), round(st[1]/s[2], 8),
          " n*eps^2 (n=M/2+1):", round((M/2+1)/(c**2*l1), 4))
