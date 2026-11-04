# Validate the Stein-type moment route for XiKernelHyp (t-variable, clean kernel e^{-pi t}).
# c: root of (pi e^c - 1/4) c = m; lam1 = pi e^{c-1}; lam2 = m/c^2.
# S_q = int_1^oo (log t - c)^{2q} (log t)^m t^{-3/4} e^{-pi t} dt  (u = log t substitution).
from mpmath import mp, mpf, quad, exp, log, pi, findroot, inf, e
mp.dps = 20
def S(m, c, q, theta=False):
    def f(u):
        th = sum(exp(-pi*k*k*exp(u)) for k in range(1, 5)) if theta else exp(-pi*exp(u))
        return (u-c)**(2*q) * u**m * exp(u/4) * th
    return quad(f, [0, c-2, c-1, c, c+1, c+3, inf])
for m in [10, 40, 200, 1000]:
    c = findroot(lambda x: (pi*exp(x)-mpf(1)/4)*x - m, log(m))
    l1, l2 = pi*exp(c-1), mpf(m)/c**2
    s = [S(m, c, q) for q in range(0, 5)]
    # Stein identity check q=1: int [(pi t-1/4) log t - m] (log t)^{m-1} x t^{-3/4} e^{-pi t} = S_0
    lhs = quad(lambda u: ((pi*exp(u)-mpf(1)/4)*u - m)*u**(m-1)*(u-c)*exp(u/4-pi*exp(u)), [0, c-1, c, c+1, inf])
    print(f"m={m} c={float(c):.3f} lam1={float(l1):.2f} lam2={float(l2):.2f} lam2^2>=lam1:{l2**2>=l1}"
          f" stein_q1_rel_err={float(lhs/s[0]-1):.1e}")
    print("   lam1^q S_q/S_0:", [round(float(l1**q*s[q]/s[0]), 4) for q in range(1, 5)],
          " (I) ok:", all(l2*s[q] <= (2*q-1)*s[q-1] for q in range(1, 5)),
          " (II,R=q+1) ok:", all(l1*s[q] <= (2*q-1)*s[q-1] + l1*s[2*q] for q in range(1, 3)))
    st = [S(m, c, q, True) for q in (0, 1, 2)]
    print("   theta/clean ratio S_0, S_2:", float(st[0]/s[0]), float(st[2]/s[2]),
          " n*eps^2 = n/(c^2 lam1), n=m/2:", float((m/2)/(c**2*l1)))
