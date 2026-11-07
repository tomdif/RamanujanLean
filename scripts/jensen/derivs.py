# Symbolic derivative data for f(s) = log M(n+s), M = K e^U (U-1)/(2U^3), U^2 = a(n+s-1/24), a = 2 pi^2/3.
# In h = 1/U:  d/ds = (a/(2U)) d/dU = -(a/2) h^3 d/dh.
# R_m(h) := f^{(m)}(s) * U^(2m-1)  (a rational function of h, analytic at h = 0, polynomial in a).
import sympy as sp
h, a = sp.symbols('h a', positive=True)
def Rlist(mmax=7):
    g = sp.Rational(1, 2)*a*h*(1 + h/(1 - h) - 3*h)        # f'
    out = {1: sp.cancel(g*h**(-1))}
    for m in range(2, mmax+1):
        g = sp.cancel(-a/2*h**3*sp.diff(g, h))
        out[m] = sp.cancel(g*h**(1-2*m))
    return out
if __name__ == '__main__':
    for m, R in Rlist().items():
        print(m, sp.factor(R), '   R(0)=', sp.factor(R.subs(h, 0)))
