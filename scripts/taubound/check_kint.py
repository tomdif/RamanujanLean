# Numerical sanity check of the unfolded Poincare-series formula used in TauBound:
#   c^{-12} K(n,c,y) = 2*pi*n^{11/2} J_11(4*pi*sqrt(n)/c)/c,  K = int_R w^-12 e(-1/(c^2 w)) e(-n w) dx, w=x+iy
# and lambda*tau(n) = [n=1] + sum_c c^-12 S(1,n;c) K(n,c,1/n), lambda = p(1).
import mpmath as mp
from math import gcd
mp.mp.dps = 30
def e(z): return mp.exp(2j*mp.pi*z)
def K(n,c,y):
    f = lambda x: (x+1j*y)**-12 * e(-1/(c**2*(x+1j*y))) * e(-n*(x+1j*y))
    return mp.quad(f, [-mp.inf,-1,-0.1,0,0.1,1,mp.inf])
def S(m,n,c):
    return sum(e((m*d+n*pow(d,-1,c))/c) for d in range(c) if gcd(d,c)==1) if c>1 else 1
for (n,c) in [(1,1),(2,1),(1,2),(3,2)]:
    y=1.0/n
    lhs = c**-12*K(n,c,y)
    rhs = 2*mp.pi*n**5.5*mp.besselj(11,4*mp.pi*mp.sqrt(n)/c)/c
    print(n,c,mp.nstr(lhs,12),mp.nstr(rhs,12))
def p(n,C=40):
    return (1 if n==1 else 0) + sum(2*mp.pi*n**5.5*mp.besselj(11,4*mp.pi*mp.sqrt(n)/c)/c*S(1,n,c) for c in range(1,C))
p1=p(1)
tau={1:1,2:-24,3:252,4:-1472,5:4830}
for n in range(1,6): print(n, mp.nstr(p(n)/p1,10), tau[n])
