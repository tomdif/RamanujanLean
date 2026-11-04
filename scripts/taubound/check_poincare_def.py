# Check the explicit Poincare series definition used in TauBound/Poincare.lean:
#   P(z) = e(z) + sum_{c>=1} sum_{d in Z, (c,d)=1} (cz+d)^-12 e( dbar/c - 1/(c(cz+d)) ),  dbar = d^{-1} mod c
# against p(1)*Delta(z), p(1) = 2.84028737516...
import mpmath as mp
from math import gcd
mp.mp.dps = 20
def e(z): return mp.exp(2j*mp.pi*z)
def P(z, C=40, D=400):
    s = e(z)
    for c in range(1, C+1):
        for d in range(-D, D+1):
            if gcd(c, abs(d)) != 1: continue
            dbar = pow(d % c, -1, c) if c > 1 else 0
            w = c*z + d
            s += w**-12 * e(mp.mpf(dbar)/c - 1/(c*w))
    return s
def Delta(z, N=60):
    q = e(z); prod = mp.mpf(1)
    for n in range(1, N): prod *= (1-q**n)**24
    return q*prod
for z in [mp.mpc(0.1,1.1), mp.mpc(-0.3,0.8)]:
    r = P(z)/Delta(z)
    print(z, mp.nstr(r, 10))
