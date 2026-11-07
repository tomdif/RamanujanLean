import mpmath as mp
exec(open('xi1.py').read().split('# direct Taylor check')[0])
mp.mp.dps=30
def Lam(s): return mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
g = lambda z: (-1+4*z*z)*Lam(mp.mpf(1)/2+z)
# Cauchy coefficients on circle radius r (entire fn, poles cancelled; avoid z=+-1/2 exactly)
r=mp.mpf('0.3'); N=64
vals=[g(r*mp.expjpi(2*mp.mpf(k)/N)) for k in range(N)]
def coef(m): return sum(vals[k]*mp.expjpi(-2*mp.mpf(k*m)/N) for k in range(N))/N/r**m
for n in range(0,6):
    direct = coef(2*n).real*mp.factorial(n)
    print(n, mp.nstr(direct,15), mp.nstr(gamma_n(n),15) if n>0 else mp.nstr(4-2*F(0),15))
for n in (10,100):
    print(n, mp.nstr(gamma_n(n),12))
