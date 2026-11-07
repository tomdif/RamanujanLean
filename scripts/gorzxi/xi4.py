import mpmath as mp, time
exec(open('xi3.py').read().split('t=time.time()')[0])
mp.mp.dps=25
def Lam(s): return mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
g = lambda z: (-1+4*z*z)*Lam(mp.mpf(1)/2+z)
r=mp.mpf('0.35'); N=40
vals=[g(r*mp.expjpi(2*mp.mpf(k)/N)) for k in range(N)]
def coef(m): return sum(vals[k]*mp.expjpi(-2*mp.mpf(k*m)/N) for k in range(N))/N/r**m
mp.mp.dps=50
print("n  direct-Taylor   integral-formula")
print(0, mp.nstr(coef(0).real,12), mp.nstr(4-2*F(0),12))
for n in (1,2,3,4):
    print(n, mp.nstr(coef(2*n).real*mp.factorial(n),12), mp.nstr(gamma_n(n),12), flush=True)
