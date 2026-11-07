import mpmath as mp
mp.mp.dps = 40
def theta0(t):
    s=mp.mpf(0); k=1
    while True:
        term=mp.e**(-mp.pi*k*k*t)
        s+=term
        if term < mp.mpf(10)**(-mp.mp.dps-5)*s: break
        k+=1
    return s
def F(s):
    # integral over t in (1,inf) of (log t)^s t^{-3/4} theta0(t); substitute t=exp(u)
    f=lambda u: mp.e**(s*mp.log(u) + u/4)*theta0(mp.e**u) if u>0 else mp.mpf(0)
    # saddle: s/u + 1/4 - pi e^u ~ 0
    u0 = mp.findroot(lambda u: s/u + mp.mpf(1)/4 - mp.pi*mp.e**u, mp.log(max(s,2))) if s>0 else 1
    pts=[0]+[u0*x for x in (0.25,0.5,0.75,0.9,1,1.1,1.25,1.5,2,3)]+[mp.inf]
    return mp.quad(f, pts)
def gamma_n(n):
    return mp.factorial(n)/mp.factorial(2*n)*(32*mp.binomial(2*n,2)*F(2*n-2)-F(2*n))/mp.mpf(2)**(2*n-1)
# direct Taylor check
def Lam(s): return mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
g = lambda z: (-1+4*z*z)*Lam(mp.mpf(1)/2+z)
mp.mp.dps=30
tay = mp.taylor(g, 0, 10)
for n in range(1,6):
    direct = tay[2*n]*mp.factorial(n)
    print(n, mp.nstr(direct,15), mp.nstr(gamma_n(n),15))
print("gamma0 direct", tay[0], " (formula n=0 not valid)")
mp.mp.dps=40
for n in (10,100):
    print(n, mp.nstr(gamma_n(n),12))
