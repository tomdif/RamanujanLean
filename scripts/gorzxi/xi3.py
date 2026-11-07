import mpmath as mp, sys, time
mp.mp.dps = 50
def theta0(t):
    s=mp.mpf(0); k=1
    while True:
        term=mp.exp(-mp.pi*k*k*t); s+=term
        if term < mp.mpf(10)**(-mp.mp.dps-5)*s: break
        k+=1
    return s
def logF_integrand(s):
    # F(s)=int_0^inf u^s e^{u/4} theta0(e^u) du  (t=e^u)
    return lambda u: mp.exp(s*mp.log(u) + u/4)*theta0(mp.exp(u)) if u>0 else mp.mpf(0)
def F(s):
    s=mp.mpf(s)
    if s==0:
        return mp.quad(logF_integrand(s),[0,0.5,1,2,3,4,5])
    u0 = mp.findroot(lambda u: s/u + mp.mpf(1)/4 - mp.pi*mp.exp(u), mp.log(s+2))
    sig = 1/mp.sqrt(s/u0**2 + mp.pi*mp.exp(u0))
    pts=[max(mp.mpf(0),u0-40*sig)]+[u0+k*sig for k in range(-30,31,3) if u0+k*sig>0]+[u0+60*sig]
    pts=sorted(set(pts))
    f=logF_integrand(s)
    val=mp.quad(f, pts)
    # tails check (crude): add [0,pts0] and [last,inf]
    if pts[0]>0: val+=mp.quad(f,[0,pts[0]])
    return val
def B(n): return 32*mp.binomial(2*n,2)*F(2*n-2)-F(2*n)
def gamma_n(n):
    return mp.factorial(n)/mp.factorial(2*n)*B(n)/mp.mpf(2)**(2*n-1)
t=time.time()
for n in (1,2,3,10,100):
    print(n, mp.nstr(gamma_n(n),15), time.time()-t, flush=True)
