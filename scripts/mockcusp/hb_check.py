# Numerical check of Andrews66.Hb: |f(q) - eps_K b(q)| <= C |z|^{-D}, q = e^{2 pi i (h + i z)/K}, Re(1/z) >= K/2.
import mpmath as mp, math, sys
mp.mp.dps=40
def eta_prod(q):   # (q;q)_inf via pentagonal series
    s=mp.mpf(0); n=0
    lq=-mp.log(abs(q))
    nmax=int(mp.sqrt(2*120/(3*lq)))+3
    s=mp.mpc(1)
    for n in range(1,nmax):
        s+=(-1)**n*(q**(n*(3*n-1)//2)+q**(n*(3*n+1)//2))
    return s
def ALf(q):  # 2 sum_Z (-1)^n q^{n(3n+1)/2}/(1+q^n)
    lq=-mp.log(abs(q)); nmax=int(mp.sqrt(2*120/(3*lq)))+3
    s=mp.mpc(1)
    for n in range(1,nmax):
        s+=4*(-1)**n*q**(n*(3*n+1)//2)/(1+q**n)
    return s
def fval(q): return ALf(q)/eta_prod(q)
def bval(q): return eta_prod(q)**3/eta_prod(q*q)**2
def series_f(q,M=200):
    s=0; d=1
    for n in range(M):
        if n>0: d*= (1+q**n)
        s+=q**(n*n)/d**2
    return s
# sanity
q0=mp.mpf('0.7')*mp.exp(1j*0.9)
print("sanity f:", fval(q0), series_f(q0))
def eps(K): return (-1)**(K//2) if K%2==0 else 0
res={}
for K in range(1,13):
    for h in range(K if K>1 else 1):
        if math.gcd(h,K)!=1: continue
        worst=[0,0,0]
        for sig in [0,0.5,2,8,30]:
            for tau in [0,1,-1,3,-3,10,-10,30,-30]:
                w=mp.mpc(K/2*(1+sig),tau*K)
                z=1/w
                q=mp.exp(2j*mp.pi*(h+1j*z)/K)
                v=abs(fval(q)-eps(K)*bval(q))
                for i,D in enumerate([0,0.5,1]):
                    worst[i]=max(worst[i],float(v/abs(w)**D))
        res[(h,K)]=worst
        print(K,h,["%.3g"%x for x in worst]); sys.stdout.flush()
