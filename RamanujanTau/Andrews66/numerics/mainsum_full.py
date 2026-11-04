import mpmath as mp, math
from fractions import Fraction as Fr
mp.mp.dps=60
NMAX=2000
a=[0]*(NMAX+1)
n=0
while n*n<=NMAX:
    t=[0]*(NMAX+1); t[n*n]=1
    for j in range(1,n+1):
        for _ in range(2):
            for i in range(j,NMAX+1): t[i]-=t[i-j]
    for i in range(NMAX+1): a[i]+=t[i]
    n+=1
def saw(x):
    return 0 if x.denominator==1 else x-math.floor(x)-Fr(1,2)
def s_ded(h,k): return sum(saw(Fr(i,k))*saw(Fr(h*i,k)) for i in range(1,k))
SD={}
def A_rad(k,n):
    tot=mp.mpc(0)
    for h in range(k):
        if math.gcd(h,k)!=1: continue
        if (h,k) not in SD: SD[(h,k)]=s_ded(h,k)
        tot+=mp.expjpi(mp.mpf(SD[(h,k)].numerator)/SD[(h,k)].denominator - mp.mpf(2*n*h)/k)
    return tot
def MK(K,n):
    s=mp.sqrt(24*n-1)
    return mp.sqrt(48)/(mp.sqrt(K)*s)*mp.sinh(mp.pi*s/(6*K))
rows=[]
for n in range(1,NMAX+1):
    N=math.isqrt(n)
    main=mp.mpf(0)
    for k in range(1,N+1):
        m=n-k*(1+(-1)**k)//4
        main+=(-1)**((k+1)//2)*A_rad(2*k,m).real*MK(2*k,n)
    err=abs(a[n]-main)
    rows.append((n,N,float(err)))
mx=max(r[2]/(r[1]*(1+math.log(r[1]))) for r in rows)
mxs=max(r[2]/math.sqrt(r[0]) for r in rows)
mxq=max(r[2]/r[0]**0.25 for r in rows)
print("max |alpha-main|/(N(1+log N)) =",mx,"; max err/sqrt(n) =",mxs,"; max err/n^(1/4) =",mxq)
for r in rows:
    if r[0] in (10,100,200,500,1000,1500,2000) or r[0]%250==0: print(r)
big=sorted(rows,key=lambda r:-r[2])[:5]; print("largest errors:",big)
