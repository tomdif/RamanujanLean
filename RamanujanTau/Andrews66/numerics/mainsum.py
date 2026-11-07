import numpy as np, math, cmath
NMAX=2000
# exact alpha(n)
a=[0]*(NMAX+1)
n=0
while n*n<=NMAX:
    t=[0]*(NMAX+1); t[n*n]=1
    for j in range(1,n+1):
        for _ in range(2):
            for i in range(j,NMAX+1): t[i]-=t[i-j]
    for i in range(NMAX+1): a[i]+=t[i]
    n+=1
def poch(q,M=4000):
    P=1+0j; qm=q
    for m in range(M):
        P*=(1-qm); qm*=q
        if abs(qm)<1e-18: break
    return P
def b(q): return poch(q)**3/poch(q*q)**2
def qp(h,K,z): return cmath.exp(2j*math.pi*(h+1j*z)/K)
def inv(h,K):
    for x in range(K):
        if (h*x+1)%K==0: return x
om={}
def omegaB(h,k):
    K=2*k
    if (h,k) not in om:
        z=1.0
        om[(h,k)] = b(qp(h,K,z))*cmath.sqrt(z)*cmath.exp(-math.pi*(1/z-z)/(24*k))/b(qp(inv(h,K),K,1/z))
    return om[(h,k)]
def Ab(k,n):
    K=2*k
    return sum(omegaB(h,k)*cmath.exp(-2j*math.pi*n*h/K) for h in range(K) if math.gcd(h,K)==1)
def MK(K,n):
    s=math.sqrt(24*n-1)
    return math.sqrt(48)/(math.sqrt(K)*s)*math.sinh(math.pi*s/(6*K))
# Dedekind sum / Rademacher A_k
def s_ded(h,k):
    return sum(((i/k - math.floor(i/k)-0.5) if i%k else 0)*((h*i/k-math.floor(h*i/k)-0.5) if (h*i)%k else 0) for i in range(1,k))
def A_rad(k,n):
    return sum(cmath.exp(1j*math.pi*s_ded(h,k))*cmath.exp(-2j*math.pi*n*h/k) for h in range(k) if math.gcd(h,k)==1)
# 1. check |omegaB|=1 and identification
maxdev=0; maxnorm=0
for k in range(1,23):
    for n in range(0,60):
        lhs=(-1)**k*Ab(k,n)
        m = n - k*(1+(-1)**k)//4
        rhs=(-1)**((k+1)//2)*A_rad(2*k,m)
        maxdev=max(maxdev,abs(lhs-rhs))
for (h,k),w in om.items(): maxnorm=max(maxnorm,abs(abs(w)-1))
print("max ||omega_b|-1| =",maxnorm,"  max |(-1)^k Ab(k,n) - Andrews sign*A_2k(shifted)| over k<=22,n<60 =",maxdev)
# 2. main sum vs alpha
print(" n   N   alpha(n)        main(n)          err      err/(N log N)  err/sqrt(n)")
worst=0
for n in list(range(1,30))+list(range(30,NMAX+1,97))+[NMAX]:
    N=math.isqrt(n)
    main=sum(((-1)**k*Ab(k,n)*MK(2*k,n)) for k in range(1,N//2+1))
    err=a[n]-main
    worst=max(worst,abs(err)/(N*(1+math.log(N))))
    if n%97==30 or n<8 or n==NMAX: print("%4d %3d %16d %18.4f %10.4f %8.4f %8.4f"%(n,N,a[n],main.real,abs(err),abs(err)/(N*(1+math.log(N))),abs(err)/math.sqrt(n)), "imag=%.1e"%main.imag)
allw=max(abs(a[n]-sum(((-1)**k*Ab(k,n)*MK(2*k,n)) for k in range(1,math.isqrt(n)//2+1)))/(math.isqrt(n)*(1+math.log(math.isqrt(n)))) for n in range(1,NMAX+1))
print("max over all n<=2000 of |alpha-main|/(N(1+log N)) =",allw)
