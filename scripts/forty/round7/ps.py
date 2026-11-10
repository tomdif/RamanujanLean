# integer power series toolkit, truncated at N
N=120
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i):
                if b[j]: c[i+j]+=x*b[j]
    return c
def add(*xs): return [sum(t) for t in zip(*xs)]
def neg(a): return [-x for x in a]
def scal(k,a): return [k*x for x in a]
def mono(e,c=1):
    a=[0]*N
    if 0<=e<N: a[e]=c
    return a
ONE=mono(0)
def inv(a):
    assert a[0] in (1,-1)
    b=[0]*N; b[0]=a[0]
    for n in range(1,N):
        s=sum(a[k]*b[n-k] for k in range(1,n+1)); b[n]=-s*a[0]
    return b
def div(a,b): return mul(a,inv(b))
def sub_q(a,k,sign=1):
    b=[0]*N
    for i,x in enumerate(a):
        if i*k<N: b[i*k]=x*(sign**i)
    return b
def P(r,m,sign=1):
    res=ONE; j=r
    while j<N:
        res=mul(res,add(ONE,mono(j,-sign))); j+=m
    return res
def fneg(k): return P(k,k)
def chi(k,sign=1): return P(k,2*k,-sign)
def phi(k,sign=1):
    a=[0]*N; n=0
    while k*n*n<N:
        a[k*n*n]+=(1 if n==0 else 2)*(sign**n); n+=1
    return a
def psi(k,sign=1):
    a=[0]*N; n=0
    while k*n*(n+1)//2<N:
        a[k*n*(n+1)//2]+=sign**(n*(n+1)//2); n+=1
    return a
def fab(a,b,sa=1,sb=1):
    # Ramanujan f(sa q^a, sb q^b) = sum_n (sa q^a)^{n(n+1)/2} (sb q^b)^{n(n-1)/2}
    r=[0]*N
    for n in range(-60,61):
        E=a*n*(n+1)//2+b*n*(n-1)//2
        if 0<=E<N: r[E]+=sa**((n*(n+1)//2)%2)*sb**((n*(n-1)//2)%2)
    return r
def qpoch_fin(n):
    r=ONE
    for k in range(1,n+1): r=mul(r,add(ONE,mono(k,-1)))
    return r
def rr(shift):
    s=[0]*N; n=0
    while n*n+shift*n<N:
        s=add(s,mul(mono(n*n+shift*n),inv(qpoch_fin(n)))); n+=1
    return s
import functools
@functools.lru_cache(None)
def _G(): return tuple(P(1,5)) 
G1=inv(mul(P(1,5),P(4,5))); H1=inv(mul(P(2,5),P(3,5)))
def G(k,s=1): return sub_q(G1,k,s)
def H(k,s=1): return sub_q(H1,k,s)
def eq(a,b,M=N): return all(x==y for x,y in zip(a[:M],b[:M]))
def firstdiff(a,b):
    for i in range(N):
        if a[i]!=b[i]: return i,a[i],b[i]
    return None
