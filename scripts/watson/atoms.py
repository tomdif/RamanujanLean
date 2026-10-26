from fractions import Fraction
import os
MOD=int(os.environ.get("MOD","40"))
def c2(m): return m*(m-1)//2
def add(v,r,n):
    r=r%MOD or MOD; v[r]=v.get(r,0)+n
def poch(v,r,step,cc,n):
    if cc==1:
        for j in range(MOD//step): add(v,r+step*j,n)
    else:
        poch(v,2*r,2*step,1,n); poch(v,r,step,1,-n)
def th(N,e,c):
    """j(c q^e; q^N) as (coef,k,vec); None if zero; requires MOD%N==0 and (c==-1 -> MOD%(2N)==0)"""
    if MOD%N or (c==-1 and MOD%(2*N)): raise ValueError
    e0=e%N; m=(e-e0)//N
    sign=(-1)**(m%2)*(1 if c==1 else (-1)**(m%2)); k=-N*c2(m)-e0*m
    v={}; coef=1
    if e0==0:
        if c==1: return None
        coef=2; poch(v,N,N,-1,2); poch(v,N,N,1,1)
    else:
        poch(v,e0,N,c,1); poch(v,N-e0,N,c,1); poch(v,N,N,1,1)
    return (sign*coef,k,{r:n for r,n in v.items() if n})
def mul(*ts):
    s=Fraction(1);k=0;v={}
    for t in ts:
        if t is None: return None
        a,b,c=t; s*=a;k+=b
        for r,n in c.items(): v[r]=v.get(r,0)+n
    return (s,k,{r:n for r,n in v.items() if n})
def inv(t): a,b,c=t; return (1/Fraction(a),-b,{r:-n for r,n in c.items()})
def fromexp(e,period,lead=0,c=1):
    v={}
    for r in range(1,MOD+1):
        n=e[(r-1)%period]
        if n: v[r]=n
    return (Fraction(c),lead,v)
def sub2(t):  # f(q) -> f(q^2): (q^r;q^MOD) -> (q^{2r};q^{2MOD}) = (q^{2r};q^MOD)(q^{2r+MOD};q^MOD)
    a,k,v=t; w={}
    for r,n in v.items():
        add(w,2*r,n); add(w,2*r+MOD,n)
    return (a,2*k,{r:n for r,n in w.items() if n})
def key(t): return (t[1],tuple(sorted(t[2].items())))
