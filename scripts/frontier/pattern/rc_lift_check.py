from fractions import Fraction as Fr
from sympy import bernoulli
import sys
def test(l,k,build):
    M=l*l; D=l*45
    def mul(a,b,mod=M):
        o=[0]*(D+1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b[:D+1-i]):
                    o[i+j]+=x*y
        return [x%mod for x in o]
    def sig(s):
        a=[0]*(D+1)
        for d in range(1,D+1):
            v=pow(d,s,M)
            for n in range(d,D+1,d): a[n]=(a[n]+v)%M
        return a
    w=l-1; B=bernoulli(w); c=Fr(-2*w)*Fr(int(B.q),int(B.p))
    cm=c.numerator*pow(c.denominator,-1,M)%M
    E=[1]+[cm*x%M for x in sig(w-1)[1:]]
    s3,s5,s1=sig(3),sig(5),sig(1)
    E4=[1]+[240*x%M for x in s3[1:]];E6=[1]+[-504*x%M for x in s5[1:]]
    E2=[1]+[-24*x%M for x in s1[1:]]
    Q=[1]+[0]*D
    # Delta via (E4^3-E6^2)/1728 over integers mod l^2 (1728 unit)
    e43=mul(mul(E4,E4),E4);e62=mul(E6,E6);inv=pow(1728,-1,M)
    Dl=[(a-b)*inv%M for a,b in zip(e43,e62)]
    g=build(Dl,E4,E6,mul)
    th=lambda a:[n*x%M for n,x in enumerate(a)]
    U=lambda a:[a[l*i] for i in range((len(a)-1)//l+1)]
    F=[(k*x-w*y)%M for x,y in zip(mul(g,th(E)),mul(E,th(g)))]
    UF=U(F); assert all(x%l==0 for x in UF), 'UF not 0 mod l'
    G=[x//l%l for x in UF]
    # RHS mod l, using series truncated at len(G)
    n=len(G)
    kinv=pow(k,-1,l)
    def trunc(a):return [x%l for x in a[:n]]
    Ug=U(g)
    def serre(a): # a of weight k, truncated list
        ee=mul(a+[0]*(D+1-len(a)),E2)
        return [ (i*a[i]-k*pow(12,-1,l)*ee[i])%l for i in range(len(a))]
    dUg=serre(trunc(Ug))
    dg=serre(trunc(g)+[x%l for x in g[n:]])
    Udg=[dg[l*i] for i in range(n)]
    thUg=[i*x%l for i,x in enumerate(trunc(Ug))]
    R=[(kinv*thUg[i]+(k-1)*kinv*(dUg[i]-Udg[i]))%l for i in range(n)]
    ok=sum(1 for i in range(n) if G[i]==R[i])
    print(f'l={l} k={k} terms={n} match={ok}', 'OK' if ok==n else [ (i,G[i],R[i]) for i in range(n) if G[i]!=R[i]][:5])
test(17,12,lambda D,E4,E6,m:D)
test(29,24,lambda D,E4,E6,m:m(D,m(m(E4,E4),E4)))
test(29,24,lambda D,E4,E6,m:m(D,D))
test(31,26,lambda D,E4,E6,m:m(D,m(D,[x*1 for x in m(E4,[1]+[0]*(len(D)-1))]))) if 0 else None
test(31,26,lambda D,E4,E6,m:m(m(D,D),[1]+[0]*(len(D)-1))) if 0 else None
