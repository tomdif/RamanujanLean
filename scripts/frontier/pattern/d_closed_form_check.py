# test: mod l^2, D(F)=U(Phi F) == A^{-1} U(Delta^delta F), A=(q;q)^l/(q^l;q^l), and A^2 == E_{l-1} mod l^2
from fractions import Fraction as Fr
from sympy import bernoulli
def run(l):
    M=l*l;D=l*l+60*l
    def mul(a,b):
        o=[0]*(D+1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b[:D+1-i]):
                    o[i+j]+=x*y
        return [x%M for x in o]
    def pw(a,e):
        r=[1]+[0]*D
        while e:
            if e&1:r=mul(r,a)
            a=mul(a,a);e>>=1
        return r
    def inv(a):
        o=[0]*(D+1);o[0]=1
        for n in range(1,D+1):
            o[n]=(-sum(a[i]*o[n-i] for i in range(1,n+1) if a[i]))%M
        return o
    Q=[0]*(D+1);Q[0]=1;m=1
    while m*(3*m-1)//2<=D:
        s=(-1)**m
        for g in (m*(3*m-1)//2,m*(3*m+1)//2):
            if g<=D:Q[g]=s%M
        m+=1
    V=lambda a,k:[(a[i//k] if i%k==0 else 0) for i in range(D+1)]
    A=mul(pw(Q,l),inv(V(Q,l)))
    w=l-1;B=bernoulli(w);c=Fr(-2*w)*Fr(int(B.q),int(B.p));cm=c.numerator*pow(c.denominator,-1,M)%M
    E=[1]+[cm*sum(pow(d,w-1,M) for d in range(1,n+1) if n%d==0)%M for n in range(1,D+1)]
    print(l,'A^2==E mod l^2:',mul(A,A)==E)
    d=(l*l-1)//24
    Dd=([0]*d+pw(Q,24*d))[:D+1]
    Phi=([0]*d+mul(V(Q,l*l),inv(Q)))[:D+1]
    F=[(k*k+1)%M for k in range(D+1)]  # arbitrary test series
    U=lambda a:[a[l*i] for i in range((len(a)-1)//l+1)]
    lhs=U(mul(Phi,F));r=U(mul(Dd,F))
    n=len(lhs);Ai=inv(A)
    rhs=[sum(Ai[i]*r[j-i] for i in range(j+1))%M for j in range(n)]
    print(l,'D closed form on',n,'coeffs:',lhs==rhs)
for l in (13,17,29):run(l)
