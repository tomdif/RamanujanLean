# exact integer test of the Lean T_{ell^2} formula on eta^r M_s, vs PARI newform coefficient
import sys, subprocess
from math import isqrt
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def run(l):
    j=l%24; kp=(l+j-2)//2; lam=(l-3)//2; delta=(l*l-1)//24
    R=(kp//12) if (kp%12!=2) else (kp//12-1)
    N=l*l*(R+2)+50
    # series to N
    def mul(a,b):
        import numpy as np
        return None
    from functools import reduce
    # use python big-int via Kronecker-free simple recurrences: power of eta product through Euler recurrence
    def qpow(e):  # prod (1-q^n)^e coefficients, recurrence n a_n = -e sum sigma(k) a_{n-k}
        sig=[0]*(N+1)
        for d in range(1,N+1):
            for m in range(d,N+1,d): sig[m]+=d
        a=[0]*(N+1); a[0]=1
        return a,sig
    # only need E4,E6,Delta products: represent via numpy object? use flint if present
    from flint import fmpz_poly
    def trunc(p): return fmpz_poly(p.coeffs()[:N+1])
    sig3=[0]*(N+1); sig5=[0]*(N+1)
    for d in range(1,N+1):
        d3=d**3; d5=d**5
        for m in range(d,N+1,d): sig3[m]+=d3; sig5[m]+=d5
    E4=fmpz_poly([1]+[240*sig3[m] for m in range(1,N+1)])
    E6=fmpz_poly([1]+[-504*sig5[m] for m in range(1,N+1)])
    # (q;q)_inf by pentagonal
    Q=[0]*(N+1)
    k=0
    while True:
        g1=k*(3*k-1)//2; g2=k*(3*k+1)//2
        if g1>N: break
        s=-1 if k%2 else 1
        Q[g1]=s
        if g2<=N: Q[g2]=s
        k+=1
    Q=fmpz_poly(Q)
    def ppow(p,e):
        r=fmpz_poly([1]);b=p
        while e:
            if e&1: r=trunc(r*b)
            b=trunc(b*b); e>>=1
        return r
    Dz=trunc(fmpz_poly([0,1])*ppow(Q,24))
    # P = 1/Q
    def inv(p):
        c=p.coeffs(); b=[0]*(N+1); b[0]=1
        # P recursively via pentagonal
        terms=[(i,c[i]) for i in range(1,len(c)) if c[i]!=0]
        for n in range(1,N+1):
            s=0
            for i,ci in terms:
                if i>n: break
                s-=int(ci)*b[n-i]
            b[n]=s
        return fmpz_poly(b)
    P=inv(Q); Pj=ppow(P,j)
    # integer basis Delta^i E4^a E6^b
    basis=[]
    for i in range(1,R+1):
        w=kp-12*i
        for b in range(0,w//6+1):
            if (w-6*b)%4==0:
                a=(w-6*b)//4; break
        G=trunc(trunc(ppow(Dz,i)*ppow(E4,a))*ppow(E6,b))
        basis.append(trunc(G*Pj))
    def co(A,i):
        return int(A[i]) if 0<=i<=N else None
    eps=leg(3,l)
    def Tc(A,m):
        n=24*m-j
        t=co(A,l*l*m-j*delta if l*l*m>=j*delta else 0)
        mid=eps*leg(((-1)**lam)*n,l)*l**(lam-1)*co(A,m)
        last=0
        if n%(l*l)==0:
            last=l**(2*lam-1)*co(A,((n//(l*l))+j)//24)
        return t+mid+last
    M=R+1
    # matrix of T in the triangular coordinate: leading coefficient of A[i] at m=i (A_i = q^i+...)
    import sympy as sp
    rows=[]
    for A in basis:
        rows.append([Tc(A,m) for m in range(1,M+1)])
    base=[[int(A[m]) for m in range(1,M+1)] for A in basis]
    Bm=sp.Matrix([r[:R] for r in base]); Tm=sp.Matrix([r[:R] for r in rows])
    Mat=Tm*Bm.inv()
    if not all(x.is_integer for x in Mat): print("nonintegral",l)
    # verify stable: predicted coefficient at further m
    ok=True
    for idx,A in enumerate(basis):
        for m in range(R+1,R+1+20):
            if l*l*m> N: break
            pred=sum(Mat[idx,c]*int(basis[c][m]) for c in range(R))
            if Tc(A,m)!=pred: ok=False
    x=sp.symbols('x')
    return ok,R,sp.factor(Mat.charpoly(x).as_expr()),eps
for l in [13,17,19,23,29,31,37,41]:
    ok,R,cp,eps=run(l)
    print(l,"stable",ok,"R",R,"eps",eps,"charpoly",cp,flush=True)
