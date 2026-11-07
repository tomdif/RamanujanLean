# q-series test at level 1: T[g,E^s]_j = l^j u [Tg,E^s]_j + sum_{i<j} [H_i,E^s]_i  mod l^{j+1}, H_i in M_{w-2i-s(l-1)}(1).
import sys,sympy
from fractions import Fraction
from math import comb
from flint import nmod_poly
def dimM(k):
    if k<0 or k%2 or k==2:return 0
    return k//12+(0 if k%12==2 else 1)
class R:
    def __init__(S,p,e,L):
        S.p,S.e,S.m,S.L=p,e,p**e,L
    def P(S,c):return nmod_poly([int(x)%S.m for x in c[:S.L]],S.m)
    def tr(S,f):return nmod_poly(f.coeffs()[:S.L],S.m)
    def mul(S,a,b):return S.tr(a*b)
    def eis(S,k):
        B=sympy.bernoulli(k);c=Fraction(-2*k)/Fraction(B.p,B.q)
        c=c.numerator*pow(c.denominator,-1,S.m)%S.m
        sg=[0]*S.L
        for d in range(1,S.L):
            dk=pow(d,k-1,S.m)
            for n in range(d,S.L,d):sg[n]+=dk
        return S.P([1]+[c*(sg[n]%S.m)%S.m for n in range(1,S.L)])
    def pw(S,f,n):
        r=S.P([1]);b=f
        while n:
            if n&1:r=S.mul(r,b)
            b=S.mul(b,b);n>>=1
        return r
    def th(S,f,r=1):
        c=f.coeffs();return S.P([pow(i,r,S.m)*int(x)%S.m for i,x in enumerate(c)])
    def U(S,f):
        c=f.coeffs();p=S.p
        return S.P([int(c[p*n]) if p*n<len(c) else 0 for n in range(len(c)//p+1)])
def cbin(a,n):
    x=Fraction(1)
    for i in range(n):x*=Fraction(a-i,i+1)
    return x
def fr(x,m):return x.numerator*pow(x.denominator,-1,m)%m
def solve(v,gens,p,e):
    "is v in the Z/p^e span of gens? (vectors as lists)"
    m=p**e;v=v[:];G=[g[:] for g in gens];n=len(v)
    def val(x):
        x%=m
        if x==0:return e
        t=0
        while x%p==0:x//=p;t+=1
        return t
    used=[False]*len(G)
    while True:
        best=None
        for a,g in enumerate(G):
            if used[a]:continue
            for c in range(n):
                t=val(g[c])
                if t<e and (best is None or t<best[0]):best=(t,a,c)
        if best is None:break
        t,a,c=best;used[a]=True;g=G[a]
        unit=pow(g[c]//p**t,-1,m)
        for b,h in enumerate(G):
            if b!=a and not used[b] and h[c]%m:
                f=(h[c]//p**t)*unit%m
                G[b]=[(x-f*y)%m for x,y in zip(h,g)]
        if v[c]%m:
            if val(v[c])<t:return False
            f=(v[c]%m//p**t)*unit%m
            v=[(x-f*y)%m for x,y in zip(v,g)]
    return all(x%m==0 for x in v)
def run(p,s,j,k):
    e=j+1;l=s*(p-1);w=k+l+2*j
    D=dimM(w)+6;K=max(dimM(k),1);L=p*(D+K+4)
    A=R(p,e,L)
    # eta-free Delta
    E4=A.eis(4);E6=A.eis(6)
    E43=A.pw(E4,3);E62=A.mul(E6,E6);c=pow(1728,-1,A.m)
    Dl=(E43-E62)*c;Dl=A.tr(Dl)
    W=A.pw(A.eis(p-1),s)
    def basis(kk):
        out=[]
        for a in range(dimM(kk)):
            r=kk-12*a
            for cc in range(3):
                if r-6*cc>=0 and (r-6*cc)%4==0:b=(r-6*cc)//4;break
            out.append(A.mul(A.mul(A.pw(Dl,a),A.pw(E4,b)),A.pw(E6,cc)))
        return out
    def br(g,kk,i):
        ll=l;t=A.P([0])
        for r in range(i+1):
            co=(-1)**r*cbin(kk+i-1,i-r)*cbin(ll+i-1,r)
            t=t+A.mul(A.th(g,r),A.th(W,i-r))*fr(co,A.m)
        return A.tr(t)
    def vec(f,n=D):
        c=f.coeffs();return [(int(c[i]) if i<len(c) else 0) for i in range(n)]
    B=basis(k)
    res=[]
    u=fr(cbin(s,j)/cbin(k+j-1,j),A.m) if cbin(k+j-1,j).numerator%p else None
    for g in B:
        h=A.U(g)   # T g mod l^{k-1}
        F=br(g,k,j)
        TF=vec(A.U(F))
        # H_i ranges over M_{k_i}, k_i=k+2(j-i), i<j ; each generator [H,W]_i
        gens=[]
        for i in range(j):
            ki=k+2*(j-i)
            for H in basis(ki):gens.append(vec(br(H,ki,i)))
        # [Tg,W]_j : express h via level-1 basis of M_k on low coefficients, to carry full length
        hv=vec(h,len(B)+2)
        # basis in echelon: solve triangular by leading q-order
        Tg=A.P([0]);hh=h
        for t,b in enumerate(B):
            ct=int(hh[t]) if t<hh.length() else 0
            Tg=Tg+b*ct
            hh=hh-A.tr(b)*ct
        Tg=A.tr(Tg)
        top=vec(br(Tg,k,j))
        pj=p**j
        target=[(x-pj*u*y)%A.m for x,y in zip(TF,top)]
        ok=solve(target,gens,p,e)
        badu=(u+1)%A.m
        tb=[(x-pj*badu*y)%A.m for x,y in zip(TF,top)]
        bad=solve(tb,gens,p,e)
        nz=any(y%p for y in top)
        res.append((ok,bad,nz))
    return res
if __name__=='__main__':
    p=int(sys.argv[1])
    for s in map(int,sys.argv[2].split(',')):
      for j in map(int,sys.argv[3].split(',')):
        for k in map(int,sys.argv[4].split(',')):
            if s<j: continue
            print(f'p={p} s={s} j={j} k={k}',run(p,s,j,k),flush=True)
