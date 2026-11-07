# Direct test of the route to G4 (BL_SHARPNESS_PROOF section 4.11).
# ubar in Kbar, g=ubar/eta, A[m]=a(24m-1). wbar = (U_{l^2} gtilde)/l - U_{l^2}(e1 gtilde) mod l.
# Sh_t = explicit lift (d/t) d^(lam-1) chi12(e) a(t e^2), lam=l-2, level 6, weight 2l-4.
# Claims: Sh_t(gbar) = theta z with z in Mbar_{l-5}(6); Sh_t(wbar) = c*theta(Ubar z) mod Mbar_{l-3}(6), c = eps*(1/5).
import sys,sympy
from fractions import Fraction
from flint import nmod_poly,nmod_mat
p=int(sys.argv[1]);tlist=[int(x) for x in sys.argv[2].split(',')] if len(sys.argv)>2 else [23,47,71]
PRm=p**3;tmax=max(tlist);nmax=2*p+8
Mw=(tmax*nmax*nmax+1)//24+2;L=p*p*(24*Mw)//24+p*p+10
print('series length',L,flush=True)
P=lambda c,m=PRm:nmod_poly(c,m)
tr=lambda f,n=L,m=PRm:nmod_poly(f.coeffs()[:n],m)
def euler(d,n=L,m=PRm):
    c=[0]*n;k=0
    while True:
        g1=k*(3*k-1)//2*d;g2=k*(3*k+1)//2*d
        if g1>=n:break
        s=1 if k%2==0 else m-1
        c[g1]=s
        if k and g2<n:c[g2]=s
        k+=1
    return nmod_poly(c,m)
def inv(f,n=L,m=PRm):
    g=nmod_poly([pow(int(f[0]),-1,m)],m);k=1
    while k<n:
        k=min(2*k,n);g=tr(g*(nmod_poly([2],m)-tr(f*g,k,m)),k,m)
    return g
def pw(f,e,n=L,m=PRm):
    r=nmod_poly([1],m);b=f
    while e:
        if e&1:r=tr(r*b,n,m)
        b=tr(b*b,n,m);e>>=1
    return r
def eis(k,n=L,m=PRm):
    B=sympy.bernoulli(k);c=Fraction(-2*k)/Fraction(B.p,B.q);den=c.denominator
    assert den%p
    c=c.numerator*pow(den,-1,m)%m
    # sigma via sieve
    import numpy as np
    s=np.zeros(n,dtype=np.uint64)
    for d in range(1,n):
        s[d::d]=(s[d::d]+pow(d,k-1,m))%m
    return nmod_poly([1]+[int(c*int(x)%m) for x in s[1:]],m)
sb=p*(nmax+6)
# level 1 cusp forms S_{p-1}: E4,E6,Delta
E4=eis(4,sb);E6=eis(6,sb);Dl=tr(pw(euler(1,sb),24,sb)*nmod_poly([0,1],PRm),sb)
k1=p-1;d=k1//12+(0 if k1%12==2 else 1)-1
bas=[]
for x in range(1,d+1):
    r=k1-12*x
    for c in range(3):
        if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
    bas.append(tr(tr(pw(Dl,x,sb)*pw(E4,b,sb),sb)*pw(E6,c,sb),sb))
Pinv=inv(euler(1,sb),sb)
# Kbar: combos with A[m]=0 mod p whenever p | 24m-1
ms=[m for m in range(1,sb) if (24*m-1)%p==0][:d+12]
Ab=[tr(b*Pinv,sb) for b in bas]
Mt=[[int(a[m])%p if m<a.length() else 0 for m in ms] for a in Ab]
M=nmod_mat(len(ms),d,[Mt[j][i] for i in range(len(ms)) for j in range(d)],p)
X,nul=M.nullspace();Kb=[[int(X[i,j]) for i in range(d)] for j in range(nul)]
print('d',d,'dim Kbar',len(Kb),flush=True)
# Full length pieces
Pfull=inv(euler(1));E=eis(p-1)
e1=nmod_poly([0]+[(int(E[i])//p) for i in range(1,E.length())],PRm)
fullbas=[]
for x in range(1,d+1):
    r=k1-12*x
    for c in range(3):
        if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
    pass
# level 1 basis to length L
print('building level-1 forms',flush=True)
E4L=eis(4);E6L=eis(6);DlL=tr(pw(euler(1),24)*nmod_poly([0,1],PRm))
for x in range(1,d+1):
    r=k1-12*x
    for c in range(3):
        if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
    fullbas.append(tr(tr(pw(DlL,x)*pw(E4L,b))*pw(E6L,c)))
# level 6 mod p
def lvl6(LQ):
    def e(dd,r):
        f=euler(dd,LQ,p)
        return pw(f,r,LQ,p) if r>=0 else pw(inv(f,LQ,p),-r,LQ,p)
    def prod(rs):
        o=nmod_poly([1],p)
        for dd,r in rs:o=tr(o*e(dd,r),LQ,p)
        return o
    G=prod([(1,12),(2,-6),(3,-4),(6,2)]);Hs=prod([(1,-5),(2,1),(3,-1),(6,5)])
    H=nmod_poly([0]+[int(x) for x in Hs.coeffs()][:LQ-1],p)
    return G,H
LQ=p*(nmax+2);G6,H6=lvl6(LQ)
def M6(kk):
    Gm=pw(G6,kk//2,LQ,p);o=[];c=Gm
    for i in range(kk+1):
        o.append(c);c=tr(c*H6,LQ,p)
    return o
vec=lambda f,n:[int(f[i]) if i<f.length() else 0 for i in range(n)]
def echelon(rows):
    R=[];Pv=[]
    for v in rows:
        v=v[:]
        for r,c in zip(R,Pv):
            if v[c]:
                f=v[c];v=[(a-f*b)%p for a,b in zip(v,r)]
        c=next((i for i,x in enumerate(v) if x),None)
        if c is None:continue
        iv=pow(v[c],-1,p);v=[x*iv%p for x in v]
        for i in range(len(R)):
            if R[i][c]:
                f=R[i][c];R[i]=[(a-f*b)%p for a,b in zip(R[i],v)]
        R.append(v);Pv.append(c)
    return R,Pv
def reduce_(v,E_):
    v=v[:]
    for r,c in zip(*E_):
        if v[c]:
            f=v[c];v=[(a-f*b)%p for a,b in zip(v,r)]
    return v
def solve_in(v,gens):
    "coordinates of v in span gens, or None"
    n=len(gens);rows=[g+[1 if i==t else 0 for t in range(n)] for i,g in enumerate(gens)]
    N=len(v);R=[];Pv=[]
    for r in rows:
        r=r[:]
        for x,c in zip(R,Pv):
            if r[c]:
                f=r[c];r=[(a-f*b)%p for a,b in zip(r,x)]
        c=next((i for i,x in enumerate(r[:N]) if x),None)
        if c is None:continue
        iv=pow(r[c],-1,p);r=[x*iv%p for x in r]
        R.append(r);Pv.append(c)
    w=v+[0]*n
    for x,c in zip(R,Pv):
        if w[c]:
            f=w[c];w=[(a-f*b)%p for a,b in zip(w,x)]
    if any(w[:N]):return None
    return [(-x)%p for x in w[N:]]
lam=p-2
def jac(a,t):return int(sympy.jacobi_symbol(a,t))
chi=lambda e:1 if e%12 in(1,11) else (-1 if e%12 in(5,7) else 0)
def Sh(a,t,N):
    o=[0]*N
    for e in range(1,N):
        c=chi(e)
        if not c:continue
        m=(t*e*e+1)//24
        if m>=len(a):break
        x=a[m]*c%p
        if not x:continue
        for dd in range(1,(N-1)//e+1):
            pd=0 if dd%p==0 else jac(dd,t)*pow(dd,lam-1,p)%p
            o[dd*e]=(o[dd*e]+pd*x)%p
    return o
N=nmax
bk=[vec(f,LQ) for f in M6(p-5)]
thbk=[[i*x%p for i,x in enumerate(b[:N])] for b in bk]
low=[vec(f,N) for f in M6(p-3)]
Elow=echelon(low)
theta=lambda v:[i*x%p for i,x in enumerate(v)]
eps=1 if p%12 in(1,11) else -1
for kv in Kb:
    ut=nmod_poly([0],PRm)
    for x,f in zip(kv,fullbas):
        if x:ut=ut+f*x
    Af=tr(ut*Pfull)
    eAf=tr(e1*Af)
    def mp(m):return (p*p*(24*m-1)+1)//24
    aw=[0]*(Mw+1);ag=[0]*(Mw+1)
    bad=0
    for m in range(1,Mw+1):
        mm=mp(m)
        if mm>=L:Mtop=m;break
        y=int(Af[mm])
        if y%p:bad+=1
        aw[m]=((y//p)-int(eAf[mm]))%p
        ag[m]=int(Af[m])%p
    print('U_{l^2} g not divisible count',bad,flush=True)
    for t in tlist:
        f=Sh(ag,t,N);w=Sh(aw,t,N)
        zc=solve_in(f,thbk)
        print(' t',t,'f nonzero',any(f),'f in theta M_{l-5}',zc is not None,flush=True)
        if zc is None or not any(f):continue
        z=[0]*LQ
        for x,b in zip(zc,bk):
            if x:z=[(u+x*v)%p for u,v in zip(z,b)]
        Uz=[z[p*i] for i in range(LQ//p)][:N]
        tUz=theta(Uz)
        rw=reduce_(w,Elow);rt=reduce_(tUz,Elow)
        print('  Ubar z nonzero',any(Uz),'theta Uz mod M_{l-3} nonzero',any(rt),'Sh(w) mod M_{l-3} nonzero',any(rw))
        cs=[c for c in range(p) if all((a-c*b)%p==0 for a,b in zip(rw,rt))]
        if cs:
            c=cs[0];print('  c =',c,' c*5 =',c*5%p,' expected eps*1/5 =',eps*pow(5,-1,p)%p,' (-1/k)=',(-pow(p-5,-1,p))%p,'eps',eps,flush=True)
        else:print('  NO constant c',flush=True)
