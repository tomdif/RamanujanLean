import sys, random
src=open('digits.py').read().split("for b in (1,2,3):")[0]
exec(src)
random.seed(1)
NC=60                       # coefficients wanted in output
LL=NC*l+10
def Eser2(Lm):
    E=[0]*Lm
    for k in range(-3000,3001):
        e=k*(3*k-1)//2
        if 0<=e<Lm: E[e]+=(1 if k%2==0 else -1)
    return E
# Phi = q^delta E(q^{l^2})/E(q)
delta=(l*l-1)//24
E1=Eser2(LL); 
inv=[0]*LL; inv[0]=1
for m in range(1,LL):
    s=0
    for j in range(1,m+1):
        if E1[j]: s+=E1[j]*inv[m-j]
    inv[m]=(-s)%mod
El2=[0]*LL
for i in range(0,LL, l*l): El2[i]=E1[i//(l*l)]%mod
Phi=[0]*LL
t=mul(El2,inv,mod,LL)
for i in range(LL-delta): Phi[i+delta]=t[i]
def forms(w,Lm):
    # basis of M_w (E4^a E6^b) to length Lm
    E4=[1]+[240*sigma(n,3) for n in range(1,Lm)]; E6=[1]+[-504*sigma(n,5) for n in range(1,Lm)]
    out=[]
    for a in range(w//4+1):
        r=w-4*a
        if r%6: continue
        f=[1]+[0]*(Lm-1)
        for _ in range(a): f=mul(f,E4,mod,Lm)
        for _ in range(r//6): f=mul(f,E6,mod,Lm)
        out.append(f)
    return out
def randform(w,Lm):
    B=forms(w,Lm); f=[0]*Lm
    for b in B:
        c=random.randrange(mod); f=[(x+c*y)%mod for x,y in zip(f,b)]
    # make cuspidal: subtract constant via combination? keep simple: subtract c0*E_w-ish -> just zero constant term artificially not modular; instead use Delta*form
    return f
Dl=[0]+[1]+[0]*(LL-2)
def Delta(Lm):
    d=[0]*Lm; E=Eser2(Lm)
    # Delta = q*E^24
    e24=[1]+[0]*(Lm-1)
    for _ in range(24): e24=mul(e24,E,mod,Lm)
    for i in range(Lm-1): d[i+1]=e24[i]
    return d
Dq=Delta(LL)
import sympy
from fractions import Fraction
kk=l-1; Bk=sympy.bernoulli(kk); ck=Fraction(-2*kk)/Fraction(Bk.p,Bk.q)
EkL=[1]+[(ck*sigma(n,kk-1)).numerator*pow((ck*sigma(n,kk-1)).denominator,-1,mod)%mod for n in range(1,LL)]
_cache={}
def EkL_pow(t):
    if t in _cache: return _cache[t]
    r=[1]+[0]*(LL-1); base=EkL[:]; e=t
    while e:
        if e&1: r=mul(r,base,mod,LL)
        base=mul(base,base,mod,LL); e>>=1
    _cache[t]=r; return r
def rand_env(c):
    f=[0]*LL
    for j in range(3):
        w=(j+c)*(l-1)-12
        g=mul(randform(w,LL),Dq,mod,LL)   # cusp form of weight (j+c)(l-1)
        tt=(l**(D-1)*(l-1)-(j+c)*(l-1))//(l-1)
        g=mul(g,EkL_pow(tt),mod,LL)
        f=[(x+(l**j)*y)%mod for x,y in zip(f,g)]
    return f
def U(f): return [f[l*n] for n in range(len(f)//l)]
def digitfilts(G,D0,start):
    R=G[:]+[0]*max(0,L-len(G)); R=R[:L]; ws=[]
    for j in range(D0):
        dig=[(x//l**j)%l for x in R]
        if all(x==0 for x in dig[:NC]): ws.append(None); continue
        w=filtration(dig[:L], l**(j+4)*(l-1)); ws.append(w)
        lf=lift_of(dig,w); tt=(l**(D-1)*(l-1)-w)//(l-1); lf=mul(lf,pw(Ek,tt),mod,L)
        R=[(x-(l**j)*y)%mod for x,y in zip(R,lf)]
    return ws
for c in (1,2):
    f=rand_env(c)
    Df=U(mul(Phi,f,mod,LL))
    Uf=U(f)
    print(f'c={c}: input envelope ~(j+{c})(l-1); D(f) digit filtrations', digitfilts(Df,3,0), ' U(f):', digitfilts(Uf,3,0), flush=True)
