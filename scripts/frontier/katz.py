# Katz expansions at level 1 for prime p: compute matrices of U and D on Katz basis, report valuations
import sys, sympy
from fractions import Fraction
p=int(sys.argv[1]); PR=int(sys.argv[2]); NMAX=int(sys.argv[3])   # precision p^PR, Katz indices 0..NMAX
mod=p**PR
k1=p-1
def dimM(k):
    if k<0 or k%2: return 0
    if k==2: return 0
    return k//12 + (0 if k%12==2 else 1)
DMAX=dimM(NMAX*k1)
LQ=(DMAX+5)          # q-precision for weight-0 expansions (in output)
LIN=LQ*p+5           # input precision needed for U
def sigma(n,k):
    s=0;d=1
    while d*d<=n:
        if n%d==0:
            s+=d**k
            if d*d!=n: s+=(n//d)**k
        d+=1
    return s
def mul(a,b,L):
    c=[0]*L
    for i,x in enumerate(a[:L]):
        if x:
            for j in range(L-i):
                y=b[j]
                if y: c[i+j]=(c[i+j]+x*y)%mod
    return c
def eis(k,L):
    B=sympy.bernoulli(k); c=Fraction(-2*k)/Fraction(B.p,B.q)
    out=[1]
    for n in range(1,L):
        v=c*sigma(n,k-1); out.append(v.numerator*pow(v.denominator,-1,mod)%mod)
    return out
L=LIN
E4=eis(4,L); E6=eis(6,L); E=eis(p-1,L)
def inv(a,L):
    b=[0]*L; b[0]=pow(a[0],-1,mod)
    for m in range(1,L):
        s=0
        for j in range(1,m+1):
            if a[j]: s+=a[j]*b[m-j]
        b[m]=(-s*b[0])%mod
    return b
Einv=inv(E,L)
# Delta
def Eser(L):
    e=[0]*L
    for k in range(-2000,2001):
        x=k*(3*k-1)//2
        if 0<=x<L: e[x]+=(1 if k%2==0 else -1)
    return e
eta=Eser(L)
D24=[1]+[0]*(L-1)
for _ in range(24): D24=mul(D24,eta,L)
Delta=[0]+D24[:L-1]
# Miller basis of M_k: forms q^t + O(q^d) ; built from Delta^a E4^b E6^c with 4b+6c+12a = k
def miller(k,L):
    d=dimM(k)
    if d==0: return []
    base=[]
    for a in range(d):
        r=k-12*a
        # r = 4b+6c minimal: choose c in {0,1}, r%4
        found=None
        for c in range(0,3):
            if r-6*c>=0 and (r-6*c)%4==0: found=((r-6*c)//4,c);break
        b,c=found
        f=[1]+[0]*(L-1)
        for _ in range(a): f=mul(f,Delta,L)
        for _ in range(b): f=mul(f,E4,L)
        for _ in range(c): f=mul(f,E6,L)
        base.append(f)
    # row reduce to Miller form over Z/mod (leading coeff of Delta^a.. at q^a is 1, triangular)
    for t in range(d):
        for s in range(d):
            if s!=t and base[s][t]:
                c=base[s][t]; base[s]=[(x-c*y)%mod for x,y in zip(base[s],base[t])]
    return base
MB={}
def katz_coeffs(F,N):
    res=[None]*(N+1)
    G=F[:]
    for i in range(N,-1,-1):
        k=i*k1
        if i==0:
            res[0]=G; break
        Mp=MB.setdefault(k-k1,miller(k-k1,L))
        dp=len(Mp)
        EM=[mul(m,E,L) for m in Mp]          # E * Miller basis of M_{k-k1}
        # solve F=sum c_s Mp_s with (G - E F) having zero q^t coeffs for t<dp ; EM triangular mod p
        c=[0]*dp; R=G[:]
        for t in range(dp):
            # EM[t] has leading q^t coefficient ≡1 mod p; eliminate coefficient t of R
            lead=EM[t][t]
            ct=R[t]*pow(lead,-1,mod)%mod
            # but EM[s] for s<t also have q^t terms already processed; process in order t=0..dp-1
            c[t]=ct
            R=[(x-ct*y)%mod for x,y in zip(R,EM[t])]
        res[i]=R          # b_i in B_k (q^t coeffs t<dp vanish)
        Fp=[0]*L
        for t in range(dp):
            if c[t]: Fp=[(x+c[t]*y)%mod for x,y in zip(Fp,Mp[t])]
        G=Fp
    return res
def v(f,upto):
    m=PR
    for x in f[:upto]:
        if x%mod:
            t=0;y=x
            while y%p==0: y//=p;t+=1
            m=min(m,t)
    return m
def U(f): return [f[p*n] for n in range(len(f)//p)]
# Phi for D
delta=(p*p-1)//24
El2=[0]*L
for i in range(0,L,p*p): El2[i]=eta[i//(p*p)]%mod
etainv=inv(eta,L)
t=mul(El2,etainv,L); Phi=[0]*L
for i in range(L-delta): Phi[i+delta]=t[i]
Npow=NMAX
EN=[1]+[0]*(L-1)
for _ in range(Npow): EN=mul(EN,E,L)
mode=sys.argv[4]
for j in range(0,NMAX+1):
    k=j*k1
    M=miller(k,L); dprev=dimM(k-k1) if j>0 else 0
    for t in range(dprev,len(M)):
        b=M[t]
        if t==0 and j>0: pass
        if t==0: continue   # cusp only (skip constant-term element)
        f=mul(b,[1]+[0]*(L-1),L)
        for _ in range(j): f=mul(f,Einv,L)      # b/E^j
        if mode=='D': f=mul(f,Phi,L)
        r=U(f)                                   # weight 0, length ~ L/p
        LL=len(r)
        rE=mul(r+[0]*(L-LL),EN,L)[:LL]          # times E^N -> approx classical weight N(p-1)
        # Katz decompose using length LL
        res=katz_coeffs(rE+[0]*(L-LL),Npow)
        vals=[v(a,min(LL,DMAX+2)) for a in res]
        print(f'{mode} j={j} t={t}: v(a_i), i=0..{Npow}:',vals,flush=True)
