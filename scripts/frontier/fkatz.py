# fast Katz-expansion tools with python-flint (nmod_poly truncated series mod p^PR)
import sys, sympy
from fractions import Fraction
import flint
from flint import nmod_poly
def setup(p,PR,NMAX):
    g=dict(p=p,PR=PR,mod=p**PR)
    mod=g['mod']; k1=p-1
    def dimM(k):
        if k<0 or k%2 or k==2: return 0
        return k//12+(0 if k%12==2 else 1)
    DMAX=dimM(NMAX*k1)
    L=(DMAX+6)*p+5
    def sigma(n,k):
        s=0;d=1
        while d*d<=n:
            if n%d==0:
                s+=d**k
                if d*d!=n: s+=(n//d)**k
            d+=1
        return s
    def P(lst): return nmod_poly(lst,mod)
    def mul(a,b): return P((a*b).coeffs()[:L])
    def eis(k):
        B=sympy.bernoulli(k); c=Fraction(-2*k)/Fraction(B.p,B.q); out=[1]
        for n in range(1,L):
            vv=c*sigma(n,k-1); out.append(vv.numerator*pow(vv.denominator,-1,mod)%mod)
        return P(out)
    E4=eis(4);E6=eis(6);E=eis(p-1)
    e=[0]*L
    for k in range(-3000,3001):
        x=k*(3*k-1)//2
        if 0<=x<L: e[x]+=(1 if k%2==0 else -1)
    eta=P([x%mod for x in e])
    def pw(f,n):
        r=P([1]); b=f
        while n:
            if n&1: r=mul(r,b)
            b=mul(b,b); n>>=1
        return r
    def inv(f):
        c0=int(f.coeffs()[0]) if f.length() else 0
        g_=P([pow(c0,-1,mod)]); n=1
        while n<L:
            n=min(2*n,L)
            fg=P((f*g_).coeffs()[:n])
            two=P([2])-fg
            g_=P((g_*two).coeffs()[:n])
        return g_
    Delta=mul(P([0,1]),pw(eta,24))
    Mcache={}
    def miller(k):
        if k in Mcache: return Mcache[k]
        d=dimM(k); base=[]
        for a in range(d):
            r=k-12*a
            for c in range(3):
                if r-6*c>=0 and (r-6*c)%4==0: b=(r-6*c)//4; break
            base.append(mul(mul(pw(Delta,a),pw(E4,b)),pw(E6,c)))
        cf=[[int(f[t]) if t<f.length() else 0 for t in range(L)] for f in base]
        for t in range(d):
            for s_ in range(d):
                if s_!=t and cf[s_][t]:
                    c=cf[s_][t]; cf[s_]=[(x-c*y)%mod for x,y in zip(cf[s_],cf[t])]
        base=[P(c) for c in cf]
        Mcache[k]=base; return base
    def katz(F,N):
        res=[None]*(N+1); G=F
        for i in range(N,0,-1):
            Mp=miller((i-1)*k1); dp=len(Mp)
            EM=[mul(m,E) for m in Mp]
            R=G; c=[]
            for t in range(dp):
                ct=(int(R[t]) if t<R.length() else 0)*pow(int(EM[t][t]),-1,mod)%mod; c.append(ct)
                R=R-EM[t]*ct
            res[i]=R
            G=P([0])
            for t in range(dp):
                if c[t]: G=G+Mp[t]*c[t]
        res[0]=G
        return res
    def val(f,upto):
        m=PR
        for t in range(min(upto,f.length())):
            x=int(f[t])
            if x:
                c=0
                while x%p==0: x//=p;c+=1
                m=min(m,c)
        return m
    g.update(locals()); return g
