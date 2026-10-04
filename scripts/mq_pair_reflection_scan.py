import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from paley_spinor_scan import isotropic_j_representatives, short_projective_roots, restricted_lattice, projective_root_target
from quintuple_vanishing_scan import primes_through
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
maxp=int(sys.argv[1]); depth=int(sys.argv[2])
def points(p,idx,Kmax):
    # list of (K, Y tuple, sign)
    per=[]
    for i in idx:
        lst=[]
        m=-1
        # enumerate m in range where exponent <= Kmax
        M=int((6*Kmax/p)**0.5)+3
        for m in range(-M,M+1):
            if m%3==2: continue
            E=i*m+p*m*(m-1)//6
            if 0<=E<=Kmax:
                lst.append((E,2*p*m-p+6*i,1 if m%3==0 else -1))
        per.append(lst)
    out=defaultdict(list)
    for a in per[0]:
        for b in per[1]:
            if a[0]+b[0]>Kmax: continue
            for c in per[2]:
                K=a[0]+b[0]+c[0]
                if K<=Kmax: out[K].append(((a[1],b[1],c[1]),a[2]*b[2]*c[2]))
    return out
stats=Counter(); dnorms=Counter(); ex=[]
for p in primes_through(maxp):
    Kmax=p*depth+p-1
    for triple in isotropic_j_representatives(p).values():
        roots=short_projective_roots(p,triple)
        pred=set()
        if roots:
            lat=restricted_lattice(p,triple)
            pred={projective_root_target(r,lat)[1] for r in roots}
        pts=points(p,triple,Kmax)
        for r in range(p):
            if r in pred: continue
            shells=[K for K in range(r,Kmax+1,p) if pts.get(K)]
            if not shells: continue
            K0=shells[0]; P0=pts[K0]
            if sum(s for _,s in P0)!=0: continue
            if len(P0)!=2: stats['first shell cancel >2 points']+=1; continue
            (Y,s1),(Y2,s2)=P0
            d=tuple(a-b for a,b in zip(Y,Y2)); g=0
            for x in d: g=gcd(g,abs(x))
            dp=tuple(x//g for x in d); nd=sum(x*x for x in dp)
            dnorms[(nd%p==0, nd//p if nd%p==0 else None)]+=1
            # test reflection R_d on later shells: does it map signed point multiset to negated one?
            dd=sum(x*x for x in d)
            fail=None
            for K in shells:
                S=Counter()
                for Yv,s in pts[K]: S[Yv]+=s
                ok=True
                for Yv,s in pts[K]:
                    t=sum(a*b for a,b in zip(Yv,d))
                    Rv=tuple(Fraction(a)-Fraction(2*t,dd)*b for a,b in zip(Yv,d))
                    if any(x.denominator!=1 for x in Rv): ok=False;break
                    Rv=tuple(int(x) for x in Rv)
                    if S.get(Rv,0)!=-s: ok=False;break
                if not ok: fail=K;break
            witness=next(K for K in shells if sum(s for _,s in pts[K])!=0) if any(sum(s for _,s in pts[K])!=0 for K in shells) else None
            if fail is None: stats['reflection never fails within depth']+=1
            elif witness==fail: stats['witness == first reflection failure']+=1
            else:
                stats['witness != first failure']+=1
                if len(ex)<8: ex.append((p,triple,r,K0//p,fail//p,witness//p if witness else None,dp,nd))
print(dict(stats)); print("primitive d norm (divisible by p?, multiple):",dict(dnorms.most_common(12)))
for e in ex: print(e)
