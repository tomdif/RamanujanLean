import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from paley_spinor_scan import isotropic_j_representatives, short_projective_roots, restricted_lattice, projective_root_target
from quintuple_vanishing_scan import primes_through
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
exec(open(__import__('os').path.join(__import__('os').path.dirname(__file__),'mq_pair_reflection_scan.py')).read().split("stats=Counter()")[0].split("maxp=int")[0])
def points(p,idx,Kmax):
    per=[]
    for i in idx:
        lst=[]
        M=int((6*Kmax/p)**0.5)+3
        for m in range(-M,M+1):
            if m%3==2: continue
            E=i*m+p*m*(m-1)//6
            if 0<=E<=Kmax: lst.append((E,m,1 if m%3==0 else -1))
        per.append(lst)
    out=defaultdict(list)
    for a in per[0]:
        for b in per[1]:
            if a[0]+b[0]>Kmax: continue
            for c in per[2]:
                K=a[0]+b[0]+c[0]
                if K<=Kmax: out[K].append(((a[1],b[1],c[1]),a[2]*b[2]*c[2]))
    return out
def is_proj_lift(d,v,p):
    # d ≡ lam v mod p for some lam (incl 0)
    for lam in range(p):
        if all((d[s]-lam*v[s])%p==0 for s in range(3)): return True
    return False
maxp=int(sys.argv[1]); depth=int(sys.argv[2])
tab=Counter()
for p in primes_through(maxp):
    Kmax=p*depth+p-1
    for v in isotropic_j_representatives(p).values():
        roots=short_projective_roots(p,v); pred=set()
        if roots:
            lat=restricted_lattice(p,v); pred={projective_root_target(r,lat)[1] for r in roots}
        pts=points(p,v,Kmax)
        for r in range(p):
            if r in pred: continue
            shells=[K for K in range(r,Kmax+1,p) if pts.get(K)]
            if not shells: continue
            K0=shells[0]; P0=pts[K0]
            if sum(s for _,s in P0)!=0 or len(P0)!=2: continue
            (m1,s1),(m2,s2)=P0
            d=tuple(a-b for a,b in zip(m1,m2)); g=0
            for x in d: g=gcd(g,abs(x))
            d=tuple(x//g for x in d); nd=sum(x*x for x in d)
            lift=is_proj_lift(d,v,p)
            kind=("lift" if lift else "nonlift")+("/tiny" if 6%nd==0 else "")+("/exactorth" if sum(a*b for a,b in zip(d,v))==0 else "")
            # witness vs failure (mapping in m-space: reflection across bisector of pair)
            mid=[Fraction(a+b,2) for a,b in zip(m1,m2)]
            fail=None
            for K in shells:
                S=Counter()
                for mv,s in pts[K]: S[mv]+=s
                ok=True
                for mv,s in pts[K]:
                    t=sum((Fraction(a)-c)*b for a,c,b in zip(mv,mid,d))
                    lam=-2*t/nd
                    rv=tuple(a+lam*b for a,b in zip(mv,d))
                    if any(Fraction(x).denominator!=1 for x in rv) or S.get(tuple(int(x) for x in rv),0)!=-s: ok=False;break
                if not ok: fail=K;break
            wit=next((K for K in shells if sum(s for _,s in pts[K])!=0),None)
            tag="never-fails" if fail is None else ("wit=fail" if wit==fail else "recancelled")
            tab[(kind,tag)]+=1
for k,c in sorted(tab.items()): print(k,c)
