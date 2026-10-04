import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from paley_spinor_scan import isotropic_j_representatives, short_projective_roots, restricted_lattice, projective_root_target
from quintuple_vanishing_scan import product_coefficients, primes_through, quintuple_terms, multiply_truncated
from collections import Counter
maxp=int(sys.argv[1]); depth=int(sys.argv[2])
def unsigned(p,idx,limit):
    res={0:1}
    for i in idx:
        t={e:abs(c) for e,c in quintuple_terms(p,i,limit).items()}
        res=multiply_truncated(res,t,limit)
    return res
stats=Counter(); cancel_sizes=Counter(); gaps=Counter()
for p in primes_through(maxp):
    limit=p*depth+p-1
    for triple in isotropic_j_representatives(p).values():
        roots=short_projective_roots(p,triple)
        pred=set()
        if roots:
            lat=restricted_lattice(p,triple)
            pred={projective_root_target(r,lat)[1] for r in roots}
        co=product_coefficients(p,triple,limit); un=unsigned(p,triple,limit)
        occ={}; nz={}
        for e in sorted(un):
            occ.setdefault(e%p,e)
        for e in sorted(co): nz.setdefault(e%p,e)
        for r in range(p):
            if r in pred: continue
            e0=occ[r]; e1=nz[r]
            if e0==e1: stats['first occupied shell is nonzero']+=1
            else:
                stats['first occupied shell cancels']+=1
                cancel_sizes[un[e0]]+=1
                # number of occupied shells skipped
                k=sum(1 for e in range(e0,e1,p) if un.get(e,0)>0)
                gaps[k]+=1
print(dict(stats)); print("points on cancelling first shell:",dict(sorted(cancel_sizes.items())))
print("occupied shells cancelled before witness:",dict(sorted(gaps.items())))
