import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from paley_spinor_scan import isotropic_j_representatives, short_projective_roots, restricted_lattice, projective_root_target
from quintuple_vanishing_scan import product_coefficients, primes_through
from collections import Counter
maxp=int(sys.argv[1]); depth=int(sys.argv[2])
stats=Counter(); even_examples=[]
for p in primes_through(maxp):
    limit=p*depth+p-1
    for triple in isotropic_j_representatives(p).values():
        roots=short_projective_roots(p,triple)
        pred=set()
        if roots:
            lat=restricted_lattice(p,triple)
            pred={projective_root_target(r,lat)[1] for r in roots}
        co=product_coefficients(p,triple,limit)
        first={}
        for e in sorted(co):
            first.setdefault(e%p,(e,co[e]))
        for r in range(p):
            if r in pred: stats['root']+=1; continue
            w=first.get(r)
            if w is None: stats['unresolved']+=1; continue
            e,c=w
            if c%2: stats['odd']+=1
            else:
                stats['even']+=1
                if len(even_examples)<15: even_examples.append((p,triple,r,e//p,c))
print(dict(stats))
for x in even_examples: print("EVEN first witness:",x)
