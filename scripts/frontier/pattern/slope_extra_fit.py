import re,ast
from math import gcd
ex=[(29,-1,8),(31,-1,26),(37,1,25),(41,-1,30),(43,-1,4),(47,1,21),(53,-1,38),(59,1,28),(61,1,6),(73,1,22)]
ps=[e[0] for e in ex]
# rational reconstruction by search
def fit(vals):
    for b in range(1,400):
        for a in range(-3000,3001):
            if a and gcd(abs(a),b)==1 and all((a-b*v)%p==0 for p,v in vals): return (a,b)
    return None
for line in open('ex.tab'):
    h,v=line.strip().split(';');h=ast.literal_eval(h);v=ast.literal_eval(v)
    if any(x%p==0 for x,p in zip(v,ps)): print(h,'zero mod l at some prime');continue
    for nm,sg in [('r',lambda e:1),('e*r',lambda e:e)]:
        r1=[(p,sg(e)*r*pow(x,-1,p)%p) for (p,e,r),x in zip(ex,v)]
        r2=[(p,sg(e)*r*x%p) for (p,e,r),x in zip(ex,v)]
        f1,f2=fit(r1),fit(r2)
        if f1: print('HIT',h,nm,'= (a/b) * a_l',f1)
        if f2: print('HIT',h,nm,'= (a/b) / a_l',f2)
print('done')
