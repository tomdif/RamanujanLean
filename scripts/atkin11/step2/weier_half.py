import itertools, sys
from fractions import Fraction as F
exec(open('weier_span.py').read()[open('weier_span.py').read().index("def red"):open('weier_span.py').read().index("monos=")])
from flint import nmod_mat
p=1000003
E=int(sys.argv[1]) if len(sys.argv)>1 else 8
HALF=len(sys.argv)>2
monos=list(itertools.combinations_with_replacement(range(1,6),4))
idx={}
for m in monos:
    for e in range(E+1): idx[(m,e)]=len(idx)
rows=[]
rng=[F(k,2) for k in range(-12,24)] if HALF else [F(k) for k in range(-6,12)]
def isint(x): return x.denominator==1
for x,y,u,v in itertools.product(rng,repeat=4):
    args=[(x+y,x-y,u+v,u-v),(x+v,x-v,u+y,u-y),(x+u,x-u,y+v,y-v)]
    if not all(isint(a) for g in args for a in g) or not isint(u-y): continue
    T=[]
    for coef,base,ar in [(1,0,args[0]),(-1,0,args[1]),(-1,int(u-y),args[2])]:
        sg=coef; sh=base; ms=[]; zero=False
        for a in ar:
            r=red(int(a))
            if r is None: zero=True; break
            sg*=r[0]; sh+=r[1]; ms.append(r[2])
        if zero: continue
        T.append((sg,sh,ms))
    if not T: continue
    mn=min(t[1] for t in T); mx=max(t[1] for t in T)
    for j in range(-mn, E-mx+1):
        v={}
        for c,s,m in T:
            k=idx[(tuple(sorted(m)),s+j)]; v[k]=v.get(k,0)+c
        rows.append(v)
ncol=len(idx)
A=nmod_mat(len(rows),ncol,[(r.get(k,0))%p for r in rows for k in range(ncol)],p)
print("instances",len(rows),"rank",A.rank())
