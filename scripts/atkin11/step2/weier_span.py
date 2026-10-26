import sys, itertools; sys.path.insert(0,'..')
from flint import nmod_mat
p=1000003
E=int(sys.argv[1]) if len(sys.argv)>1 else 8
def red(n):
    """f(q^n) = sign * q^shift * f(q^r), r in 0..10 (with r and 11-r identified -> rep in 1..5, or 0 => zero)."""
    sign=1; shift=0
    # f(q^{n+11}) = -q^{-n} f(q^n)  <=>  f(q^m) = -q^{-(m-11)} f(q^{m-11})
    while n>=11:
        n-=11; sign=-sign; shift-=n
    while n<0:
        # f(q^n) = -q^{n} f(q^{n+11})? from f(q^{m}) = -q^{-(m-11)} f(q^{m-11}) with m=n+11: f(q^{n+11}) = -q^{-n} f(q^n) => f(q^n) = -q^{n} f(q^{n+11})
        sign=-sign; shift+=n; n+=11
    if n==0: return None
    if n>5:
        # f(q^n) = f(q^{11-n}) ? (x, Q/x; Q) symmetric under x -> Q/x: f(q^n)=f(q^{11-n})
        n=11-n
    return sign, shift, n
monos=list(itertools.combinations_with_replacement(range(1,6),4))
idx={}
for m in monos:
    for e in range(E+1): idx[(m,e)]=len(idx)
rows=[]
def addrel(terms):
    # terms: list of (coef, shift, multiset)
    v={}
    for c,s,m in terms:
        if not (0<=s<=E): return
        k=idx[(tuple(sorted(m)),s)]; v[k]=v.get(k,0)+c
    rows.append(v)
for x,y,u,v in itertools.product(range(-6,12),repeat=4):
    T=[]
    ok=True
    for coef,base,args in [(1,0,(x+y,x-y,u+v,u-v)),(-1,0,(x+v,x-v,u+y,u-y)),(-1,u-y,(x+u,x-u,y+v,y-v))]:
        sg=coef; sh=base; ms=[]; zero=False
        for a in args:
            r=red(a)
            if r is None: zero=True; break
            sg*=r[0]; sh+=r[1]; ms.append(r[2])
        if zero: continue
        T.append((sg,sh,ms))
    if not T: continue
    mn=min(t[1] for t in T)
    for j in range(-mn, E+1):
        addrel([(c,s+j,m) for c,s,m in T])
print("instances",len(rows))
ncol=len(idx)
A=nmod_mat(len(rows),ncol,[ (r.get(k,0))%p for r in rows for k in range(ncol)],p)
print("rank of Weierstrass span:",A.rank())
