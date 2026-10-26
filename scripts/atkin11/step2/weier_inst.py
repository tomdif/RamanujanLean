import itertools, sympy as sp
src=open('weier_span.py').read()
exec(src[src.index("def red"):src.index("monos=")])
Q=sp.Symbol('Q'); t=sp.symbols('t1:6')
def poly_of(x,y,u,v):
    T=[]
    for coef,base,args in [(1,0,(x+y,x-y,u+v,u-v)),(-1,0,(x+v,x-v,u+y,u-y)),(-1,u-y,(x+u,x-u,y+v,y-v))]:
        sg=coef; sh=base; ms=[]; zero=False
        for a in args:
            r=red(a)
            if r is None: zero=True; break
            sg*=r[0]; sh+=r[1]; ms.append(r[2])
        if zero: continue
        T.append((sg,sh,ms))
    if not T: return None
    mn=min(s for _,s,_ in T)
    pol=sp.expand(sum(sg*Q**(sh-mn)*sp.Mul(*[t[a-1] for a in ms]) for sg,sh,ms in T))
    if pol==0: return None
    return sp.Poly(pol,Q,*t).monic().as_expr()
allp={}
for x,y,u,v in itertools.product(range(-4,9),repeat=4):
    p=poly_of(x,y,u,v)
    if p is not None: allp.setdefault(p,[]).append((x,y,u,v))
print(len(allp))
good={}
for p,L in allp.items():
    ok=[a for a in L if 0<a[2]<a[3] and 2*a[3]<11]
    good[p]=ok[0] if ok else None
    print(ok[0] if ok else "NONE", "  ", p)
