import sympy as sp, itertools, json
def c2(k): return k*(k-1)//2
def norm(e):
    j=e//13; r=e-13*j
    if r==0: return None
    R=r if r<=6 else 13-r
    m=-(13*c2(j+1))-r*j+13*j
    s=1 if j%2==0 else -1
    return (r,j,m,R,s)
Qs=sp.Symbol('Q'); J=sp.symbols('J1:7')
seen={}; insts=[]
for x,y in itertools.product(range(-6,7),repeat=2):
    for u in range(1,7):
        for v in range(u+1,7):
            groups=[(x+y,x-y,u+v,u-v),(x+v,x-v,u+y,u-y),(y+v,y-v,x+u,x-u)]
            terms=[]
            for g in groups:
                prod=1
                for e in g:
                    n=norm(e)
                    if n is None: prod=0; break
                    r,j,m,R,s=n; prod*=s*Qs**m*J[R-1]
                terms.append(prod)
            h=sp.expand(terms[0]-terms[1]-Qs**(u-y)*terms[2])
            if h==0: continue
            args=sp.Add.make_args(h)
            # handle negative powers
            mins=min(a.as_powers_dict().get(Qs,0) for a in args)
            t=sp.expand(h*Qs**(-mins)); P=sp.Poly(t,Qs,*J); t=sp.expand(t/P.LC())
            key=sp.srepr(t)
            if key in seen or sp.srepr(sp.expand(-t)) in seen: continue
            seen[key]=1; insts.append(((x,y,u,v),str(t)))
print(len(insts))
json.dump(insts,open('weier13_inst.json','w'))
