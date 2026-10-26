import itertools, pickle, sympy as sp, sys
sys.path.insert(0,'.')
exec(open('weier_span.py').read().split("monos=")[0].split("E=int")[0])
src=open('weier_span.py').read()
red_src=src[src.index("def red"):src.index("monos=")]
exec(red_src)
Q=sp.Symbol('Q'); t=sp.symbols('t1:6')
polys=set()
for x,y,u,v in itertools.product(range(-4,9),repeat=4):
    T=[]
    for coef,base,args in [(1,0,(x+y,x-y,u+v,u-v)),(-1,0,(x+v,x-v,u+y,u-y)),(-1,u-y,(x+u,x-u,y+v,y-v))]:
        sg=coef; sh=base; ms=[]; zero=False
        for a in args:
            r=red(a)
            if r is None: zero=True; break
            sg*=r[0]; sh+=r[1]; ms.append(r[2])
        if zero: continue
        T.append((sg,sh,ms))
    if not T: continue
    mn=min(s for _,s,_ in T)
    pol=sum(sg*Q**(sh-mn)*sp.Mul(*[t[a-1] for a in ms]) for sg,sh,ms in T)
    pol=sp.expand(pol)
    if pol==0: continue
    # normalize sign/primitive
    pol=sp.Poly(pol,Q,*t); pol=pol.monic() if pol.LC()!=0 else pol
    polys.add(pol.as_expr())
print(len(polys),"distinct three-term polys", file=sys.stderr)
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7=sp.symbols('c0 c1 c2 c4 c7')
sub={c0:t[3]/t[1], c1:-t[1]/t[0], c2:-t[4]/t[2], c7:t[2]/t[3], c4:-Q*t[0]/t[4]}
def clear(expr):
    e=sp.together(sp.expand(expr.subs(sub)))
    n,d=sp.fraction(e)
    return sp.expand(n)
targets={'I3':E[6]-11*E[5]-13310,'e3':E[3]-121,'e4':E[4]+121}
with open('test.sing','w') as f:
    f.write('LIB "elim.lib";\nring r=0,(Q,t1,t2,t3,t4,t5),dp;\noption(redSB);\n')
    f.write('ideal W='+',\n'.join(str(p).replace('**','^') for p in polys)+';\n')
    f.write('ideal G=std(W);\n')
    f.write('ideal S=sat(W,t1*t2*t3*t4*t5);\nS=std(S);\n')
    for k,v in targets.items():
        f.write(f'poly {k}='+str(clear(v)).replace('**','^')+';\n')
        f.write(f'"{k} in W:"; reduce({k},G)==0;\n')
        f.write(f'"{k} in sat W:"; reduce({k},S)==0;\n')
    f.write('quit;\n')
