import sympy as sp
from liftlib import lift, lean
exec(open('alg28.py').read().split("def z(")[0])
VARS=[q,a1,a2,b1,b2,e1,e2,U,Um,V,Vm,Uq,Vq,Um2,Vm2,U4,V4]
names=['h14','h14m','h14q','h14m2','h14q4','h1','h1m','h2','h4']
H=[h14,h14m,h14q,h14m2,h14q4,h1,h1m,h2,h4]
def show(tag,goal,mult,hs=None):
    hs=hs or list(zip(names,H))
    co=lift(goal,[h for _,h in hs],VARS,mult)
    if co is None: print(tag,'NOTIN'); return
    print(tag,' + '.join(f"({lean(cf)}) * {n}" for (n,_),cf in zip(hs,co) if cf!=0))
show('k31', d**2*(a1*b1*Vm-a2*b2*V)-2*q**3*Vq, c)
show('k33', c*d*(U*Vm+Um*V)*d - 2*c*V*Vm*W, a1*a2*b1*b2)
show('k42', (d*U*Um - d/c**2 - q**4*c/d**2 + 2*q**2*W/(c*d**2))*c**2*d**2, 1)
