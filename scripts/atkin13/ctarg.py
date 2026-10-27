import json, sympy as sp
from cform import *
chi=json.load(open('chi13.json')); co=json.load(open('modeq_coeffs.json'))
Cv=[c0,c1,c2,c5,c9,c12]
T=-1-c0*c1/Qc-c2*c12-c5*c9
out=[]
for j in range(1,14):
    X=sum(v*sp.Mul(*[ci**a for ci,a in zip(Cv,k)])*Qc**q for k,q,v in chi[j])
    a=co[f'phi{13-j}'] if j<13 else [1]
    Fj=sum(ai*T**(7-i) for i,ai in enumerate(a) if ai)
    num,den=sp.fraction(sp.together(sp.expand(X-Fj)))
    num=sp.expand(num)
    nt=len(sp.Poly(num,*Cv).terms()) if num!=0 else 0
    print(j,'terms',nt,'deg',sp.Poly(num,*Cv).total_degree() if num!=0 else -1,'den',den,flush=True)
    out.append(str(num))
json.dump(out,open('ctarg13.json','w'))
