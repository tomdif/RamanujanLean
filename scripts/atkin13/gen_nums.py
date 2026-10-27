import json, sympy as sp
chi=json.load(open('chi13.json')); co=json.load(open('modeq_coeffs.json')); W=json.load(open('weier13.json'))
J1,J2,J3,J4,J5,J6,Q=sp.symbols('J1:7 Q')
c=[J4/J2,-J6/J3,-J2/J1,J5/J4,Q*J1/J6,-J3/J5]
T=-1-c[0]*c[1]/Q-c[2]*c[5]-c[3]*c[4]
nums={}
for j in range(1,14):
    X=sum(v*sp.Mul(*[ci**a for ci,a in zip(c,k)])*Q**q for k,q,v in chi[j])
    a=co[f'phi{13-j}'] if j<13 else [1]
    Fj=sum(ai*T**(7-i) for i,ai in enumerate(a) if ai)
    num,den=sp.fraction(sp.together(X-Fj))
    num=sp.expand(num)
    # strip content
    nums[j]=(num,den)
    print(j,len(sp.Poly(num,J1,J2,J3,J4,J5,J6,Q).terms()),den,flush=True)
lines=['ring r=0,(J1,J2,J3,J4,J5,J6,Q),dp;','option(redSB);']
rels=[]
for rel in W:
    rels.append('+'.join(f'({s})*Q^{m}*'+'*'.join(f'J{x}' for x in mon) for s,m,mon in rel))
lines.append('ideal I='+',\n'.join(rels)+';')
lines.append('ideal G=std(I);')
lines.append('poly D=J1*J2*J3*J4*J5*J6*Q;')
for j,(num,den) in nums.items():
    lines.append(f'poly N{j}='+str(num).replace('**','^')+';')
    lines.append(f'int k{j}=0; while(reduce(D^k{j}*N{j},G)!=0 && k{j}<12){{k{j}++;}} "j={j} k=",k{j};')
lines.append('quit;')
open('cert.sing','w').write('\n'.join(lines))
import pickle; pickle.dump({j:(str(n),str(d)) for j,(n,d) in nums.items()},open('nums.pkl','wb'))
