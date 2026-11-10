import sympy as sp
exec(open('e28f.py').read().split("out=[]")[0])
U2=V2*c1/d1
rels['e16']=a1*b1*Um-a2*b2*U-2*q*U2/c1**2
rels['e31']=a1*b1*Vm-a2*b2*V-2*q**3*V2/d1**2
for k in ['e16','e31']:
    n=sp.expand(sp.numer(sp.together(rels[k]))); print(k, 0 if n==0 else len(n.as_ordered_terms()))
out=[]
for k,v in rels.items():
    n=sp.expand(sp.numer(sp.together(v)))
    out.append(f"poly {k}={n};".replace("**","^"))
s='ring r=0,(a1,a2,b1,b2,q),dp;\n'+"\n".join(out)+"""
option(redSB);
ideal I=e5,e6,e6m,e16,e31;
ideal Is=std(I);
poly m=a1*a2*b1*b2*q;
int k;
for(k=0;k<=6;k++){ "k="+string(k); reduce(e7*m^k,Is)==0; reduce(e8*m^k,Is)==0; }
quit;
"""
open('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/s7.sing','w').write(s)
