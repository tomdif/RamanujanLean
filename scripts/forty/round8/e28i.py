import sympy as sp
exec(open('e28f.py').read().split("out=[]")[0])
W=d1**2*(a1/b1+a2/b2)/2
T2=c1**2*d1**2
X=S*Sm*(q**2*S2+T2)
rels['e40']=S2**2-X-2*q**2
rels['e40p']=S2**2-X+2*q**2
out=[]
for k,v in rels.items():
    n=sp.expand(sp.numer(sp.together(v)))
    out.append(f"poly {k}={n};".replace("**","^"))
s='ring r=0,(a1,a2,b1,b2,q),dp;\n'+"\n".join(out)+"""
option(redSB);
ideal I=e5,e6,e6m;
ideal Is=std(I);
"prod in I:"; reduce(e40*e40p,Is)==0;
ideal J=std(I+ideal(e40));
"e7 in I+e40:"; reduce(e7,J)==0;
"e8 in I+e40:"; reduce(e8,J)==0;
poly m=a1*a2*b1*b2*q;
"e7 m:"; reduce(e7*m^4,J)==0;
"e8 m:"; reduce(e8*m^4,J)==0;
quit;
"""
open('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/s10.sing','w').write(s)
