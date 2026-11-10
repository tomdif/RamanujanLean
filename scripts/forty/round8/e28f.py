import sympy as sp
a1,a2,b1,b2,q=sp.symbols('a1 a2 b1 b2 q')
c1=a1*a2; d1=b1*b2
U=(b1/c1-q**2*a1/d1)/b2; V=U*b2/a2
Um=(b2/c1-q**2*a2/d1)/b1; Vm=Um*b1/a1
V2=d1**2*(a1/b1-a2/b2)/(2*q); U2=V2*c1/d1
S=U*V; Sm=Um*Vm; S2=U2*V2
T=a2**2*b2**2; Tm=a1**2*b1**2
cc=b2**3/a2**3
rels={
 'e5': S*Sm-S2-4*q**4/(T*Tm),
 'e6': Sm*S2-q*S-T,
 'e6m': S*S2+q*Sm-Tm,
 'e7': S**3-5*q*S-T-4*q**3/T,
 'e8': S**4-q*S**2-cc*(1+q**2/cc)**2,
}
out=[]
for k,v in rels.items():
    n=sp.numer(sp.together(v)); n=sp.expand(n)
    out.append(f"poly {k}={n};".replace("**","^"))
s='LIB "elim.lib";\nring r=0,(a1,a2,b1,b2,q),dp;\n'+"\n".join(out)+"""
ideal I=e5,e6,e6m;
ideal Is=std(sat(I,a1*a2*b1*b2*q));
"e7:"; reduce(e7,Is);
"e8:"; reduce(e8,Is);
quit;
"""
open('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/s5.sing','w').write(s)
