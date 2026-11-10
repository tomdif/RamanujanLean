"""round 10: emit the algebra block of E35g.lean (Yesilyurt (5.18)-(5.24)); certificates checked in alg47.py."""
from sympy import symbols, expand
q,a,b,c,d,p,pp,X1,S4T1,ps,Ps,V,NV,S4V,f2_,F2,f4,F4=symbols('q a b c d p pp X1 S4T1 ps Ps V NV S4V f2_ F2 f4 F4')
names={'q':'X','a':'chip 1','b':'Pinf 1 2','c':'chip 47','d':'Pinf 47 94','p':'Pinf 2 2','pp':'Pinf 94 94',
 'X1':'S 2 T1','S4T1':'S 4 T1','ps':'fb 2 8','Ps':'fb 94 376','V':'(J 1 3 * J 47 141)','NV':'(Ng (J 1 3) * Ng (J 47 141))',
 'S4V':'(S 4 (J 1 3) * S 4 (J 47 141))','f2_':'fb 2 4','F2':'fb 94 188','f4':'fb0 4','F4':'fb0 188'}
import re
def L(e):
    s=str(e).replace('**','^')
    s=re.sub(r'\b([A-Za-z_][A-Za-z_0-9]*)\b',lambda m:'('+names[m.group(1)]+')' if m.group(1) in names else m.group(1),s)
    return s
u=a*c; v=b*d; m=u*v; P=p*pp
K=(u**2+v**2)*m**2+4*q**12+2*q**2*(u+v)*m**2+4*q**8*m
M=(u**4+v**4)*m**4+16*q**24
f1=2*q**6+u**2*v+u*v**2
f2=2*q**6-2*q**2*u*v+u**2*v+u*v**2
A=f2_*F2+q**24*f4*F4
ph=a**2*p; phb=b**2*p; Ph=c**2*pp; Phb=d**2*pp
xx=(a*b)**2*ps; yy=(c*d)**2*Ps
out={}
out['K']=L(K); out['M']=L(M); out['f1']=L(f1); out['f2']=L(f2); out['m']=L(m); out['P']=L(P)
out['K1cert']=f"(2 * ({L(m)})^2) * h518 + ({L(m)})^2 * hS4 + 4 * X^12 * ((({L(c*d)})^2 * ({L(Ps)})) * hps + ({L(p)}) * hPs) + 2 * X^2 * ({L(m)})^2 * (hV + hNV) + 4 * X^8 * ({L(m)}) * hS4V"
st1=f"(2 * ({L(X1)} + {L(A)})) * hX1 - (({L(ph)})^2 * sqQ + ({L(F2**2+q**47*F4**2)}) * sq) - (({L(phb)})^2 * sqQN + ({L(F2**2-q**47*F4**2)}) * sqN) + 4 * X^24 * (({L(F2*F4)}) * p6 + 2 * ({L(ps)})^2 * p6Q)"
out['K2cert']=f"({L(m)})^4 * ({st1}) + 16 * X^24 * ({L(xx*yy+p*pp)}) * (({L(yy)}) * hps + ({L(p)}) * hPs)"
import json; json.dump(out,open('g_alg.json','w'),indent=1)
for k,vv in out.items(): print(k,':',vv[:200])
