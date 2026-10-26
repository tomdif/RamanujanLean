"""Targets G4,R1,R2 on the dehomogenized curve (Q=1, t5=1), sparse Laurent arithmetic in t1..t4."""
import pickle, sympy as sp, itertools
from fractions import Fraction as Fr
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7,Qs=sp.symbols('c0 c1 c2 c4 c7 Q')
# c -> Laurent monomials in t1..t4 (Q=1, t5=1): c0=t4/t2, c1=-t2/t1, c2=-1/t3, c7=t3/t4, c4=-t1
cmap={c0:(1,(0,-1,0,1)), c1:(-1,(-1,1,0,0)), c2:(-1,(0,0,-1,0)), c7:(1,(0,0,1,-1)), c4:(-1,(1,0,0,0))}
def add(a,b,s=1):
    r=dict(a)
    for k,v in b.items():
        r[k]=r.get(k,0)+s*v
        if r[k]==0: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v!=0}
def scal(a,c): return {k:v*c for k,v in a.items() if v*c!=0}
def conv(expr):
    r={}
    for term in sp.Add.make_args(sp.expand(expr)):
        coef,rest=term.as_coeff_Mul()
        s=Fr(int(sp.numer(coef)),int(sp.denom(coef))); ex=[0,0,0,0]
        for f,pw in rest.as_powers_dict().items():
            if f==1 or f==Qs: continue
            sg,e=cmap[f]; pw=int(pw); s*=sg**pw
            ex=[x+pw*y for x,y in zip(ex,e)]
        k=tuple(ex); r[k]=r.get(k,0)+s
    return {k:v for k,v in r.items() if v!=0}
e={j:conv(E[j]) for j in (5,7,9,11)}
one={(0,0,0,0):Fr(1)}
# Q=1 so P5=1, F_j = e_j
n4=scal(add(e[5],scal(one,1331)),Fr(1,22))
n3=scal(add(add(e[7],scal(n4,-1452)),scal(one,-14641)),Fr(1,22))
n2=scal(add(add(add(scal(n3,968),scal(n4,11979)),scal(one,161051)),e[9],-1),Fr(1,11))
D=e[11]
G4=add(mul(add(n4,n3),D),mul(n2,n2),-1)
R1=add(add(add(mul(n2,n3),mul(n2,n2),-1),mul(n3,D)),scal(D,-11))
R2=add(add(add(mul(mul(n3,n3),D),mul(mul(n2,n2),n2),-1),mul(mul(n2,n3),D)),mul(D,D))
def clear(p):
    mn=[min(k[i] for k in p) for i in range(4)]
    den=1
    for v in p.values(): den=den*v.denominator//__import__('math').gcd(den,v.denominator)
    return {tuple(k[i]-mn[i] for i in range(4)):int(v*den) for k,v in p.items()}
def tos(p): return "+".join(f"({v})*"+"*".join(f"t{i+1}^{k[i]}" for i in range(4)) for k,v in p.items())
targets={'G4':clear(G4),'R1':clear(R1),'R2':clear(R2)}
for k,v in targets.items(): print(k,len(v),"terms", max(sum(m) for m in v))
rels=["t1^2*t3*t4 + t1*t3 - t2^2*t4","t1*t2^2*t4 + t1*t4^2 - t2*t3^2","t1^2*t2 + t1*t3*t4^2 - t2^2*t3",
"t1^3*t4 + t2*t4^3 - t3^3","t1*t2*t3^2 + t1*t4 - t2*t3*t4^2","t1^2*t2*t3 + t2*t4 - t3^2*t4",
"t1*t2^3 + t2 - t3*t4^3","t1^3*t2 + t3 - t4^3","t1^3 + t1*t3^3 - t2^3*t4","t1 + t2^3*t3 - t3^3*t4"]
with open('dehom.sing','w') as f:
    f.write('LIB "elim.lib";\nring r=0,(t1,t2,t3,t4),dp;\noption(redSB);\nideal W='+",\n".join(rels)+';\n')
    f.write('ideal GW=std(W);\n"dim"; dim(GW);\npoly m=t1*t2*t3*t4;\n')
    for k,v in targets.items():
        f.write(f'poly {k}='+tos(v)+';\n')
        f.write(f'''int kk;
for(kk=0;kk<=30;kk++){{ if(reduce(m^kk*{k},GW)==0){{break;}} }}
"{k}: sat exp "+string(kk);
matrix L{k}=lift(W,m^kk*{k});
int tot{k}=0; int jj{k};
for(jj{k}=1;jj{k}<=nrows(L{k});jj{k}++){{ tot{k}=tot{k}+size(L{k}[jj{k},1]); }}
"{k}: cofactor terms "+string(tot{k});
''')
    f.write('quit;\n')
