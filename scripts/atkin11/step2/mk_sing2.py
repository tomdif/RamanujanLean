import pickle, sympy as sp, sys
exec(open('mk_singular.py').read().split("E=pickle.load")[0])
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7=sp.symbols('c0 c1 c2 c4 c7')
Z=sp.Symbol('Z')
sub={c0:t[3]/t[1], c1:-t[1]/t[0], c2:-t[4]/t[2], c7:t[2]/t[3], c4:-Q*t[0]/t[4]}
e={j:sp.expand(E[j].subs(sub)) for j in range(1,12)}
g4=(e[5]*Z+1331*Z)/22
g3=(e[7]*Z-1452*g4-14641*Z)/22
g2=(968*g3+11979*g4+161051*Z-e[9]*Z)/11
targets={'C8':e[8]*Z-(242*g3+5324*g4+73205*Z),'C10':e[10]*Z-(121*g2+2662*g3+14641*g4+161051*Z),
 'G4':g4-(g2**2-g3),'R1':g2*g3-(g2**2-g3+11*Z),'R2':g3**2-(g2**3-g2*g3-Z)}
def clear(expr):
    n,d=sp.fraction(sp.together(sp.expand(expr)))
    return sp.expand(n)
with open('test2.sing','w') as f:
    f.write('LIB "elim.lib";\nring r=0,(Z,Q,t1,t2,t3,t4,t5),dp;\noption(redSB);\n')
    f.write('ideal W='+',\n'.join(str(p).replace('**','^') for p in polys)+',Z*(t1*t2*t3*t4*t5)^12-Q^5;\n')
    f.write('ideal G=std(W);\n')
    for k,v in targets.items():
        f.write(f'poly {k}='+str(clear(v)).replace('**','^')+';\n')
        f.write(f'"{k} in W:"; reduce({k},G)==0;\n')
    f.write('ideal S=sat(W,t1*t2*t3*t4*t5*Q);\nS=std(S);\n')
    for k in targets: f.write(f'"{k} in sat W:"; reduce({k},S)==0;\n')
    f.write('quit;\n')
print("written")
