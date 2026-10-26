"""Everything in the dissection variables c0,c1,c2,c4,c7 (Q = -c0 c1 c2 c4 c7)."""
import pickle, sympy as sp, itertools
src=open('weier_inst.py').read().split("allp={}")[0]
exec(src)
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7=sp.symbols('c0 c1 c2 c4 c7')
Qc=-c0*c1*c2*c4*c7
t4=sp.Symbol('t4s')
tsub={t[0]:-t4/(c0*c1), t[1]:t4/c0, t[2]:c7*t4, t[3]:t4, t[4]:-c2*c7*t4}
rels=set()
for x,y,u,v in itertools.product(range(-4,9),repeat=4):
    p=poly_of(x,y,u,v)
    if p is None: continue
    q=sp.together(sp.expand(p.subs(tsub).subs(Q,Qc)/t4**4))
    n,d=sp.fraction(q)
    n=sp.factor_terms(sp.expand(n))
    rels.add(sp.expand(n))
rels=[r for r in rels if r!=0]
print(len(rels))
def S(e): return str(e).replace('**','^')
Ec={j:sp.expand(E[j].subs(sp.Symbol('Q'),sp.Symbol('Qv'))) for j in range(1,12)}
with open('testc.sing','w') as f:
    f.write('LIB "elim.lib";\nring r=0,(c0,c1,c2,c4,c7),dp;\npoly Qv=-c0*c1*c2*c4*c7;\n')
    f.write('ideal W='+',\n'.join(S(r) for r in rels)+';\n')
    f.write('ideal SW=sat(W,c0*c1*c2*c4*c7);\nSW=std(SW);\n"satW size:"; size(SW);\n')
    # e_j have negative powers of Qv: multiply e_j by Qv^5 to make polynomial
    for j in (5,7,9,11):
        f.write(f'poly F{j}=' + S(sp.expand(Ec[j]*sp.Symbol('Qv')**5)) + ';\n')
    # e_j = F_j / Qv^5 ; D = e11 = F11/Qv^5
    f.write('''
poly P5=Qv^5;
// N4 = (e5+1331)/22 ; work with scaled numerators over common denominator Qv^5
poly n4=(F5+1331*P5)/22;
poly n3=(F7-1452*n4-14641*P5)/22;
poly n2=(968*n3+11979*n4+161051*P5-F9)/11;
poly D=F11;
// g_i = n_i / D  (Qv^5 cancels)
poly G4=(n4+n3)*D-n2^2;
poly R1=n2*n3-n2^2+n3*D-11*D*P5;
poly R2=n3^2*D-n2^3+n2*n3*D+D^2*P5;
"G4:"; reduce(G4,SW)==0;
"R1:"; reduce(R1,SW)==0;
"R2:"; reduce(R2,SW)==0;
quit;
''')
