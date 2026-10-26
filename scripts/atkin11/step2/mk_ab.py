import pickle, sympy as sp, itertools
exec(open('mk_c.py').read().split("def S(e)")[0])   # rels (W in c-vars), E, symbols, tsub
def S(e): return str(e).replace('**','^')
tt=sp.symbols('t1:6'); QQ=sp.Symbol('Q')
Aexpr=-QQ**3*tt[0]**3*tt[2]*tt[3]**2 - QQ**3*tt[0]**2*tt[1]*tt[2]**3 + QQ*tt[0]*tt[2]*tt[4]**4
Bexpr=(QQ**4*tt[0]**4*tt[2]**2 + 6*QQ**3*tt[0]**3*tt[2]*tt[3]**2 + 6*QQ**3*tt[0]**2*tt[1]*tt[2]**3 + QQ**2*tt[0]**2*tt[3]**4
       - 6*QQ*tt[0]*tt[2]*tt[4]**4 + QQ**2*tt[1]**4*tt[4]**2 + QQ**2*tt[1]**2*tt[2]**4 + tt[3]**2*tt[4]**4)
def toc(expr):
    q=sp.together(sp.expand(expr.subs({tt[i]:tsub[t[i]] for i in range(5)}).subs(QQ,Qc)/t4**6))
    return q
Ac=toc(Aexpr); Bc=toc(Bexpr)
nA,dA=sp.fraction(Ac); nB,dB=sp.fraction(Bc)
g2c=sp.cancel(nA*dB/(dA*nB))
gn,gd=sp.fraction(g2c)
print("g2 num terms",len(sp.Add.make_args(sp.expand(gn))),"den terms",len(sp.Add.make_args(sp.expand(gd))))
Ec={j:sp.expand(E[j].subs(sp.Symbol('Q'),sp.Symbol('Qv'))) for j in range(1,12)}
with open('testab.sing','w') as f:
    f.write('LIB "elim.lib";\nring r=0,(c0,c1,c2,c4,c7),dp;\noption(redSB);\npoly Qv=-c0*c1*c2*c4*c7;\n')
    f.write('ideal W='+',\n'.join(S(r) for r in rels)+';\nideal GW=std(W);\n')
    for j in range(1,12): f.write(f'poly F{j}=' + S(sp.expand(Ec[j]*sp.Symbol('Qv')**5)) + ';\n')
    f.write(f'poly GN={S(sp.expand(gn))};\npoly GD={S(sp.expand(gd))};\n')
    f.write('''
poly P5=Qv^5;
// e_j = F_j/P5 ; z = 1/e11 = P5/F11 ; g2 = GN/GD
// g3 = (g2^2+11z)/(1+g2) = (GN^2*F11 + 11*P5*GD^2) / (GD*(GD+GN)*F11)
poly D3=GD*(GD+GN)*F11; poly N3=GN^2*F11+11*P5*GD^2;
// g4 = g2^2 - g3 = (GN^2*(GD+GN)*F11 - GD*N3)/(GD*D3) -- write g4 = N4/D4
poly D4=GD*D3; poly N4=GN^2*(GD+GN)*F11-GD*N3;
// common denominator for M identities: Dall = D4*F11 (g's and z) ; z*Dall = P5*D4
poly Dall=D4*F11;
poly g2D=GN*GD*(GD+GN)*F11*F11; // g2*Dall = GN/GD * GD^2 (GD+GN) F11^2
poly g3D=N3*GD*F11;             // g3*Dall
poly g4D=N4*F11;                // g4*Dall
poly zD=P5*D4;                  // z*Dall
// e_k * z * Dall = F_k/P5 * P5/F11 * Dall = F_k * D4
poly M6=22*g4D-1331*zD-F5*D4;
poly M4=22*g3D+1452*g4D+14641*zD-F7*D4;
poly M3=242*g3D+5324*g4D+73205*zD-F8*D4;
poly M2=-11*g2D+968*g3D+11979*g4D+161051*zD-F9*D4;
poly M1=121*g2D+2662*g3D+14641*g4D+161051*zD-F10*D4;
// quintic: g2^5 = z(1+13g2+34g2^2)+121z^2 : multiply by GD^5*F11^2
poly QU=GN^5*F11^2 - P5*F11*(GD^5+13*GN*GD^4+34*GN^2*GD^3) - 121*P5^2*GD^5;
list T=M6,M4,M3,M2,M1,QU; list nm="M6","M4","M3","M2","M1","QU";
int i; int k; poly m=c0*c1*c2*c4*c7;
for(i=1;i<=6;i++){
  for(k=0;k<=30;k++){ if(reduce(m^k*T[i],GW)==0){break;} }
  if(k>30){ string(nm[i])+": NOT in ideal"; }
  else {
    matrix L=lift(W,m^k*T[i]); int tot=0; int j;
    for(j=1;j<=nrows(L);j++){ tot=tot+size(L[j,1]); }
    string(nm[i])+": sat "+string(k)+" target terms "+string(size(T[i]))+" cofactor terms "+string(tot);
    kill L; kill tot; kill j;
  }
}
quit;
''')
