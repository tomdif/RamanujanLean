"""round 11: is 3.15(ii) in the ideal of the Cramer relations F1..F4, degree-7 M7 at q, q^3, and Jacobi?"""
import sympy as sp
q,L,p1,m1,p3,m3,p7,m7,p21,m21=sp.symbols('q L p1 m1 p3 m3 p7 m7 p21 m21')
def num(e): return sp.numer(sp.together(e))
m2,m6,m14,m42=p1*m1,p3*m3,p7*m7,p21*m21
a=m1/m3; b=m6/m2; c=m7/m1; d=m2/m14
at=p1/p3; ct=p7/p1
a1=m7/m21; b1=m42/m14; c1=m14/m2; d1=m1/m7
a1t=p7/p21; d1t=p1/p7
rels={
 'F1': L*p1**2-(b*c+q*a*d),
 'F2': L*m1**2-(b*ct-q*at*d),
 'F3': L*p7**2-(q*a1*c1+b1*d1),
 'F4': L*m7**2-(b1*d1t-q*a1t*c1),
 'M7a': (p1*p7-m1*m7)*p1*m1*p7*m7-2*q,
 'M7b': (p3*p21-m3*m21)*p3*m3*p21*m21-2*q**3,
}
# Jacobi chi^8(q) - chi^8(-q) = 16 q / chi^8(-q^2)?  (checked numerically in jac.py)
for k,(p,m) in {1:(p1,m1),3:(p3,m3),7:(p7,m7),21:(p21,m21)}.items():
    rels[f'J{k}']=(p**8-m**8)*(p*m)**8-16*q**k
target=p1*m3*p7*m21-m1*p3*m7*p21-2*q*L
import sys
use=sys.argv[1].split(',') if len(sys.argv)>1 else list(rels)
gens=[str(sp.expand(num(rels[k]))) for k in use]
with open('ideal15.sing','w') as f:
    f.write('ring r=0,(z,L,p1,m1,p3,m3,p7,m7,p21,m21,q),dp;\noption(redSB);\n')
    f.write('ideal I='+',\n'.join(gens)+';\n')
    f.write('poly t='+str(sp.expand(target))+';\n')
    f.write('ideal J=I,z*p1*m1*p3*m3*p7*m7*p21*m21*q-1;\n')
    f.write('ideal SJ=std(J);\nprint(reduce(t,SJ));\nprint(dim(SJ));\nquit;\n')
print('wrote', use)
