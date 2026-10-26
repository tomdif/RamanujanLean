from sympy import symbols, expand, groebner, reduced, Poly
g2,g3,z=symbols('g2 g3 z')
R1=g2*g3-(g2**2-g3+11*z)
R2=g3**2-(g2**3-g2*g3-z)
g4=g2**2-g3; g6=g2*g4
gi={1:g2,2:g3,3:g4,4:g6,5:z}
import json
ST=json.load(open('structure.json'))
def J(t):
    a,r=divmod(t,5)
    return z**a*(1 if r==0 else gi[r])
G=groebner([R1,R2],g3,g2,z,order='lex')
for k,d in ST.items():
    b,r=map(int,k.split(','))
    lhs=gi[b]*gi[r]; rhs=sum(v*J(int(t)) for t,v in d.items())
    diff=expand(lhs-rhs)
    q,rem=reduced(diff,[R1,R2],g3,g2,z,order='lex')
    print(k, 'rem',rem, 'coeffs', [expand(x) for x in q])
print('---groebner', list(G))
for k,d in ST.items():
    b,r=map(int,k.split(','))
    lhs=gi[b]*gi[r]; rhs=sum(v*J(int(t)) for t,v in d.items())
    diff=expand(lhs-rhs)
    q,rem=reduced(diff,list(G),g3,g2,z,order='lex')
    print(k,'rem',rem)
