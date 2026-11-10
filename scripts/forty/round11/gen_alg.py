"""round 11: emit the final linear_combination for Entry 3.15(ii) from the Singular lift (cert15b.out):
   2*(t*g*mo) = sum (2*C_i) * F_i,  F = [F1, F2, F3, F4, M7] as in ideal15a.sing."""
import re, sympy as sp
txt=open('cert15b.out').read()
coefs=[c.replace('END','').strip().replace('\n','') for c in txt.split('COEF')[1:]]
names=['hF1','hF2','hF3','hF4','hM7']
S=sp.symbols('L p1 m1 p3 m3 p7 m7 p21 m21 q')
loc={str(s):s for s in S}
gens=[l.strip().rstrip(',;') for l in open('ideal15a.sing').read().split('ideal I=')[1].split(';')[0].split('\n')]
gens=[sp.sympify(g.replace('**','^').replace('^','**'),locals=loc) for g in gens]
t=sp.sympify('-2*L*q - m1*m7*p21*p3 + m21*m3*p1*p7',locals=loc)
g=sp.sympify('m3*m7**3-m1**3*m21',locals=loc); mo=sp.sympify('p1*m1*p3*m3*p7*m7*p21*m21*q',locals=loc)
C=[sp.sympify(c.replace('^','**'),locals=loc) for c in coefs]
chk=sp.expand(sum(c*f for c,f in zip(C,gens))-t*g*mo)
print('certificate check:',chk==0)
def lean(e):
    s=str(sp.expand(2*e)).replace('**','^')
    return s
parts=[f"({lean(c)}) * {n}" for c,n in zip(C,names)]
open('alg_lc.txt','w').write(' +\n      '.join(parts))
print(len(open('alg_lc.txt').read()))
