"""Symbolic e_j(psi conjugates) as polynomials in the dissection components c_k and Q."""
import itertools, sympy as sp
from math import factorial
c0,c1,c2,c4,c7,Q=sp.symbols('c0 c1 c2 c4 c7 Q')
cs={0:c0,1:c1,2:c2,4:c4,5:sp.Integer(1),7:c7}
keys=sorted(cs)
def psum(m):
    tot=0
    for comp in itertools.product(range(m+1),repeat=len(keys)):
        if sum(comp)!=m: continue
        s=sum(k*e for k,e in zip(keys,comp))
        if (s-5*m)%11: continue
        t=(s-5*m)//11
        mult=factorial(m)
        for e in comp: mult//=factorial(e)
        term=mult*Q**t
        for k,e in zip(keys,comp): term*=cs[k]**e
        tot+=term
    return sp.expand(11*tot)
P={m:psum(m) for m in range(1,12)}
E={0:sp.Integer(1)}
for j in range(1,12):
    E[j]=sp.expand(sum((-1)**(i-1)*E[j-i]*P[i] for i in range(1,j+1))/j)
import pickle
pickle.dump(E,open('E_sym.pkl','wb'))
for j in range(1,12): print(j, len(sp.Add.make_args(E[j])), 'terms')
print('e5 =',E[5])
