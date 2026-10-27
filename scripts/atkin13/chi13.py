# symbolic char poly coefficients e_j(Psi'_lambda), Psi' = sum_r q^{r-7} c_r, r in R, c7=1
# monomials keyed by exponent vector over (c0,c1,c2,c5,c9,c12) plus total degree m (x7 power implicit)
import json
from collections import defaultdict
from fractions import Fraction
R=[0,1,2,5,9,12]   # c-variable residues; 7 is the constant term
def mul(A,B):
    C=defaultdict(int)
    for ka,va in A.items():
        for kb,vb in B.items():
            C[tuple(x+y for x,y in zip(ka,kb))]+=va*vb
    return {k:v for k,v in C.items() if v}
base={tuple(1 if i==j else 0 for i in range(6)):1 for j in range(6)}
base[(0,)*6]=1   # x7 = q^0 * 1
def qexp(k,m):
    s=sum(a*(r-7) for a,r in zip(k,R)); a7=m-sum(k)
    return s  # x7 contributes 0
P={(0,)*6:1}
psums=[]
for m in range(1,14):
    P=mul(P,base)
    # keep exponent ≡0 mod 13: result as poly in c and Q: key (k, Qexp)
    S={}
    for k,v in P.items():
        e=qexp(k,m)
        if e%13==0: S[(k,e//13)]=13*v
    psums.append(S)
    print(m,len(P),len(S),flush=True)
def padd(A,B,s=1):
    C=dict(A)
    for k,v in B.items():
        C[k]=C.get(k,0)+s*v
        if C[k]==0: del C[k]
    return C
def pmul(A,B):
    C=defaultdict(int)
    for (ka,qa),va in A.items():
        for (kb,qb),vb in B.items():
            C[(tuple(x+y for x,y in zip(ka,kb)),qa+qb)]+=va*vb
    return {k:v for k,v in C.items() if v}
e=[{((0,)*6,0):1}]
for j in range(1,14):
    s={}
    for i in range(1,j+1):
        t=pmul(e[j-i],psums[i-1])
        s=padd(s,t,1 if i%2==1 else -1)
    assert all(v%j==0 for v in s.values())
    e.append({k:v//j for k,v in s.items()})
    print('e',j,len(e[j]),flush=True)
json.dump([[[list(k),q,v] for (k,q),v in ej.items()] for ej in e],open('chi13.json','w'))
