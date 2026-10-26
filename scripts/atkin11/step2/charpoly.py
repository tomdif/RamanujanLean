"""psi = E(q)/(q^5 E(q^121)) = q^{-5} sum_k q^k c_k(Q).  Compute the conjugate power sums / elementary symmetric
functions as power series in Q and compare with Atkin's basis at Q."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from atkin_basis import basis
from math import comb, factorial
from fractions import Fraction
M=260
def eta_a(a,M):
    p=fmpq_poly([1])
    for n in range(M):
        for e in (11*n+a, 11*n+11-a):
            if e<M: p=fmpq_poly((p*fmpq_poly([1]+[0]*(e-1)+[-1])).coeffs()[:M])
    return S(p,0,M)
H={a:eta_a(a,M) for a in range(1,6)}
Q=S(fmpq_poly([0,1]),0,M)
c={0:H[4]*H[2].inv(), 1:-1*H[2]*H[1].inv(), 2:-1*H[5]*H[3].inv(), 5:const(1,M), 7:H[3]*H[4].inv(), 4:-1*Q*H[1]*H[5].inv()}
# verify dissection: E(q)/E(q^121) == sum q^k c_k(q^11)
N2=600
Eq=euler(1,N2); E121=euler(121,N2)
lhs=Eq*E121.inv()
rhs=const(0,N2)
for k,ck in c.items():
    s=ck.subs(11); rhs=rhs+S(s.p,s.v+k,s.N+k)
print("dissection ok:", all((lhs-rhs).coeff(n)==0 for n in range(0,N2-30)))
# power sums p_m = 11 * sum_{multisets, sum k = 5m (mod 11)} multinomial prod c_k * Q^{(sum k - 5m)/11}
keys=sorted(c)
def psum(m):
    tot=const(0,M)
    for comp in itertools.product(range(m+1),repeat=len(keys)):
        if sum(comp)!=m: continue
        s=sum(k*e for k,e in zip(keys,comp))
        if (s-5*m)%11: continue
        t=(s-5*m)//11
        mult=factorial(m)
        for e in comp: mult//=factorial(e)
        term=const(mult,M)
        for k,e in zip(keys,comp):
            for _ in range(e): term=term*c[k]
        term=S(term.p,term.v+t,term.N+t)
        tot=tot+term
    return 11*tot
P={m:psum(m) for m in range(1,12)}
# Newton: e_j
E={0:const(1,M)}
for j in range(1,12):
    acc=const(0,M)
    for i in range(1,j+1):
        acc=acc+((-1)**(i-1))*E[j-i]*P[i]
    E[j]=acc*fmpq(1,j)
for j in range(1,12): print(j, E[j])
B=basis(M)
import pickle
