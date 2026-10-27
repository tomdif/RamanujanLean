"""Match each 11-dissection class of E(q) with a specialized quintuple product Q(q^i, q^121) = (q^i,q^{121-i},q^121;q^121)(q^{121+2i},q^{121-2i};q^242)."""
import sys; sys.path.insert(0,'..')
from qs import *
M=3000
def poch(a,d,M):
    p=fmpq_poly([1])
    e=a
    while e<M:
        p=fmpq_poly((p*fmpq_poly([1]+[0]*(e-1)+[-1])).coeffs()[:M]) if e>0 else p
        e+=d
    return S(p,0,M)
def Qsp(i):
    s=poch(i,121,M)*poch(121-i,121,M)*poch(121,121,M)*poch(121+2*i,242,M)*poch(121-2*i,242,M)
    return s
# classes of E(q): sum over n with n(3n-1)/2 = k mod 11
E=euler(1,M)
cls={}
for n in range(-60,61):
    e=n*(3*n-1)//2
    if e<M:
        k=e%11; cls.setdefault(k,{}); cls[k][e]=cls[k].get(e,0)+(-1)**(n%2)
for k in sorted(cls):
    c=cls[k]; lo=min(c)
    ser=S(fmpq_poly([c.get(lo+j,0) for j in range(M-lo)]),lo,M)
    # find i, sign, shift with ser = sign * q^shift * Qsp(i)
    found=None
    for i in range(1,61):
        q=Qsp(i)
        ld,lc=ser.lead()
        sh=ld-q.lead()[0]; sg=lc/q.lead()[1]
        diff=ser-sg*S(q.p,q.v+sh,q.N+sh)
        if all(diff.coeff(n)==0 for n in range(max(diff.v,0),M-200)):
            found=(i,int(sg),sh); break
    print("class",k,"lead",ser.lead(),"->",found)
