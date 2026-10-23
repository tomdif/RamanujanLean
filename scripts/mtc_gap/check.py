import series; series.N=120
from series import *
import al
from al import *
def P(lst): return {i:Fr(c) for i,c in enumerate(lst) if c}
psi0=P(series.psi0()); f0=P(series.f0()); Phi=P(series.RPhi())
# (4.13) psi0 = -m(q14,q30,q3) - q^-2 m(q4,q30,q3)
rhs=ladd(lsc(-1,m(1,14,30,1,3)), lsc(-1,lmul({-2:Fr(1)},m(1,4,30,1,3))))
d=ladd(psi0,lsc(-1,rhs)); print('4.13 AL psi0 diff:', {e:c for e,c in d.items() if e<100})
# (4.11) f0 = 2m(q14,q30,q4)+2q^-2 m(q4,q30,q4) + J5,10 J2,5/J1
th=lmul(lmul(J(5,10),J(2,5)),linv(Jm(1)))
rhs=ladd(lsc(2,m(1,14,30,1,4)), lsc(2,lmul({-2:Fr(1)},m(1,4,30,1,4))), th)
d=ladd(f0,lsc(-1,rhs)); print('4.11 AL f0 diff:', {e:c for e,c in d.items() if e<100})
# Prop 3.2 at x=q^2, base q^10: q^2 g(q^2,q^10) = Phi(q^2) ; g(x,q)=-x^-1 m(q^2x^-3,q^3,x^2)-x^-2 m(q x^-3,q^3,x^2)
# x=q^2, q->q^10: -q^-2 m(q^{20-6},q^30,q^4) - q^-4 m(q^{10-6},q^30,q^4)
g=ladd(lsc(-1,lmul({-2:Fr(1)},m(1,14,30,1,4))), lsc(-1,lmul({-4:Fr(1)},m(1,4,30,1,4))))
d=ladd(lmul({2:Fr(1)},g), lsc(-1,P(sub_q(series.RPhi(),2)))); print('Prop3.2 diff:', {e:c for e,c in d.items() if e<100})
# Andrews Hecke (0.3): J1 f0 = sum_{n>=0,|j|<=n} (-1)^j q^{5n^2/2+n/2-j^2}(1-q^{4n+2})
h={}
for n in range(0,20):
  for jj in range(-n,n+1):
    for e,s in ((5*n*n//2+n//2 if False else (5*n*n+n)//2 - jj*jj,1),((5*n*n+n)//2-jj*jj+4*n+2,-1)):
      if e<al.T: h[e]=h.get(e,0)+s*(-1)**jj
d=ladd(lmul(Jm(1),f0),lsc(-1,L({e:Fr(c) for e,c in h.items()}))); print('Hecke 0.3 diff:', {e:c for e,c in d.items() if e<100})
