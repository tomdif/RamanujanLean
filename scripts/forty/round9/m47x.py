"""round 9: the reduction of Yesilyurt (5.18) to the eta-theta identity (E) and two 'even part' identities.
Th1 = phi(q)phi(Q) + 4q^12 psi(q^2)psi(Q^2)          (= sum q^{x^2+xy+12y^2})
Th2 = phi(q^2)phi(Q^2) + 2q^6 psi(q)psi(Q) + 4q^24 psi(q^4)psi(Q^4)                  (= sum q^{2x^2+xy+6y^2})
Th3 = phi(q^3)phi(Q^3) + 2q^4 f(q^2,q^4)f(Q^2,Q^4) + 2q^16 f(q,q^5)f(Q,Q^5) + 4q^36 psi(q^6)psi(Q^6)   (= sum q^{3x^2+xy+4y^2})
(E)  Th2 - Th3 = 2 q^2 f(-q)f(-Q)
(R2) q^6 (psi(q)psi(Q) + psi(-q)psi(-Q)) = Th3(q^2) - Th2(q^4)
(R3) Th3 + Th3(-q) = 2 (Th2(q^2) + Th3(q^2) - Th3(q^4))
"""
import sys; sys.path.insert(0,'../round8')
import numpy as np
import lib; lib.P=800
from lib import *
Q=47
def fp(a,b,s=1): return f((s,a),(s,b))   # f(s q^a, s q^b)
def th(a,b,c,R=60):
    o=z()
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+b*x*y+c*y*y
            if E<lib.P: o[E]+=1
    return o
Th1=add(mul(phi(1),phi(Q)),sc(4,sh(12,mul(psi(2),psi(2*Q)))))
Th2=add(mul(phi(2),phi(2*Q)),sc(2,sh(6,mul(psi(1),psi(Q)))),sc(4,sh(24,mul(psi(4),psi(4*Q)))))
Th3=add(mul(phi(3),phi(3*Q)),sc(2,sh(4,mul(fp(2,4),fp(2*Q,4*Q)))),sc(2,sh(16,mul(fp(1,5),fp(Q,5*Q)))),sc(4,sh(36,mul(psi(6),psi(6*Q)))))
n=700
print('Th1',eq(Th1,th(1,1,12),n),'Th2',eq(Th2,th(2,1,6),n),'Th3',eq(Th3,th(3,1,4),n))
print('E',eq(sub(Th2,Th3),sc(2,sh(2,mul(fm(1),fm(Q)))),n))
print('R2',eq(sh(6,add(mul(psi(1),psi(Q)),mul(psi(1,-1),psi(Q,-1)))),sub(subq(Th3,2),subq(Th2,4)),n))
Th3m=subq(Th3,1,-1)
print('R3',eq(add(Th3,Th3m),sc(2,sub(add(subq(Th2,2),subq(Th3,2)),subq(Th3,4))),n))
