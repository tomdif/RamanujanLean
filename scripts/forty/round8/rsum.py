"""Yesilyurt's R(eps,delta,l,t,alpha,beta,m,p) (JMAA 2012 (2.18), x=y=1) as a binary form:
R = sum_{M,J} (-1)^{eps M + delta J} q^{[beta(2M+t)^2 + alpha(2pJ+2mM+mt+pl)^2]/(4p)}.
Exponents are returned scaled by S (q = s^S) so that everything is integral."""
from fractions import Fraction as Fr
import numpy as np
def Rform(eps,delta,l,t,alpha,beta,m,p):
    l=Fr(l)
    # E(M,J) = lam M^2 + 2 alpha m M J + alpha p J^2 + dM M + dJ J + c0
    lam=Fr(alpha*m*m+beta,p)
    c=lambda M,J: (beta*(2*M+t)**2 + alpha*(2*p*J+2*m*M+m*t+p*l)**2)/Fr(4*p)
    c0=c(0,0); dM=c(1,0)-c0-lam; dJ=c(0,1)-c0-alpha*p
    return (lam, alpha*m, alpha*p, dM, dJ, eps%2, delta%2, c0)
def series(F,P,S=1,R=60):
    lam,b,cc,dM,dJ,s1,s2,c0=F
    out={}
    for M in range(-R,R+1):
        for J in range(-R,R+1):
            E=(lam*M*M+2*b*M*J+cc*J*J+dM*M+dJ*J+c0)*S
            if E< P:
                assert E.denominator==1, E
                E=int(E); out[E]=out.get(E,0)+(-1)**((s1*M+s2*J)%2)
    return out
if __name__=="__main__":
    for args in [(1,0,Fr(-1,3),1,3,23,2,5),(1,-9,Fr(-1,3),4,69,1,1,10),(0,1,Fr(-1,3),1,3,23,2,5),(0,1,Fr(-1,3),4,69,1,1,10)]:
        F=Rform(*args); print(args,F)
        s=series(F,400,S=12); print(sorted(s.items())[:12])
