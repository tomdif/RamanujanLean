# Level-4 check of CVHyp: R(u) = -Phi'(u)/(u Phi(u)) nondecreasing on (0, oo).
# Exact termwise derivatives; dR = [ -Phi'' u Phi + Phi'(Phi + u Phi') ] / (u Phi)^2.
import mpmath as mp
mp.mp.dps = 60
pi = mp.pi
def derivs(u, K=12):
    P=P1=P2=mp.mpf(0)
    for k in range(1,K+1):
        c=pi*k*k; y=mp.exp(2*u); E=mp.exp(-c*y)
        # phi_k = (2 c^2 e^{9u/2} - 3 c e^{5u/2}) E ; write a(u)=A e^{9u/2} - B e^{5u/2}
        A=2*c*c; B=3*c
        a=A*mp.exp(4.5*u)-B*mp.exp(2.5*u); a1=4.5*A*mp.exp(4.5*u)-2.5*B*mp.exp(2.5*u); a2=20.25*A*mp.exp(4.5*u)-6.25*B*mp.exp(2.5*u)
        e1=-2*c*y; e2=-4*c*y+e1*e1   # (E)'/E, (E)''/E
        P+=a*E; P1+=(a1+a*e1)*E; P2+=(a2+2*a1*e1+a*e2)*E
    return P,P1,P2
def dR(u):
    P,P1,P2=derivs(u)
    return (-P2*u*P + P1*(P+u*P1))/(u*P)**2
mn=None
import math
us=[mp.mpf(i)/2000 for i in range(1,2001)]+[mp.mpf(1)+mp.mpf(i)/200 for i in range(1,1001)]
for u in us:
    v=dR(u)/u if u<mp.mpf('0.5') else dR(u)
    if mn is None or v<mn[1]: mn=(u,v)
    if v<=0: print("NEGATIVE at",u,v)
print("min of dR/u (u<0.5) or dR (u>=0.5) on grid (0,6]:", mp.nstr(mn[0],6), mp.nstr(mn[1],8))
for u in ['1e-3','1e-2','0.05','0.1','0.2','0.5','1','2','4','6']:
    u=mp.mpf(u); print(u, 'dR/u=',mp.nstr(dR(u)/u,10))
