# CNV condition: R(u) = -Phi'(u)/(u Phi(u)) nondecreasing on (0,inf)  <=>  Q(u)=u(Phi Phi''-Phi'^2)-Phi Phi' <= 0 ... sign check
import mpmath as mp
mp.mp.dps=40
def terms(u,K):
    P=P1=P2=mp.mpf(0)
    for k in range(1,K+1):
        f=lambda u: (2*mp.pi**2*k**4*mp.exp(9*u/2)-3*mp.pi*k**2*mp.exp(5*u/2))*mp.exp(-mp.pi*k*k*mp.exp(2*u))
        P+=f(u); P1+=mp.diff(f,u); P2+=mp.diff(f,u,2)
    return P,P1,P2
def R(u,K=10):
    P,P1,_=terms(u,K); return -P1/(u*P)
def dR(u,K=10):
    P,P1,P2=terms(u,K)
    return -(P2*u*P-P1*(P+u*P1))/(u*P)**2
for u in [0.01,0.05,0.1,0.2,0.3,0.5,0.75,1,1.5,2,3,4]:
    print(u, mp.nstr(R(u),10), 'dR full', mp.nstr(dR(u),8), 'dR k=1 only', mp.nstr(dR(u,1),8))
