# region (b) feasibility: Taylor model of even Phi at 0 with crude remainder
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps=50; pi=mp.pi
def Dpoly(p):  # p list of coeffs in z ; D p = p/2 + 2 z p' - 2 z p
    n=len(p); q=[Fr(0)]*(n+1)
    for d,c in enumerate(p):
        q[d]+=c/2; q[d]+=2*d*c; q[d+1]+=-2*c
    while q and q[-1]==0: q.pop()
    return q
P=[[Fr(0),Fr(-3),Fr(2)]]
for i in range(24): P.append(Dpoly(P[-1]))
def ev(p,z): return sum(mp.mpf(c.numerator)/c.denominator*z**d for d,c in enumerate(p))
def evabs(p,z): return sum(abs(mp.mpf(c.numerator)/c.denominator)*z**d for d,c in enumerate(p))
def S(i,u,K=6):
    x=pi*mp.exp(2*u); return mp.exp(u/2)*sum(ev(P[i],k*k*x)*mp.exp(-k*k*x) for k in range(1,K+1))
c=[S(i,0)/mp.factorial(i) for i in range(25)]
print('odd coeffs',[mp.nstr(c[i],3) for i in (1,3,5,7)])
def Mcrude(i,u0):
    zs=[pi*mp.exp(2*u0*t/400) for t in range(401)]
    m1=max(evabs(P[i],z)*mp.exp(-z) for z in zs)
    m2=sum(max(evabs(P[i],k*k*z)*mp.exp(-k*k*z) for z in zs) for k in range(2,6))
    return mp.exp(u0/2)*(m1+m2)
def Mtrue(i,u0):
    return max(abs(S(i,u0*t/400)) for t in range(401))
for u0 in ['0.1','0.15','0.2','0.25']:
    u0=mp.mpf(u0)
    for N in [3,4,5,6,7,8,10]:
        M=Mcrude(2*N,u0); Mt=Mtrue(2*N,u0)
        worst=mp.inf
        for t in range(1,201):
            u=u0*t/200
            P0=sum(c[2*j]*u**(2*j) for j in range(N)); e0=M*u**(2*N)/mp.factorial(2*N)
            Q=sum(2*j*(2-2*j)*c[2*j]*u**(2*j-4) for j in range(2,N)); eW=M*u**(2*N-4)*(1/mp.factorial(2*N-1)+1/mp.factorial(2*N-2))
            V=sum(2*j*c[2*j]*u**(2*j-2) for j in range(1,N)); eV=M*u**(2*N-2)/mp.factorial(2*N-1)
            # lower bound: Phi in [P0-e0,P0+e0] (>0), W<=? use worst
            Wlo=Q-eW; 
            lo=min((P0-e0)*Wlo,(P0+e0)*Wlo)+ (max(abs(V)-eV,0))**2
            worst=min(worst,lo)
        print('u0',u0,'N',N,'Mcrude',mp.nstr(M,4),'Mtrue',mp.nstr(Mt,4),'min G/u^3 lb',mp.nstr(worst,5))
print("---- with M = 2*Mtrue")
for u0 in ['0.1','0.15','0.2','0.25']:
    u0=mp.mpf(u0)
    for N in [5,6,7,8,10,12]:
        M=2*Mtrue(2*N,u0)
        worst=mp.inf
        for t in range(1,201):
            u=u0*t/200
            P0=sum(c[2*j]*u**(2*j) for j in range(N)); e0=M*u**(2*N)/mp.factorial(2*N)
            Q=sum(2*j*(2-2*j)*c[2*j]*u**(2*j-4) for j in range(2,N)); eW=M*u**(2*N-4)*(1/mp.factorial(2*N-1)+1/mp.factorial(2*N-2))
            V=sum(2*j*c[2*j]*u**(2*j-2) for j in range(1,N)); eV=M*u**(2*N-2)/mp.factorial(2*N-1)
            Wlo=Q-eW
            lo=min((P0-e0)*Wlo,(P0+e0)*Wlo)+ (max(abs(V)-eV,0))**2
            worst=min(worst,lo)
        print('u0',u0,'N',N,'min G/u^3 lb',mp.nstr(worst,5))
