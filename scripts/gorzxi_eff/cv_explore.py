# exploration: derivatives of Phi via monomial lists, G = Phi(Phi'-u Phi'') + u Phi'^2
import mpmath as mp
mp.mp.dps=40
pi=mp.pi
def D(L):
    out={}
    for (a,j),c in L.items():
        out[(a,j)]=out.get((a,j),0)+a*c
        out[(a+2,j+1)]=out.get((a+2,j+1),0)-2*pi*c
    return out
phi={(mp.mpf(9)/2,2):2*pi**2,(mp.mpf(5)/2,1):-3*pi}
Ls=[phi]
for i in range(5): Ls.append(D(Ls[-1]))
def S(L,u,K=8):
    s=0
    for k in range(1,K+1):
        KK=k*k; e=mp.exp(-pi*KK*mp.exp(2*u))
        for (a,j),c in L.items(): s+=c*KK**j*mp.exp(a*u)*e
    return s
def G(u):
    P,P1,P2=[S(Ls[i],u) for i in range(3)]
    return P*(P1-u*P2)+u*P1**2
print("Phi'(0)",S(Ls[1],0),"Phi'''(0)",S(Ls[3],0))
for u in ['0.01','0.05','0.1','0.2','0.3','0.5','1','2']:
    u=mp.mpf(u); P,P1,P2=[S(Ls[i],u) for i in range(3)]
    print(u, 'G/u^3', mp.nstr(G(u)/u**3,8),'Phi',mp.nstr(P,6),"P1",mp.nstr(P1,6),"P2",mp.nstr(P2,6),"P4",mp.nstr(S(Ls[4],u),6), 'rel', mp.nstr(G(u)/(abs(P*P1)+u*abs(P*P2)),5))
# region b crude test
P0=S(Ls[0],0)
for u0 in ['0.05','0.1','0.15','0.2','0.25','0.3']:
    u0=mp.mpf(u0); us=[u0*i/200 for i in range(201)]
    m2=min(-S(Ls[2],u) for u in us); M4=max(S(Ls[4],u) for u in us)
    print('u0',u0,'m2^2',mp.nstr(m2**2,6),'P0*M4/3',mp.nstr(P0*M4/3,6))
