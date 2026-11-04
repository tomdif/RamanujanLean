import mpmath as mp
mp.mp.dps=40; pi=mp.pi
def P(z):  # P0,P1,P2 polys at z
    p0=2*z**2-3*z
    p1=p0/2+2*z*(4*z-3)-2*z*p0
    # p2 = D p1, D p = p/2+2z p' - 2 z p
    dp1=mp.diff(lambda t: (2*t**2-3*t)/2+2*t*(4*t-3)-2*t*(2*t**2-3*t), z)
    p2=p1/2+2*z*dp1-2*z*p1
    return p0,p1,p2
def parts(u,Kmax=6):
    x=pi*mp.exp(2*u)
    T=[0,0,0]
    for k in range(2,Kmax+1):
        K=k*k; pp=P(K*x); e=mp.exp(-K*x)
        for i in range(3): T[i]+=pp[i]*e
    p=P(x); e1=mp.exp(-x)
    f=[p[i]*e1 for i in range(3)]
    G11=f[0]*(f[1]-u*f[2])+u*f[1]**2
    Phi=[f[i]+T[i] for i in range(3)]
    G=Phi[0]*(Phi[1]-u*Phi[2])+u*Phi[1]**2
    F=x**2*(8*x**3*(2*u-1)+x**2*(42-48*u)+x*(60*u-60)+mp.mpf(45)/2)*mp.exp(-2*x)
    return G11,G,F,G-G11
for u in ['0','0.001','0.01','0.02','0.03','0.05','0.08','0.1','0.15','0.2','0.3','0.5','0.7','1','1.5']:
    u=mp.mpf(u); G11,G,F,cr=parts(u)
    print(mp.nstr(u,4),'G11',mp.nstr(G11,6),'F',mp.nstr(F,6),'G',mp.nstr(G,6),'cross/G11',mp.nstr(cr/G11,6))
