import mpmath as mp, math, sympy as sp
mp.mp.dps=20
chi=lambda n:{1:1,11:1,5:-1,7:-1}.get(n%12,0)
def psi(N,n):
    if N==1: return 1
    return int(sp.jacobi_symbol(n%N,N))
def eta(z):
    q=mp.exp(2j*mp.pi*z); P=mp.mpc(1)
    for n in range(1,3000):
        t=q**n
        if abs(t)<1e-25: break
        P*=(1-t)
    return mp.exp(2j*mp.pi*z/24)*P
def Theta(t,zeta):
    r=mp.mpc(0)
    for x in range(-150,151):
        c=chi(x)
        if c: r+=c*mp.exp(2j*mp.pi*(x*x*t/24+x*zeta))
    return r
def LHS(z,w,sig,N,B=10):
    xi,y=w.real,w.imag; wb=mp.conj(w)
    zt=-1/(N*z); Z=mp.conj(zt); vt=zt.imag
    kap=mp.pi*vt/(6*N*y*y); s=1j*sig/(N*z*y)
    tot=mp.mpc(0)
    for a in range(-B,B+1):
        pa=psi(N,a)
        if pa==0: continue
        b0=int(mp.nint(-12*a*xi))
        for b in range(b0-B,b0+B+1):
            ch=chi(N*b)
            if ch==0: continue
            c0=int(mp.nint(-6*N*a*xi*xi-N*b*xi))
            for c in range(c0-B,c0+B+1):
                Q=6*N*a*wb*wb+N*b*wb+c
                ex=s*Q-kap*abs(Q)**2+2j*mp.pi*(N*b*b/mp.mpf(24)-a*c)*Z
                if ex.real<-50: continue
                tot+=pa*ch*mp.exp(ex)
    return tot
def RHS(z,w,sig,N,B=12):
    xi,y=w.real,w.imag
    zt=-1/(N*z); Z=mp.conj(zt); vt=zt.imag
    kap=mp.pi*vt/(6*N*y*y); s=1j*sig/(N*z*y)
    tot=mp.mpc(0)
    pre=mp.sqrt(mp.pi/kap)*mp.sqrt(z)*mp.exp(-2j*mp.pi*3/24)*chi(N)
    for a in range(-B,B+1):
        pa=psi(N,a)
        if pa==0: continue
        for m in range(-B,B+1):
            zeta=a*Z+m
            t2=-12*N*a*y*xi; t1=6*N*a*(xi*xi-y*y)
            E=s*1j*t2-kap*t2**2+2j*mp.pi*t1*zeta+s**2/(4*kap)-1j*mp.pi*s*zeta/kap-mp.pi**2*zeta**2/kap
            if E.real<-50: continue
            z0=xi*(N*m*z-a)+sig/(2j*mp.pi)
            tot+=pa*mp.exp(E)*mp.exp(2j*mp.pi*6*z0*z0/z)*Theta(z,z0)
    return pre*tot
def Gcal(z,g,xi,y,sig):
    v=z.imag
    return mp.exp(6*g*y*sig/v-3*sig*sig/(2*mp.pi*v)-6*mp.pi*g*g*y*y/v)*Theta(z,g*xi+sig/(2j*mp.pi))/eta(z)
def termcheck(z,w,sig,N,a,m):
    # term (a,m) of RHS vs Gcal(gamma z, sig/j)*eta(z)
    xi,y=w.real,w.imag
    zt=-1/(N*z); Z=mp.conj(zt); vt=zt.imag
    kap=mp.pi*vt/(6*N*y*y); s=1j*sig/(N*z*y)
    zeta=a*Z+m; t2=-12*N*a*y*xi; t1=6*N*a*(xi*xi-y*y)
    E=s*1j*t2-kap*t2**2+2j*mp.pi*t1*zeta+s**2/(4*kap)-1j*mp.pi*s*zeta/kap-mp.pi**2*zeta**2/kap
    z0=xi*(N*m*z-a)+sig/(2j*mp.pi)
    T=mp.exp(E)*mp.exp(2j*mp.pi*6*z0*z0/z)*Theta(z,z0)
    g=math.gcd(a,N*m)*(1 if a!=0 else 1)
    c=N*m//g; d=-a//g
    if c<0 or (c==0 and d<0): g=-g; c,d=-c,-d
    if c==0: A,Bb=1,0
    else:
        A=pow(d,-1,c) if c>1 else 1
        Bb=(A*d-1)//c
    j=c*z+d; gz=(A*z+Bb)/j
    return T/(Gcal(gz,g,xi,y,sig/j)*eta(z)), g,c,d
for N in [5,7]:
  for z,w,sig in [(mp.mpc(0.11,0.9),mp.mpc(0.17,0.7),mp.mpf(0.3)),(mp.mpc(-0.2,1.1),mp.mpc(0.31,0.6),mp.mpc(0.2,-0.4))]:
    L=LHS(z,w,sig,N); R=RHS(z,w,sig,N)
    print('N',N,'L/R',mp.nstr(L/R,10))
    for (a,m) in [(1,0),(2,0),(-1,0),(1,1),(2,1),(-3,2),(3,-1)]:
        if psi(N,a)==0: continue
        r,g,c,d=termcheck(z,w,sig,N,a,m)
        print('   a,m',a,m,'g',g,'c,d',c,d,'ratio',mp.nstr(r,10))
