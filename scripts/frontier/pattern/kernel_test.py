# compare lattice side of AAD kernel with Poincare side, at general w (phase e(n g xi))
import mpmath as mp, math, sys, sympy as sp
mp.mp.dps=18
chi=lambda n:{1:1,11:1,5:-1,7:-1}.get(n%12,0)
def He(mu,x): 
    a,b=mp.mpf(1),x
    if mu==0: return a
    for k in range(1,mu): a,b=b,x*b-k*a
    return b
def eta(z):
    q=mp.exp(2j*mp.pi*z); P=mp.mpc(1)
    for n in range(1,3000):
        t=q**n
        if abs(t)<1e-22: break
        P*=(1-t)
    return mp.exp(2j*mp.pi*z/24)*P
def psi(N,n):
    if N==1: return 1
    return int(sp.jacobi_symbol(n%N,N))
def thstar(z,w,lam,N,B=12):
    # w is the inverted point; orig = -1/(6Nw)
    u,v=z.real,z.imag; xi,y=w.real,w.imag
    orig=-1/(6*N*w)
    wb=mp.conj(w)
    s=mp.mpc(0)
    for a in range(-B,B+1):
      pa=psi(N,a)
      if pa==0: continue
      b0=int(mp.nint(-12*a*orig.real))
      for b in range(b0-B,b0+B+1):
        ch=chi(N*b)
        if ch==0: continue
        c0=int(mp.nint(-6*N*a*orig.real**2-N*b*orig.real))
        for c in range(c0-B,c0+B+1):
          x1,x2,x3=a,N*b,6*N*c
          P=x1-x2*wb+x3*wb*wb
          D=x2*x2-4*x1*x3
          R=2*abs(P)**2/(y*y)-D
          ex=2j*mp.pi*u*D/(24*N)-mp.pi*v*R/(12*N)
          if ex.real<-45: continue
          s+=pa*ch*P**lam*mp.exp(ex)
    return v**0.5*y**(-2*lam)*s
def lattice(z,w,lam,N):
    zt=-1/(N*z); wt=-1/(6*N*w)
    return N**(-mp.mpf(lam)/2-mp.mpf(1)/4)*(-1j*z)**(-lam-mp.mpf(1)/2)*(6*N)**(-lam)*w**(-2*lam)*thstar(zt,wt,lam,N)
def Theta(mu,z,s):
    u,v=z.real,z.imag
    r=mp.mpc(0)
    for x in range(-200,201):
        ch=chi(x)
        if ch==0: continue
        ex=2j*mp.pi*x*x*z/24
        if ex.real<-45: continue
        r+=ch*He(mu,mp.sqrt(mp.pi*v/3)*x)*mp.exp(ex)*mp.exp(2j*mp.pi*x*s)
    return v**(-mp.mpf(mu)/2)*r
def poincare(z,w,lam,N,Cmax=60,sg=1,fac=1):
    xi,y=w.real,w.imag
    etaz=eta(z)
    tot=mp.mpc(0)
    for mu in range(0,lam+1):
        cmu=(sg*fac)**mu*mp.binomial(lam,mu)*6**(lam-mu+mp.mpf(1)/2)*(3/mp.pi)**(mp.mpf(mu)/2)*N**(mp.mpf(1)/4)
        for c in range(0,Cmax+1,N):
          for d in range(-Cmax,Cmax+1):
            if math.gcd(c,abs(d))!=1: continue
            if c==0 and d!=1: continue
            pd=psi(N,d) if N>1 else 1
            if pd==0: continue
            den=c*z+d
            gz=(z*0+0)  # placeholder
            # gamma = [a,b;c,d]
            if c==0: a,b=1,0
            else:
                a=pow(d,-1,c) if c>1 else 1
                b=(a*d-1)//c
            gz=(a*z+b)/den
            im=gz.imag
            for g in range(-30,31):
                if g==0: continue
                pg=psi(N,-g)
                if pg==0: continue
                ex=-6*mp.pi*y*y*g*g/im
                if ex<-45: continue
                tot+=cmu*y**(1-mu)*pg*g**(lam-mu)*pd*den**(-lam)*(etaz/eta(gz))*im**(mu-lam)*mp.exp(ex)*Theta(mu,gz,g*xi)
    return tot
tests=[(2,5),(4,5)] if len(sys.argv)<2 else eval(sys.argv[1])
for lam,N in tests:
  for z,w in [(mp.mpc(0.11,0.9),mp.mpc(0.0,0.7)),(mp.mpc(0.11,0.9),mp.mpc(0.17,0.7)),(mp.mpc(-0.2,1.1),mp.mpc(0.31,0.6))]:
    L=lattice(z,w,lam,N); P1=poincare(z,w,lam,N,sg=1); P2=poincare(z,w,lam,N,sg=-1)
    print('lam',lam,'N',N,'w',w,'ratio+',mp.nstr(L/P1,8),'ratio-',mp.nstr(L/P2,8),flush=True)
