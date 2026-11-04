# Check Key Lemma bound for the f Appell-Lerch sum at odd cusps, and for phi (K=2 mod 4) / psi (K=0 mod 4) pieces.
import mpmath as mp, math
mp.mp.dps=40
def S_gen(alpha,c,om,A,B,D,E,nmax):
    s=mp.mpc(0)
    for n in range(-nmax,nmax+1):
        s+=c(n)*mp.exp(-alpha*(A*n*n+B*n))/(1-om(n)*mp.exp(-alpha*(D*n+E)))
    return s
def bound(alpha,A,B,D,E,T,delta):
    R=mp.re(1/alpha); c0=mp.pi**2*R/(4*A*T*T)
    m=min(1,(mp.re(alpha)/abs(alpha))*(delta-mp.pi*D/(2*T*A)))/3
    return (1/m)*mp.sqrt(mp.pi/(A*mp.re(alpha)))*mp.exp(B*B*mp.re(alpha)/(4*A))*2*mp.exp(-c0)/(1-mp.exp(-4*c0))
worst=0
for K in [1,3,5,7,9,11]:
  for h in range(max(K,1)):
    if math.gcd(h,K)!=1: continue
    zeta=mp.exp(2j*mp.pi*h/K)
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30]:
        w=mp.mpc(K/2*(1+sig),tau*K); z=1/w; alpha=2*mp.pi*z/K
        nmax=int(mp.sqrt(150/(1.5*mp.re(alpha))))+5
        S=S_gen(alpha,lambda n:(-1)**n*zeta**(n*(3*n+1)//2),lambda n:-zeta**n,1.5,0.5,1,0,nmax)
        b=bound(alpha,1.5,0.5,1,0,K,mp.pi/K)
        worst=max(worst,float(abs(S)/b))
print("f odd K: max |S|/bound =",worst)
# psi: K = 0 mod 4, Q = zeta' e^{-alpha}, sum (-1)^n Q^{6n^2+6n+1}/(1-Q^{4n+1}); c_n=(-1)^n zeta'^{6n^2+6n+1}, omega_n = zeta'^{4n+1}, A=6,B=6,(const 1 factored),D=4,E=1,T=K/4, delta=2pi/K
worst=0
for K in [4,8,12]:
  for h in range(K):
    if math.gcd(h,K)!=1: continue
    zeta=mp.exp(2j*mp.pi*h/K)
    # anti-periodicity check
    cfun=lambda n:(-1)**n*zeta**(6*n*n+6*n)
    assert all(abs(cfun(n+K//4)+cfun(n))<1e-20 for n in range(-5,5))
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30]:
        w=mp.mpc(K/2*(1+sig),tau*K); z=1/w; alpha=2*mp.pi*z/K
        nmax=int(mp.sqrt(150/(6*mp.re(alpha))))+5
        S=S_gen(alpha,cfun,lambda n:zeta**(4*n+1),6,6,4,1,nmax)
        b=bound(alpha,6,6,4,1,K//4,2*mp.pi/K)
        worst=max(worst,float(abs(S)/b))
print("psi K=0 mod 4: max |S|/bound =",worst)
# phi at odd K': two pieces, c_n = (-1)^n zeta^{n(3n+1)/2}, omega=-zeta^{2n}, A=3/2, B=1/2 (and B=3/2 with c_n'=(-1)^n zeta^{n(3n+3)/2}), D=2
worst=0
for K in [1,3,5,7,9]:
  for h in range(max(K,1)):
    if math.gcd(h,K)!=1: continue
    zeta=mp.exp(2j*mp.pi*h/K)
    c2=lambda n:(-1)**n*zeta**(n*(3*n+3)//2)
    assert all(abs(c2(n+K)+c2(n))<1e-20 for n in range(-5,5))
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30]:
        w=mp.mpc(K/2*(1+sig),tau*K); z=1/w; alpha=2*mp.pi*z/K
        nmax=int(mp.sqrt(150/(1.5*mp.re(alpha))))+5
        for (cf,B) in [(lambda n:(-1)**n*zeta**(n*(3*n+1)//2),0.5),(c2,1.5)]:
          S=S_gen(alpha,cf,lambda n:-zeta**(2*n),1.5,B,2,0,nmax)
          b=bound(alpha,1.5,B,2,0,K,mp.pi/K)
          worst=max(worst,float(abs(S)/b))
print("phi odd K: max |S|/bound =",worst)
