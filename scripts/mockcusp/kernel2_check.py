# Numerical validation for the sharpened (D = 1) Appell-Lerch bound (MockCusp/Sharp*.lean).
# (a) bad-set lemma:  int e^{-P(x-x0)^2}/|1-e^{v0+beta x}| dx
#        <= (3/eta) sqrt(pi/P) + (1/m)(2 eta/|beta|)(1 + 16|beta|^2/(pi^2 P)),   0<eta<=1, m = inf |den|
# (b) full chain bound >= |S| for the f, phi, psi Appell-Lerch sums, and chain*|z|^{3/2} bounded (=> Hb C 1).
import numpy as np, math, cmath, random
from scipy.integrate import quad
random.seed(1)
def lemma_a(trials=300):
    worst=0
    for _ in range(trials):
        P=10**random.uniform(-3,2); x0=random.uniform(-5,5)
        beta=cmath.rect(10**random.uniform(-2,1), random.uniform(0,2*math.pi))
        if abs(beta.real)<1e-3: continue
        v0=complex(random.uniform(-3,3),random.uniform(-7,7))
        den=lambda x: abs(1-cmath.exp(v0+beta*x)) if (v0+beta*x).real<600 else 1e260
        W=1/math.sqrt(P); L=x0-12*W; R=x0+12*W
        xs=np.linspace(L,R,20001); m=min(den(x) for x in xs)
        if m<1e-6: continue
        # poles near the real line: break points
        f=lambda x: math.exp(-P*(x-x0)**2)/den(x)
        I=0; pts=np.linspace(L,R,401)
        for a,b in zip(pts[:-1],pts[1:]): I+=quad(f,a,b,limit=200)[0]
        for eta in [1,0.3,0.1,0.03,0.01]:
            bnd=3/eta*math.sqrt(math.pi/P)+(1/m)*(2*eta/abs(beta))*(1+16*abs(beta)**2/(math.pi**2*P))
            worst=max(worst,I/bnd)
    return worst
print("(a) max integral/bound =",lemma_a())

def chain(K,A,B,D,E,T,alpha,thetas):
    # thetas: phases of the T classes
    R=(1/alpha).real; re=alpha.real; na=abs(alpha)
    Y0=math.pi*R/(2*T*A); c0=math.pi**2*R/(4*A*T*T)
    W=math.sqrt(math.pi/(A*re)); N=1+16*na**2*D**2/(math.pi**2*A*re)
    gs=[]
    for th in thetas:
        d=abs(th-2*math.pi*round(th/(2*math.pi)))
        gs.append(d-math.pi*D/(2*T*A))
    assert min(gs)>0
    br=6*W+2*math.sqrt(18*N*W)*((na*D)**-0.5+(re*D)**-0.5*sum(g**-0.5 for g in gs)/T)
    pref=math.exp(c0+B*B*re/(4*A))/math.sinh(2*c0)
    return pref*br, br
def S_gen(alpha,c,om,A,B,D,E,nmax):
    s=0
    for n in range(-nmax,nmax+1):
        s+=c(n)*cmath.exp(-alpha*(A*n*n+B*n))/(1-om(n)*cmath.exp(-alpha*(D*n+E)))
    return s
worst=0; worstR=0
for K in [1,3,5,7,9,11,25,51]:
  for h in range(max(K,1)):
    if math.gcd(h,K)!=1: continue
    if K>11 and h not in (1,K//2,K-1): continue
    zeta=cmath.exp(2j*math.pi*h/K)
    thetas=[math.pi+2*math.pi*h*r/K for r in range(K)]
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30,100]:
        w=complex(K/2*(1+sig),tau*K); z=1/w; alpha=2*math.pi*z/K
        nmax=int(math.sqrt(60/(1.5*alpha.real)))+5
        if nmax>40000: continue
        S=S_gen(alpha,lambda n:(-1)**n*zeta**((n*(3*n+1)//2)%K),lambda n:-zeta**(n%K),1.5,0.5,1,0,nmax)
        b,br=chain(K,1.5,0.5,1,0,K,alpha,thetas)
        worst=max(worst,abs(S)/b); worstR=max(worstR,br*abs(z)**1.5)
print("(b) f: max |S|/chain =",worst,"  max bracket*|z|^{3/2} =",worstR)
# bracket growth at the boundary for large K (no sums needed)
for K in [1,3,11,101,1001]:
    for tau in [0,1,10,1e3,1e5]:
        z=1/complex(K/2,tau*K); alpha=2*math.pi*z/K
        thetas=[math.pi+2*math.pi*r/K for r in range(K)]
        b,br=chain(K,1.5,0.5,1,0,K,alpha,thetas)
        worstR=max(worstR,br*abs(z)**1.5)
print("    bracket*|z|^{3/2} incl. K<=1001, tau<=1e5:",worstR)
# psi: K=4T, theta_n = 2 pi h0 (4n+1)/K, (A,B,D,E)=(6,2,4,1)
worst=0; wR=0
for K in [4,8,12,20,100,404]:
  for h in range(K):
    if math.gcd(h,K)!=1: continue
    if K>12 and h not in (1,K-1): continue
    T=K//4; h0=h+2*T; zeta=cmath.exp(2j*math.pi*h0/K)
    thetas=[2*math.pi*h0*(4*n+1)/K for n in range(T)]
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30,1000]:
        w=complex(K/2*(1+sig),tau*K); z=1/w; alpha=2*math.pi*z/K
        b,br=chain(K,6,2,4,1,T,alpha,thetas); wR=max(wR,br*abs(z)**1.5)
        nmax=int(math.sqrt(60/(6*alpha.real)))+5
        if K<=12 and nmax<40000:
          S=S_gen(alpha,lambda n:(-1)**n*zeta**((6*n*n+2*n)%K),lambda n:zeta**((4*n+1)%K),6,2,4,1,nmax)
          worst=max(worst,abs(S)/b)
print("(b) psi: max |S|/chain =",worst," max bracket*|z|^{3/2} =",wR)
# phi: odd K, theta = pi/2 + 2 pi h n/K
worst=0; wR=0
for K in [1,3,5,7,9,51,501]:
  for h in range(max(K,1)):
    if math.gcd(h,K)!=1: continue
    if K>9 and h not in (1,K-1): continue
    zeta=cmath.exp(2j*math.pi*h/K)
    thetas=[math.pi/2+2*math.pi*h*r/K for r in range(K)]
    for sig in [0,1,5]:
      for tau in [0,1,-3,10,-30,1000]:
        w=complex(K/2*(1+sig),tau*K); z=1/w; alpha=2*math.pi*z/K
        b,br=chain(K,1.5,0.5,1,0,K,alpha,thetas); wR=max(wR,br*abs(z)**1.5)
        nmax=int(math.sqrt(60/(1.5*alpha.real)))+5
        if K<=9 and nmax<40000:
          S=S_gen(alpha,lambda n:(-1)**n*zeta**((n*(3*n+1)//2)%K),lambda n:1j*zeta**(n%K),1.5,0.5,1,0,nmax)
          worst=max(worst,abs(S)/b)
print("(b) phi: max |S|/chain =",worst," max bracket*|z|^{3/2} =",wR)
