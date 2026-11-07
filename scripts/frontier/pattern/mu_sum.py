import mpmath as mp
mp.mp.dps=30
def H(mu,x): return mp.hermite(mu,x/mp.sqrt(2))*2**(-mp.mpf(mu)/2)  # probabilists' He
def I(mu,g,n,y):
    f=lambda v: v**(mp.mpf(mu-3)/2)*mp.exp(-6*mp.pi*y**2*g**2/v-mp.pi*n**2*v/6)*H(mu,mp.sqrt(mp.pi*n**2*v/3))
    return mp.quad(f,[0,0.5,2,10,60,400])
def S(lam,g,n,y):
    s=0
    for mu in range(0,lam+1,2):
        c=mp.binomial(lam,mu)*6**(lam-mu+mp.mpf(1)/2)*(3/mp.pi)**(mp.mpf(mu)/2)
        s+=c*y**(1-mu)*g**(lam-mu)*I(mu,g,n,y)
    return s
for lam in [2,3,5,6]:
  rows=[]
  for (g,n,y) in [(1,1,.5),(1,1,1.1),(2,1,.5),(1,5,.3),(3,5,.2),(2,7,.15)]:
    val=S(lam,g,n,mp.mpf(y))
    rows.append(val/(g**(lam-1)*mp.exp(-2*mp.pi*g*n*y)))
  print(lam,[mp.nstr(r,10) for r in rows],flush=True)
