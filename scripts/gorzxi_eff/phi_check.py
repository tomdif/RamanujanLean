import mpmath as mp
mp.mp.dps=40
def Phi(u,K=8):
    return mp.fsum((2*mp.pi**2*k**4*mp.exp(9*u/2)-3*mp.pi*k**2*mp.exp(5*u/2))*mp.exp(-mp.pi*k*k*mp.exp(2*u)) for k in range(1,K))
def b(n): return mp.quad(lambda u:u**(2*n)*Phi(u),[0,0.5,1,1.5,2,3,5])
for n in range(0,4):
    print(n, mp.nstr(b(n),15), mp.nstr(16*mp.factorial(n)*b(n)/mp.factorial(2*n),15), mp.nstr(32*mp.factorial(n)*b(n)/mp.factorial(2*n),15))
print("Phi(0.3)-Phi(-0.3)",Phi(0.3,20)-Phi(-0.3,20))
