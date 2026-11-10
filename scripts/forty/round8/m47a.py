import lib; lib.P=600
from lib import *
P=lib.P
Q=47
X1=z()
for x in range(-60,61):
    for y in range(-6,7):
        if (x-y)%2==0:
            E=(x*x+47*y*y)//2
            if E<P: X1[E]+=1
fq=lambda k,s=1: f((s,k),(-1,2*k)) if s==1 else fm(k)   # f(q^k) = f(q^k,-q^{2k}) ; f(-q^k)
fp=lambda k: f((1,k),(-1,2*k))
rhs = add(mul(phi(1),phi(Q)), mul(phi(1,-1),phi(Q,-1)))
rhs = rhs//2 if False else rhs
half = np.array([x//2 for x in rhs]); assert (rhs%2==0).all()
R = add(half, sc(2,sh(12,mul(psi(2),psi(2*Q)))), sh(2,add(mul(fp(1),fp(Q)), mul(fm(1),fm(Q)))), sc(2,sh(8,mul(fm(4),fm(4*Q)))))
print("(5.18):", eq(X1[:550],R[:550]))
print("X1 odd part zero:", all(X1[1::2][:270]==0))
