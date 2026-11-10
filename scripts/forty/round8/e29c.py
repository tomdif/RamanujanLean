import lib; lib.P=200
from lib import *
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
A = add(mul(G(2),G(23)), sh(5,mul(H(2),H(23))))
B = sub(mul(G(46),H(1)), sh(9,mul(G(1),H(46))))
A2=subq(A,2); B2=subq(B,2)
u = mul(chi(1),chi(23)); v = mul(chi(1,-1),chi(23,-1)); w = mul(chi(2,-1),chi(46,-1))
cA = mul(mul(A,ng(A)),inv(A2)); cB = mul(mul(B,ng(B)),inv(B2))
print("cA",cA[:30]); print("cB",cB[:30])
print("cA exps", exps(cA,100)); print("cB exps", exps(cB,100))
print("1+2q^2/w", add(mono(0), sc(2,mul(mono(2),inv(w))))[:30])
