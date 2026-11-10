import lib; lib.P=200
from lib import *
A = add(mul(G(2),G(23)), sh(5,mul(H(2),H(23))))
B = sub(mul(G(46),H(1)), sh(9,mul(G(1),H(46))))
Na = mul(A, mul(fm(2),fm(23)))
Nb = mul(B, mul(fm(1),fm(46)))
print(Na[:40]); print(Nb[:40])
x = mul(chi(1,-1),chi(23,-1))
print(eq(mul(A,B), add(x, mono(1), sc(2, mul(mono(2), inv(x))))))
print("A exps", exps(A,100)); print("B exps", exps(B,100))
print("A/B exps", exps(mul(A, inv(B)),100))
