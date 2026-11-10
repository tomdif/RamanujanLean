import lib; lib.P=200
from lib import *
A = add(mul(G(2),G(23)), sh(5,mul(H(2),H(23))))
B = sub(mul(G(46),H(1)), sh(9,mul(G(1),H(46))))
u = mul(chi(1),chi(23)); v = mul(chi(1,-1),chi(23,-1)); w = mul(chi(2,-1),chi(46,-1))
print("M23:", eq(sub(sub(u,v), sc(2,mul(mono(3),inv(w)))), sc(2,mono(1))))
for name,s in [("A",A),("B",B),("A+B",add(A,B)),("A-B",sub(A,B)),("Av",mul(A,v)),("B/v", mul(B,inv(v))),("A*u",mul(A,u)),("B*u",mul(B,u))]:
    print(name, s[:30])
print("v",v[:30]); print("u",u[:30])
