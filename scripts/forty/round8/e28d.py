import lib; lib.P=700
from lib import *
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
Q=17
V=add(mul(G(1),G(2*Q)), sh(7,mul(H(1),H(2*Q))))
U=sub(mul(G(Q),H(2)), sh(3,mul(G(2),H(Q))))
J=lambda e,N: f((-1,e),(-1,N-e))
P88=fm(8); P22=fm(2); P3434=fm(34)
lhs=mul(P88, sub(mul(J(68,136),J(2,8)), sh(4,mul(J(34,136),J(4,8)))))
rhs=mul(mul(P22,P3434), mul(subq(V,2), J(2,8)))
print("E13'", eq(lhs[:600],rhs[:600]))
lhs2=mul(P88, add(mul(J(68,136),J(2,8)), sh(4,mul(J(34,136),J(4,8)))))
rhs2=mul(mul(P22,P3434), mul(mul(V,ng(V)), J(2,8)))
print("E21' (VV-)", eq(lhs2[:600],rhs2[:600]))
