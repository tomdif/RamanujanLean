import lib; lib.P=400
from lib import *
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
Q=17
V=add(mul(G(1),G(2*Q)), sh(7,mul(H(1),H(2*Q))))
U=sub(mul(G(Q),H(2)), sh(3,mul(G(2),H(Q))))
c=lambda k,s=1: chi(k,s)
I=inv
def R(a,b): return mul(a,I(b))
S=mul(U,V); Sm=ng(S); S2=subq(S,2); Sm2=subq(S,2,-1); S4=subq(S,4)
T=mul(pw(c(1,-1),2),pw(c(Q,-1),2)); Tm=ng(T); T2=subq(T,2)
N=350
print("3.1", eq(mul(c(Q,-1),U)[:N], sub(R(c(Q),c(2,-1)), sh(2,R(c(1),c(2*Q,-1))))[:N]))
print("3.2", eq(sh(1,sc(2,subq(V,2)))[:N], mul(pw(c(2*Q,-1),2), sub(R(c(1),c(Q)),R(c(1,-1),c(Q,-1))))[:N]))
print("3.3", eq(mul(c(2*Q,-1),mul(U,ng(U)))[:N], add(R(c(2*Q),c(4,-1)), sh(4,R(c(2),c(4*Q,-1))))[:N]))
print("3.4", eq(sc(2,mul(subq(U,2,-1),subq(V,4)))[:N], mul(pw(c(2*Q,-1),2), add(R(c(1),c(Q)),R(c(1,-1),c(Q,-1))))[:N]))
print("3.5", eq(sub(mul(S,Sm),S2)[:N], sc(4,sh(4,I(T2)))[:N]))
for nm,lhs in [("S(-q)S(q^2)-qS",sub(mul(Sm,S2),sh(1,S))),("S(-q)S^2(q)-qS? ",sub(mul(Sm,mul(S,S)),sh(1,S))),("S(-q)S(q^2)^? ",None)]:
    if lhs is not None: print("3.6",nm, eq(lhs[:N],T[:N]))
print("3.7", eq(sub(pw(S,3),sc(5,sh(1,S)))[:N], add(T, sc(4,sh(3,I(T))))[:N]))
cc=R(pw(c(Q,-1),3),pw(c(1,-1),3))
print("3.8", eq(sub(pw(S,4),sh(1,pw(S,2)))[:N], mul(cc, pw(add(mono(0),sh(2,I(cc))),2))[:N]))
print("3.40", eq(mul(mul(S,Sm),mul(subq(S,2,-1),S4))[:N], sub(pw(S2,2),mono(2,2))[:N]))
u1=mul(c(1),c(Q)); v1=mul(c(1,-1),c(Q,-1))
print("3.16", eq(sub(mul(u1,ng(U)),mul(v1,U))[:N], sh(1,sc(2,R(subq(U,2),pw(c(2,-1),2))))[:N]))
print("3.31", eq(sub(mul(u1,ng(V)),mul(v1,V))[:N], sh(3,sc(2,R(subq(V,2),pw(c(2*Q,-1),2))))[:N]))
