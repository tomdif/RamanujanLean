import lib; lib.P=300
from lib import *
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
Q=47
A = sub(mul(H(2),G(Q)), sh(9,mul(G(2),H(Q))))      # Yesilyurt's A
B = add(mul(G(1),G(2*Q)), sh(19,mul(H(1),H(2*Q)))) # Yesilyurt's B
u=mul(chi(1),chi(Q)); v=mul(chi(1,-1),chi(Q,-1)); w=mul(chi(2,-1),chi(2*Q,-1))
iw=inv(w); iv=inv(v)
print("uv=w", eq(mul(u,v),w))
print("AB=(q^2+u)(1+2q^2/w)", eq(mul(A,B), mul(add(mono(2),u), add(mono(0),sc(2,mul(mono(2),iw))))))
print("A(q)A(-q)=(1+2q^2/w)A(q^2)", eq(mul(A,ng(A)), mul(add(mono(0),sc(2,mul(mono(2),iw))),subq(A,2))))
print("(5.6)", eq(mul(add(v,mono(2)),A), mul(subq(B,1,-1) if False else ng(B), subq(A,2))))
L=add(u,v); T=w
for sc2 in [1,2]:
    q2=mono(2*sc2//2) if False else None
# test (5.24) with q-powers as written (q^2,q^4,..) and halved
def poly(L,T,k):  # k: exponent scale: q^(k*j)
    m=lambda e: mono(e*k//2) if (e*k)%2==0 else None
    t1=sc(4,mul(T,mul(T,T))); t2=sc(-1,mul(mul(T,T),mul(L,L))); t3=sc(2,mul(m(2),mul(mul(T,T),L)))
    t4=sc(8,mul(mul(T,T),m(4))); t5=sc(4,mul(mul(T,L),m(6))); t6=sc(4,mul(m(8),T)); t7=sc(-4,m(12))
    return add(t1,t2,t3,t4,t5,t6,t7)
print("5.24 as written", poly(L,T,2)[:20])
print("5.24 halved", poly(L,T,1)[:20])
cA=mul(mul(A,ng(A)),inv(subq(A,2))); cB=mul(mul(B,ng(B)),inv(subq(B,2)))
print("cA",cA[:24]); print("cB",cB[:24])
for nm,c in [("1+2q^4/w",add(mono(0),sc(2,mul(mono(4),iw)))),("1+2q^2/w",add(mono(0),sc(2,mul(mono(2),iw))))]:
    print(nm,c[:24])
P=mul(A,B); print("AB", P[:24]); print("u",u[:12],"v",v[:12])
D=add(sub(u,v), mono(2,-1), sc(2,mul(mono(6),iw)))
print("D^2 claim", eq(mul(D,D), mul(mono(2), add(sc(4,v), mono(2,9), sc(8,mul(mono(4),iv))))))
import sympy as sp
U,V,q=sp.symbols('U V q')
Lr=U+V; Tr=U*V
P524=4*Tr**3-Tr**2*Lr**2+2*q**2*Tr**2*Lr+8*Tr**2*q**4+4*Tr*Lr*q**6+4*q**8*Tr-4*q**12
Dr=U-V-q**2+2*q**6/(U*V)
Pd=sp.numer(sp.together(Dr**2*V - q**2*(4*V**2+9*q**2*V+8*q**4)))
print(sp.factor(Pd))
print(sp.factor(P524))
print(sp.div(sp.expand(Pd),sp.expand(P524),U))
