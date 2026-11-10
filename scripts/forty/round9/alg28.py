"""certificates for the abstract algebra of Entry 3.28(ii) (Yesilyurt §3, (3.29)-(3.44))."""
import sympy as sp
q,a1,a2,b1,b2,e1,e2,U,Um,V,Vm,Uq,Vq,Um2,Vm2,U4,V4=sp.symbols('q a1 a2 b1 b2 e1 e2 U Um V Vm Uq Vq Um2 Vm2 U4 V4')
c=a1*a2; d=b1*b2
h14=U*b2-V*a2; h14m=Um*b1-Vm*a1; h14q=Uq*d-Vq*c; h14m2=Um2*e2-Vm2*e1; h14q4=U4*(e2*d)-V4*(e1*c)
h1=c*d*b2*U-(b1*d-q**2*a1*c); h1m=c*d*b1*Um-(b2*d-q**2*a2*c)
h2=2*q*Vq-d*(a1*b2-a2*b1); h4=2*(Um2*V4)-d*(a1*b2+a2*b1)
s1=U*V; s2=Um*Vm; P=Uq*Vq; W=Um2*V4; Z=Um2*Vm2*(U4*V4); t=(c*d)**2
h5=(s1*s2-P)*t-4*q**4; h6=s2*P-q*s1-a2**2*b2**2; h6m=s1*P+q*s2-a1**2*b1**2; h6q2=Z-q**2*P-t
def z(name, e): 
    r=sp.expand(e); print(name, r==0 or r)
# kZ: (Vm2*U4*d - W*c)*(e1*e2) = 0
z('kZ', (Vm2*U4*d-W*c)*(e1*e2) - ((Vm2*e1)*h14q4 - (V4*e1*c)*h14m2))
# k14: U*Um*d - V*Vm*c
z('k14', U*Um*d-V*Vm*c - ((Um*b1)*h14+(V*a2)*h14m))
# k16 * d : c^2*(a1*b1*Um-a2*b2*U)*d - 2*q*Uq*d
z('k16', (c**2*(a1*b1*Um-a2*b2*U)-2*q*Uq)*d - (c*a1*h1m - c*a2*h1 - c*h2 - 2*q*h14q))
g31=d**2*(a1*b1*Vm-a2*b2*V)-2*q**3*Vq
z('k31', g31*c - (-a2*b1*d**2*h14m*a1/a1 + a1*b2*d**2*h14 + d*b1*h1m - d*b2*h1 + q**2*c*h2))
