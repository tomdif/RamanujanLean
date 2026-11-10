"""round 9: sympy checks of the linear_combination certificates in E28f.lean (Entry 3.28(ii))."""
import sympy as sp
q,a1,a2,b1,b2,e1,e2,g1,g2,U,Um,V,Vm,Uq,Vq,Um2,U4,V4,W=sp.symbols('q a1 a2 b1 b2 e1 e2 g1 g2 U Um V Vm Uq Vq Um2 U4 V4 W')
c=a1*a2; d=b1*b2; c4=e1*c; d4=e2*d; c8=g1*c4; d8=g2*d4
def z(n,e): r=sp.expand(e); print(n, r==0 or sp.factor(r))
h14=U*b2-V*a2; h14m=Um*b1-Vm*a1; h14q=Uq*d-Vq*c; h14q4=U4*d4-V4*c4
k14=(Um*b1)*h14+(V*a2)*h14m
hA=a2**2*c*b2*d*V-(a2*d**2-q**2*b2*c**2)
hAm=a1**2*c*b1*d*Vm-(a1*d**2-q**2*b1*c**2)
# glue1
z('glue1', a2*b2*(c*d*b2*U-(b1*d-q**2*a1*c)) - ((a2*b2*c*d)*h14+hA))
h15=2*q*Uq-c**2*(Vm*a1**2-V*a2**2)
z('glue2', c*d**2*(2*q*Vq-d*(a1*b2-a2*b1)) - ((-2*q*d**2)*h14q+d**3*h15+(c*d*b2)*hAm-(c*d*b1)*hA))
hB=c**2*c4*d*d4*(V*Vm)-(c*d4**2+q**4*d*c4**2)
z('glue3', c*d*(d*U*Um*c4*d4-(e2*d4+q**4*e1*c4)) - ((c*d*c4*d4)*k14+hB))
h3=d*U*Um*c4*d4-(e2*d4+q**4*e1*c4)
h1q2=c4*d4*d*Uq-(e2*d4-q**4*e1*c4)
A=d*U*Um*c4*d4; B=c4*d4*d*Uq; X1=e2*d4; Y1=q**4*e1*c4
z('alg5', c*d*e1**2*e2**2*((U*V*(Um*Vm)-Uq*Vq)*(c*d)**2-4*q**4) - ((A+X1+Y1)*h3-(B+X1-Y1)*h1q2+d*c4**2*d4**2*(-U*Um*k14+Uq*h14q)))
P28=(Um*Vq)**2-q*V**2-b2**3*a2
z('alg6', a1*b2*d*(Um*Vm*(Uq*Vq)-q*(U*V)-a2**2*b2**2) - (a1*a2*d*P28+b2*Um*Vq*(-Uq*d*h14m+Um*b1*h14q)-a1*d*q*V*h14))
h2=2*q*Vq-d*(a1*b2-a2*b1); h4=2*W-d*(a1*b2+a2*b1)
z('alg27', 4*(W**2-q**2*Vq**2-d**3*c) - ((2*W-2*q*Vq)*(h4+h2)+2*d*a1*b2*(h4-h2)))
# alg4
h3q2=d4*Uq*Um2*c8*d8-(g2*d8+q**8*g1*c8)
h1q4=c8*d8*d4*U4-(g2*d8-q**8*g1*c8)
Am=a1**2-a2**2; Ap=a1**2+a2**2; Bm=b1**2-b2**2; Bp=b1**2+b2**2
j1=2*g1**2-c*c4*Ap; j2=4*q-c*c4*c8**2*Am; j3=2*g2**2-d*d4*Bp; j4=4*q**17-d*d4*d8**2*Bm
L=Uq*Um2*U4
P0=d4**2*c8**2*d8**2*L-(g2**2*d8**2-q**16*g1**2*c8**2)
z('P0', P0-((c8*d8*d4*U4)*h3q2+(g2*d8+q**8*g1*c8)*h1q4))
M=(c*c4*Am)*(d*d4*Bm); A_=c*c4*c8**2*Am; B_=d*d4*d8**2*Bm
comb=2*M*P0+2*d4**2*L*(B_*j2+4*q*j4)-2*g2**2*(c*c4*Am)*j4+2*q**16*g1**2*(d*d4*Bm)*j2+4*q**17*(c*c4*Am)*j3-4*q**17*(d*d4*Bm)*j1
K1=4*q*d4*L-c*c4*d*(a1**2*b2**2-a2**2*b1**2)
z('P2', 8*q**17*d4*K1-comb)
K2=c*c4*(4*q*Vq*(Um2*V4)-d**2*(a1*b2-a2*b1)*(a1*b2+a2*b1))
z('K2', K2-(d*K1-4*q*Um2*(U4*d4)*h14q-4*q*Um2*Vq*c*h14q4))
K2p=4*q*Vq*(Um2*V4)-d**2*(a1*b2-a2*b1)*(a1*b2+a2*b1)
z('K3', 2*q*Vq*(2*(Um2*V4)-d*(a1*b2+a2*b1)) - (K2p - d*(a1*b2+a2*b1)*h2))
