import sympy as sp
q,a1,a2,b1,b2,e1,e2,g1,g2,Uq,Vq,Um2,U4,V4=sp.symbols('q a1 a2 b1 b2 e1 e2 g1 g2 Uq Vq Um2 U4 V4')
c=a1*a2; d=b1*b2; c4=e1*c; d4=e2*d; c8=g1*c4; d8=g2*d4
Am=a1**2-a2**2; Ap=a1**2+a2**2; Bm=b1**2-b2**2; Bp=b1**2+b2**2
h3q2= d4*Uq*Um2*c8*d8-(g2*d8+q**8*g1*c8)
h1q4= c8*d8*d4*U4-(g2*d8-q**8*g1*c8)
j1= 2*g1**2-c*c4*Ap
j2= 4*q-c*c4*c8**2*Am
j3= 2*g2**2-d*d4*Bp
j4= 4*q**17-d*d4*d8**2*Bm
h14q= Uq*d-Vq*c
h14q4= U4*d4-V4*c4
P=(c8*d8*d4*U4)*h3q2+(g2*d8+q**8*g1*c8)*h1q4   # = LHS*LHS' - (g2d8)^2 + q^16 (g1c8)^2
M=(c*c4*Am)*(d*d4*Bm)
# P2: 32 q^18 d4^2 Uq Um2 U4 - 8 q^17 c c4 d d4 (a1^2 b2^2 - a2^2 b1^2)  (times 2 to avoid halves)
goalP2=32*q**18*d4**2*Uq*Um2*U4-8*q**17*c*c4*d*d4*(a1**2*b2**2-a2**2*b1**2)
X=sp.symbols('x1:6')
comb=2*M*P + X[0]*j2 + X[1]*j4 + X[2]*j1+X[3]*j3
# solve coefficients: guess forms
cand = 2*M*P - 2*d4**2*Uq*Um2*U4*(-(d*d4*d8**2*Bm)*j2*(-1)) 
r=sp.expand(goalP2-2*M*P)
print(sp.factor(r))
