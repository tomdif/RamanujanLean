import sympy as sp
q,a1,a2,b1,b2,e1,e2,g1,g2,L=sp.symbols('q a1 a2 b1 b2 e1 e2 g1 g2 L')
c=a1*a2; d=b1*b2; c4=e1*c; d4=e2*d; c8=g1*c4; d8=g2*d4
Am=a1**2-a2**2; Ap=a1**2+a2**2; Bm=b1**2-b2**2; Bp=b1**2+b2**2
P0= d4**2*c8**2*d8**2*L-(g2**2*d8**2-q**16*g1**2*c8**2)
j1= 2*g1**2-c*c4*Ap
j2= 4*q-c*c4*c8**2*Am
j3= 2*g2**2-d*d4*Bp
j4= 4*q**17-d*d4*d8**2*Bm
goal=32*q**18*d4**2*L-8*q**17*c*c4*d*d4*(a1**2*b2**2-a2**2*b1**2)
M=(c*c4*Am)*(d*d4*Bm)
A_=c*c4*c8**2*Am; B_=d*d4*d8**2*Bm
comb = 2*M*P0 + 2*d4**2*L*(B_*j2 + 4*q*j4) - 2*g2**2*(c*c4*Am)*j4 + 2*q**16*g1**2*(d*d4*Bm)*j2 \
       + 4*q**17*(c*c4*Am)*j3 - 4*q**17*(d*d4*Bm)*j1
print(sp.factor(sp.expand(goal-comb)))
