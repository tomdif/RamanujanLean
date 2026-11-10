import sympy as sp
from liftlib import lift, lean
q,a1,a2,b1,b2,e1,e2,g1,g2,Uq,Vq,Um2,U4,V4=sp.symbols('q a1 a2 b1 b2 e1 e2 g1 g2 Uq Vq Um2 U4 V4')
c=a1*a2; d=b1*b2; c4=e1*c; d4=e2*d; c8=g1*c4; d8=g2*d4
H={
 'h3q2': d4*Uq*Um2*c8*d8-(g2*d8+q**8*g1*c8),
 'h1q4': c8*d8*d4*U4-(g2*d8-q**8*g1*c8),
 'j1': 2*g1**2-c*c4*(a1**2+a2**2),
 'j2': 4*q-c*c4*c8**2*(a1**2-a2**2),
 'j3': 2*g2**2-d*d4*(b1**2+b2**2),
 'j4': 4*q**17-d*d4*d8**2*(b1**2-b2**2),
 'h14q': Uq*d-Vq*c,
 'h14q4': U4*d4-V4*c4,
}
goal=4*q*Vq*(Um2*V4)-d**2*(a1*b2-a2*b1)*(a1*b2+a2*b1)
V=[q,a1,a2,b1,b2,e1,e2,g1,g2,Uq,Vq,Um2,U4,V4]
for mult in [c*c4*d*d4*e1*e2*g1*g2, c**2*c4**2*d**2*d4**2*e1*e2*g1*g2*q**16, (c*c4*d*d4)**2*e1*e2*g1**2*g2**2*q**17]:
    co=lift(goal,list(H.values()),V,mult)
    print('mult',mult, None if co is None else 'FOUND')
    if co:
        for n,cf in zip(H,co): print(n,':',lean(cf))
        break
