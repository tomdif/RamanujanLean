import series as S
S.N=N=150
from series import *
T={k:getattr(S,k)() for k in ['f0','f1','F0','F1','chi0','chi1','phi0','phi1','psi0','psi1']}
G=inv(mul(inf(1,5),inf(4,5))); H=inv(mul(inf(2,5),inf(3,5)))
th4=mul(inf(1,1),inv(inf(1,1,-1)))
psi2=mul(inf(4,4),inv(inf(2,4)))
def Z(a): return not any(a)
f1,F1,phi1,psi1,chi1,psi0,F0=T['f1'],T['F1'],T['phi1'],T['psi1'],T['chi1'],T['psi0'],T['F0']
# (2_1): q f1 + q th4 H = 2 phi1(-q^2)
print('2_1', Z(add(qmul_shift(f1,1),qmul_shift(mul(th4,H),1),sc(-2,sub_q(negq(phi1),2)))))
# (3_1): f1 - th4 H = 2 psi2 G(q^4) - 2 F1(q^2)
print('3_1', Z(add(f1,sc(-1,mul(th4,H)),sc(-2,mul(psi2,sub_q(G,4))),sc(2,sub_q(F1,2)))))
# (1_1): psi1 = psi2 G(q^4) + q F1(q^2)
print('1_1', Z(add(psi1,sc(-1,mul(psi2,sub_q(G,4))),sc(-1,qmul_shift(sub_q(F1,2),1)))))
# (1_0)
print('1_0', Z(add(psi0,sc(-1,qmul_shift(mul(psi2,sub_q(H,4)),1)),sc(-1,sub_q(F0,2)),one())))
print('B1', Z(add(qmul_shift(chi1,1),sc(-2,qmul_shift(F1,1)),sc(-1,negq(phi1)))))
a=add(f1,mul(th4,H)); print(a[:20]); print(sub_q(negq(phi1),2)[:20])
b=add(f1,sc(-1,mul(th4,H))); print(b[:20]); print(add(sc(2,mul(psi2,sub_q(G,4))),sc(-2,sub_q(F1,2)))[:20])
