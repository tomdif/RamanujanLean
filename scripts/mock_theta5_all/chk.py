import series as S
S.N=N=200
from series import *
T={k:getattr(S,k)() for k in ['f0','f1','F0','F1','chi0','chi1','phi0','phi1','psi0','psi1']}
Phi=RPhi(); Psi=RPsi()
F0=T['F0']
for a in (1,2):
  for c in range(-3,4):
    for k in range(-2,3):
      d=add(F0,sc(-1,one()),sc(-c,sub_q(Phi,a)))
      if k>0: pass
      e=eta_exps(d)
      if e[2] is not None:
        p=period(e[2],60)
        if p: print('F0-1-',c,'Phi(q^%d)'%a,e[0],e[1],p)
for a in (1,2):
  for c in range(-3,4):
      d=add(F0,sc(-1,one()),sc(-c,qmul_shift(sub_q(Psi,a),0)))
      e=eta_exps(d)
      if e[2] is not None:
        p=period(e[2],60)
        if p: print('F0-1-',c,'Psi(q^%d)'%a,e[0],e[1],p)
