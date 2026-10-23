import series as S
from series import *
S.N=N=160
import series
series.N=160
T={k:getattr(series,k)() for k in ['f0','f1','F0','F1','chi0','chi1','phi0','phi1','psi0','psi1']}
T['phi0(-q)']=negq(T['phi0']); T['phi1(-q)']=negq(T['phi1'])
X={'Phi':RPhi(),'Psi':RPsi()}
print('Phi',X['Phi'][:20]); print('Psi',X['Psi'][:20])
print('chi0',T['chi0'][:20])
hits=[]
for tn,t in T.items():
  for xn,x in X.items():
    for a in (1,2,5):
      xa=sub_q(x,a)
      for b in range(-3,4):
        for c in range(-4,5):
          if c==0: continue
          # t*q^? : allow t shifted so negative b means shift t up
          if b>=0: d=add(t, sc(-c, qmul_shift(xa,b)))
          else: d=add(qmul_shift(t,-b), sc(-c,xa))
          if not any(d): continue
          s,c0,e=eta_exps(d)
          if e is None: continue
          p=period(e,60)
          if p: hits.append((tn,xn,a,b,c,s,c0,p)); print(tn,'-',c,'q^',b,xn+'(q^%d)'%a,'= ',c0,'q^%d'%s,'prod period',p[0],p[1])
