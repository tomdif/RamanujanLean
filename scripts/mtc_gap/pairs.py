import series
series.N=160
from series import *
T={k:getattr(series,k)() for k in ['f0','f1','F0','F1','chi0','chi1','phi0','phi1','psi0','psi1']}
for k in list(T): T[k+'(-q)']=negq(T[k])
for k in ['f0','f1','F0','F1','psi0','psi1','phi0','phi1']: T[k+'(q2)']=sub_q(T[k],2)
names=list(T)
for i,a in enumerate(names):
  for b in names[i+1:]:
    for c in (-3,-2,-1,1,2,3):
      for k0 in (-2,-1,0,1,2):
        for sh in (0,1,-1):
          ta,tb=T[a],T[b]
          if sh==1: tb=qmul_shift(tb,1)
          if sh==-1: ta=qmul_shift(ta,1)
          d=add(ta,sc(c,tb),mono(0,k0))
          if not any(d): print('ZERO',a,c,b,k0); continue
          s,c0,e=eta_exps(d)
          if e is None: continue
          p=period(e,60)
          if p: print(a,'+',c,'q^%d'%sh if sh else '',b,'+',k0,' = ',c0,'q^%d'%s,'per',p[0])
