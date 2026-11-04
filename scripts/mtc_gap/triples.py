import series, itertools
series.N=160
from series import *
T={k:getattr(series,k)() for k in ['f0','f1','F0','F1','chi0','chi1','phi0','phi1','psi0','psi1']}
for k in list(T): T[k+'(-q)']=negq(T[k])
for k in ['f0','f1','F0','F1','psi0','psi1','phi0','phi1','chi0','chi1']: T[k+'(q2)']=sub_q(T[k],2)
names=list(T)
target=[n for n in names if n.startswith('chi0')]
others=[n for n in names if not n.startswith('chi')]
cs=(-3,-2,-1,1,2,3)
found=0
for a in target:
  for b,c in itertools.combinations(others,2):
    for cb in cs:
      for cc in cs:
        for k0 in (-2,-1,0,1,2,3):
          d=add(add(T[a],sc(cb,T[b])),add(sc(cc,T[c]),mono(0,k0)))
          if not any(d): print("ZERO",a,cb,b,cc,c,k0); continue
          s,c0,e=eta_exps(d)
          if e is None: continue
          p=period(e,60)
          if p:
            print(a,'+',cb,b,'+',cc,c,'+',k0,'=',c0,'q^%d'%s,'per',p[0]); found+=1
print('found',found)
