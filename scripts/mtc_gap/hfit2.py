import series, itertools
series.N=70
from series import *
N=series.N
mults={'(q)':inf(1,1),'(q2;q2)':inf(2,2),'(q)^2/(q2;q2)':mul(mul(inf(1,1),inf(1,1)),inv(inf(2,2))),'(q2;q2)^2/(q)':mul(mul(inf(2,2),inf(2,2)),inv(inf(1,1))),
       '(q;q2)':inf(1,2),'(-q;q)':inv(inf(1,2)),'(q2;q2)(q;q2)':mul(inf(2,2),inf(1,2)) }
F={k:getattr(series,k)() for k in ['phi0','phi1','psi0','psi1','f0','F0']}
for k in list(F): F[k+'(-q)']=negq(F[k])
targets={}
for mk,mv in mults.items():
    for fk,fv in F.items():
        targets[(mk,fk)]=tuple(mul(mv,fv))
tset={}
for k,v in targets.items(): tset.setdefault(v,[]).append(k)
def H(A,B,C,D,E,sgn,half,K=1):
    r=[0]*N
    for n in range(0,40):
        for j in range(-n,n+1):
            if abs(K*j)>n: continue
            e2=A*n*n+B*n-C*j*j
            if e2%2: 
                if not half: continue
            if e2%2: continue
            e=e2//2
            s=(-1)**(j%2) if sgn==0 else (-1)**((n+j)%2)
            for ee,ss in ((e,1),(e+D*n+E,-1)):
                if 0<=ee<N: r[ee]+=s*ss
    return tuple(r)
hits=0
for K in (1,2,3):
 for A in range(1,13):
  for B in range(-4,13):
    for C in range(1,30):
      for D in range(1,7):
        for E in range(0,6):
          for sgn in (0,1):
            h=H(A,B,C,D,E,sgn,False,K)
            if h in tset:
                print('HIT K',K,A,B,C,D,E,sgn,tset[h],flush=True); hits+=1
print('hits',hits)
