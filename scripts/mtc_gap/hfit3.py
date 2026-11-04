import series, itertools
series.N=60
from series import *
N=series.N
mults={'(q)':inf(1,1),'(q2;q2)':inf(2,2),'(q)^2/(q2;q2)':mul(mul(inf(1,1),inf(1,1)),inv(inf(2,2))),'(q2;q2)^2/(q)':mul(mul(inf(2,2),inf(2,2)),inv(inf(1,1))),'(q;q2)':inf(1,2),'1/(q;q2)':inv(inf(1,2))}
F={k:getattr(series,k)() for k in ['phi0','phi1','psi0','psi1','F0','F1','chi0','chi1']}
for k in list(F): F[k+'(-q)']=negq(F[k])
tset={}
for mk,mv in mults.items():
    for fk,fv in F.items():
        tset.setdefault(tuple(mul(mv,fv)),[]).append((mk,fk))
def H(A,B,C,G,D,E,sgn,K):
    r=[0]*N
    for n in range(0,30):
        if (A*n*n+B*n)//2 > N+ C*n*n: break
        for j in range(-n,n+1):
            if abs(K*j)>n: continue
            e2=A*n*n+B*n-(C*j*j+G*j)
            if e2%2: return None
            e=e2//2
            s=(-1)**(j%2) if sgn==0 else ((-1)**((n+j)%2) if sgn==1 else (-1)**(n%2))
            for ee,ss in ((e,1),(e+D*n+E,-1)):
                if 0<=ee<N: r[ee]+=s*ss
    return tuple(r)
hits=0
for K in (1,2,3):
 for A in range(1,13):
  for B in range(-3,13):
   for C in range(1,7):
    for G in range(-3,4):
     for D in range(1,8):
      for E in range(0,6):
       for sgn in (0,1,2):
        h=H(A,B,C,G,D,E,sgn,K)
        if h is not None and h in tset:
            print('HIT K',K,'A B',A,B,'C G',C,G,'D E',D,E,'sgn',sgn,tset[h],flush=True); hits+=1
print('hits',hits)
