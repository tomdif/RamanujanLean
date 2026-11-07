import series, itertools
series.N=80
from series import *
N=series.N
F={k:getattr(series,k)() for k in ['phi0','phi1','psi0','psi1','chi0','chi1']}
for k in list(F): F[k+'(-q)']=negq(F[k])
def lam(A,B,C,D,eps):
    r=[0]*N
    for n in range(-30,31):
        e2=A*n*n+B*n
        if e2%2: return None
        e=e2//2
        w=C*n+D
        s=(-1)**(n%2) if eps==0 else 1
        if w>0:
            for k in range(0,N):
                ee=e+w*k
                if ee>=N: break
                if ee>=0: r[ee]+=s
        elif w<0:
            for k in range(1,N):
                ee=e-(-w)*k

            # 1/(1-x) = -x^{-1}/(1-x^{-1}) = -sum_{k>=1} x^{-k}; x = q^w with w<0: x^{-k}=q^{-wk}
            for k in range(1,N):
                ee=e+(-w)*k
                if ee>=N: break
                if ee>=0: r[ee]-=s
        else: return None
    return r
hits=0
for A in range(1,31):
  for B in range(-A,A+1):
    for C in range(1,16):
      for D in range(1,C):
        for eps in (0,1):
          L=lam(A,B,C,D,eps)
          if L is None or not any(L): continue
          for k,v in F.items():
            if abs(v[0])!=1: continue
            P=mul(L,inv(v))
            if not any(P): continue
            s,c0,e=eta_exps(P)
            if e is None: continue
            p=period(e,60)
            if p: print('HIT',A,B,C,D,eps,k,c0,'q^',s,'per',p[0],flush=True); hits+=1
print('hits',hits)
