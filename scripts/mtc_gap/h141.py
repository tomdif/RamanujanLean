import series, itertools
series.N=90
from series import *
N=series.N
def f141(sx,a,sy,b,d):
    r=[0]*N
    for rr in range(-40,41):
        for ss in range(-40,41):
            if (rr>=0)!=(ss>=0): continue
            E=d*(rr*(rr-1)//2+4*rr*ss+ss*(ss-1)//2)+a*rr+b*ss
            if 0<=E<N:
                sg=1 if rr>=0 else -1
                r[E]+=sg*(-1)**((rr+ss)%2)*(sx**(rr%2))*(sy**(ss%2))
            elif E<0: return None
    return r
F={}
for k in ['phi0','phi1','psi0','psi1','chi0','chi1','F0','F1']:
    v=getattr(series,k)()
    for m in (1,2,3,4):
        F[(k,m,1)]=sub_q(v,m); F[(k,m,-1)]=sub_q(negq(v),m)
hits=0
for d in range(1,7):
  for a in range(-2*d,6*d+1):
    for b in range(a,6*d+1):
      for sx,sy in itertools.product((1,-1),repeat=2):
        f=f141(sx,a,sy,b,d)
        if f is None or not any(f): continue
        for key,v in F.items():
            if abs(v[0])!=1: continue
            P=mul(f,inv(v))
            if not any(P): continue
            s,c0,e=eta_exps(P)
            if e is None: continue
            p=period(e,60)
            if p: print('HIT d',d,'x',sx,'Q^',a,'y',sy,'Q^',b,'->',key,'mult',c0,'Q^',s,'per',p[0],flush=True); hits+=1
print('hits',hits)
