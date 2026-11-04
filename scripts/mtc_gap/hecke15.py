import series, itertools
series.N=120
from series import *
N=series.N
def fabc(a,b,c,ex,sx,ey,sy,scale):
    # f_{a,b,c}(sx q^ex, sy q^ey; q^scale) with q-exponents in units of 1/2 -> use doubled exponents: all exps integer after *2
    r=[0]*N
    for rr in range(-40,40):
        for ss in range(-40,40):
            if (rr>=0)!=(ss>=0): continue
            sg=1 if rr>=0 else -1
            e2=scale*(a*rr*(rr-1)+2*b*rr*ss+c*ss*(ss-1))//1  # doubled? a C(r,2)*2 = a r(r-1)
            # total exponent (doubled): scale*(a r(r-1)/2 + b r s + c s(s-1)/2)*2 = scale*(a r(r-1)+2b r s + c s(s-1))
            E=e2+2*(ex*rr+ey*ss)
            if E%2: continue
            E//=2
            if 0<=E<N:
                r[E]+=sg*(-1)**((rr+ss)%2)*(sx**(rr%2))*(sy**(ss%2))
    return r
T={k:getattr(series,k)() for k in ['phi0','phi1','psi0','psi1']}
for k in list(T): T[k+'(-q)']=negq(T[k])
for k in ['phi0','phi1','psi0','psi1']: T[k+'(q2)']=sub_q(T[k],2)
forms=[(1,4,1),(2,5,5),(1,5,10),(3,6,7),(2,7,17)]
for (a,b,c) in forms:
  for scale in (1,2):
    for ex in range(0,8):
      for ey in range(0,8):
        for sx,sy in itertools.product((1,-1),repeat=2):
          F=fabc(a,b,c,ex,sx,ey,sy,scale)
          if not any(F): continue
          for k,v in T.items():
            # F = P * v  -> P = F / v
            if v[0]==0: continue
            try:
              P=mul(F,inv(v)) if abs(v[0])==1 else None
            except AssertionError: continue
            if P is None or not any(P): continue
            s,c0,e=eta_exps(P)
            if e is None: continue
            p=period(e,40)
            if p: print((a,b,c),'scale',scale,'x',sx,'q^',ex/2,'y',sy,'q^',ey/2,'->',k,'P:',c0,'q^',s,'per',p[0],flush=True)
