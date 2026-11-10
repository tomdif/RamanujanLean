"""round 9: (5.18) in t (q = t^2) as weighted binary-form sums; full refinement mod N and matching of pieces."""
import numpy as np, itertools, sys
from collections import defaultdict
from fractions import Fraction as Fr
P=1400
R=60
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1)); xs=xs.ravel(); ys=ys.ravel()
def ser(F,k0=0,w=None):
    a,b,c,d,e=F
    E=a*xs*xs+2*b*xs*ys+c*ys*ys+d*xs+e*ys+k0
    assert E.min()>=0
    m=E<P
    ww=np.ones(len(xs),dtype=np.int64) if w is None else w
    return np.bincount(E[m],weights=ww[m],minlength=P).astype(np.int64)[:P]
C=(3,1,16,1,16)
def wT4(x,y):
    if x%4==0: return 1
    if x%4==1 and y%2==0: return -1
    if x%4==3 and y%2==1: return -1
    return 0
terms=[ # (name, coef, shift, form, weight(x,y) or None, period)
 ('X1',Fr(1),0,(4,2,48,0,0),None,1),
 ('T2',Fr(-1),0,(8,4,96,0,0),None,1),
 ('T3',Fr(-1,2),0,(2,1,24,0,0),lambda x,y: 1 if y%2 else 0,2),
 ('T4',Fr(-1),4,C,wT4,4),
 ('T5',Fr(-1),16,(12,4,64,4,64),lambda x,y: -1 if x%2 else 1,2),
]
tot=np.zeros(P,dtype=object)
for nm,co,sh,F,w,per in terms:
    W=None if w is None else np.array([w(x,y) for x,y in zip(xs,ys)],dtype=np.int64)
    s=ser(F,0,W); tot[sh:]=tot[sh:]+np.array([co*int(v) for v in s[:P-sh]],dtype=object)
print("identity (5.18) in t:", all(v==0 for v in tot[:P-200]))
def subst(F,N,r):
    a,b,c,d,e=F; r1,r2=r
    const=a*r1*r1+2*b*r1*r2+c*r2*r2+d*r1+e*r2
    gx=2*a*r1+2*b*r2+d; gy=2*b*r1+2*c*r2+e
    return const,(a*N*N,b*N*N,c*N*N,gx*N,gy*N)
def run(N):
    grp=defaultdict(Fr); info=defaultdict(list)
    for nm,co,sh,F,w,per in terms:
        assert N%per==0
        for r1 in range(N):
            for r2 in range(N):
                wt=1 if w is None else w(r1,r2)
                if wt==0: continue
                k,G=subst(F,N,(r1,r2))
                s=ser(G,k)
                nz=np.nonzero(s[:P-300])[0]
                if len(nz)==0: continue
                k0=nz[0]; lead=int(s[k0])
                key=(sh+k0,tuple(int(v) for v in s[k0:k0+500]//lead) if False else tuple(Fr(int(v),lead) for v in s[k0:k0+500]))
                grp[key]+=co*wt*lead; info[key].append((nm,(r1,r2),co*wt*lead,G,sh+k))
    bad=[k for k,v in grp.items() if v!=0]
    print("N",N,"groups",len(grp),"unbalanced",len(bad))
    return grp,info,bad
for N in (4,8):
    grp,info,bad=run(N)
    if not bad:
        print("TAUTOLOGICAL at N",N); break
    else:
        for k in bad[:6]: print('  ',k[0],grp[k],[(i[0],i[1],i[2]) for i in info[k]])
