# search a QS gluing for (5.18): X1 - T2 - T3 - T5 - T4 = 0 (q-level, integral forms)
import itertools, numpy as np
from fractions import Fraction as Fr
from collections import defaultdict
P=700
def form(F,k0=0,R=50):
    a,b,c,d,e,s1,s2=F
    o=np.zeros(P,dtype=np.int64)
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+2*b*x*y+c*y*y+d*x+e*y+k0
            if E<P:
                assert E>=0,(F,k0,x,y)
                o[E]+=(-1)**((s1*x+s2*y)%2)
    return o
def sub(F,M,r):
    a,b,c,d,e,s1,s2=F; (m11,m12),(m21,m22)=M; r1,r2=r
    Qf=lambda x,y: a*x*x+2*b*x*y+c*y*y
    A=Qf(m11,m21); C=Qf(m12,m22); B=a*m11*m12+b*(m11*m22+m12*m21)+c*m21*m22
    gx=2*a*r1+2*b*r2+d; gy=2*b*r1+2*c*r2+e
    return Qf(r1,r2)+d*r1+e*r2, (-1)**((s1*r1+s2*r2)%2), (A,B,C,gx*m11+gy*m21,gx*m12+gy*m22,(s1*m11+s2*m21)%2,(s1*m12+s2*m22)%2)
SPL={None:None,
 'x2':([[2,0],[0,1]],[(0,0),(1,0)]), 'y2':([[1,0],[0,2]],[(0,0),(0,1)]), 'xy2':([[1,1],[-1,1]],[(0,0),(1,0)]),
 'x3':([[3,0],[0,1]],[(0,0),(1,0),(2,0)]), 'y3':([[1,0],[0,3]],[(0,0),(0,1),(0,2)]),
 'xy3':([[1,1],[-1,2]],[(0,0),(1,0),(2,0)]), 'xmy3':([[1,1],[1,-2]],[(0,0),(1,0),(2,0)])}
# terms: (coef, shift, form)
terms={
 'X1':(Fr(1),0,(2,1,24,0,0,0,0)),
 'T2':(Fr(-1),0,(4,2,48,0,0,0,0)),
 'T3':(Fr(-1,2),12,(1,0,47,1,47,0,0)),
 'T5':(Fr(-2),8,(6,0,282,-2,-94,1,1)),
 'T4a':(Fr(-1),2,(72,3,6,-24,-1,0,0)),
 'T4b':(Fr(-1),2,(72,3,6,-24,-1,0,1)),
 'T4c':(Fr(1),3,(72,3,6,-21,5,0,0)),
 'T4d':(Fr(-1),3,(72,3,6,-21,5,1,1)),
}
# check identity numerically
tot=np.zeros(P,dtype=object)
for nm,(c,k,F) in terms.items():
    s=form(F,k); tot=tot+np.array([c*int(v) for v in s],dtype=object)
print("identity holds:", all(v==0 for v in tot[:600]))
def sig(s):
    nz=np.nonzero(s[:600])[0]
    if len(nz)==0: return None
    k=nz[0]; c=int(s[k]); return (k, c, tuple(Fr(int(v),c) for v in s[k:k+400]))
pieces={}
for nm,(c,k,F) in terms.items():
    for opt,sp in SPL.items():
        if sp is None: lst=[(0,1,F)]
        else:
            M,rs=sp; lst=[sub(F,M,r) for r in rs]
        out=[]
        for (k0,sg,G) in lst:
            s=form(G,k+k0)
            g=sig(s)
            if g is None: continue
            out.append((c*sg*g[1], g[0], g[2], G, k+k0))
        pieces[(nm,opt)]=out
names=list(terms)
opts=list(SPL)
cnt=0
for choice in itertools.product(opts,repeat=len(names)):
    grp=defaultdict(Fr)
    for nm,o in zip(names,choice):
        for (c,k0,shape,G,kk) in pieces[(nm,o)]:
            grp[(k0,shape)]+=c
    if all(v==0 for v in grp.values()):
        print("FOUND",dict(zip(names,choice))); cnt+=1
        if cnt>5: break
print("done")
