"""round 9: search a gluing for (**):  t^4 C|_{E = 0 mod 4} + t^16 C(t^4) = QS(4,2,48) - QS(8,2,24)   (t^2 = q)
C = sum (-1)^x t^{3x^2+2xy+16y^2+x+16y}; terms fully refined mod N_term, pieces matched by series."""
import numpy as np, itertools
from collections import defaultdict
from fractions import Fraction as Fr
P=2400; R=70
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1)); xs=xs.ravel(); ys=ys.ravel()
def ser(F,k0):
    a,b,c,d,e=F
    E=a*xs*xs+2*b*xs*ys+c*ys*ys+d*xs+e*ys+k0
    assert E.min()>=0
    m=E<P
    return np.bincount(E[m],minlength=P).astype(np.int64)[:P]
def Cval(x,y): return 3*x*x+2*x*y+16*y*y+x+16*y
terms=[('C4',4,(3,1,16,1,16),lambda x,y: ((-1)**(x%2)) if Cval(x,y)%4==0 else 0,4),
       ('C16',16,(12,4,64,4,64),lambda x,y: (-1)**(x%2),2),
       ('T1',0,(4,2,48,0,0),lambda x,y:-1,1),
       ('T2',0,(8,2,24,0,0),lambda x,y:1,1)]
# check identity
def full(F,sh,w,per):
    tot=np.zeros(P,dtype=np.int64)
    for r1 in range(per):
        for r2 in range(per):
            wt=w(r1,r2)
            if wt==0: continue
            k,G=subst(F,per,(r1,r2)); s=ser(G,k)
            tot[sh:]+=wt*s[:P-sh]
    return tot
def subst(F,N,r):
    a,b,c,d,e=F; r1,r2=r
    const=a*r1*r1+2*b*r1*r2+c*r2*r2+d*r1+e*r2
    gx=2*a*r1+2*b*r2+d; gy=2*b*r1+2*c*r2+e
    return const,(a*N*N,b*N*N,c*N*N,gx*N,gy*N)
tot=sum(full(F,sh,w,per) for _,sh,F,w,per in terms)
print("identity (**):", not tot[:P-800].any())
cache={}
def pieces(i,N):
    if (i,N) in cache: return cache[(i,N)]
    nm,sh,F,w,per=terms[i]
    out=[]
    for r1 in range(N):
        for r2 in range(N):
            wt=w(r1,r2)
            if wt==0: continue
            k,G=subst(F,N,(r1,r2)); s=ser(G,k)
            nz=np.nonzero(s[:P-900])[0]
            if len(nz)==0: continue
            k0=nz[0]; lead=int(s[k0])
            out.append((sh+k0,tuple(Fr(int(v),lead) for v in s[k0:k0+800]),wt*lead,(nm,N,(r1,r2),G,sh+k)))
    cache[(i,N)]=out; return out
levels={0:[4,8],1:[2,4,8],2:[1,2,4,8],3:[1,2,4,8]}
for combo in itertools.product(*[levels[i] for i in range(4)]):
    grp=defaultdict(int); info=defaultdict(list)
    for i,N in enumerate(combo):
        for (k,shape,c,inf) in pieces(i,N): grp[(k,shape)]+=c; info[(k,shape)].append(inf)
    bad=sum(1 for v in grp.values() if v)
    print(combo,'groups',len(grp),'unbalanced',bad)
    if bad==0:
        for key,v in info.items(): print('  ',key[0],v)
        break
