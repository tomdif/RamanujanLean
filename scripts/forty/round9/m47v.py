"""round 9: QS gluing search for theta(2,1,6) - theta(3,1,4) = 2 q^2 f(-q)f(-q^47), in t (q=t^2):
A=(4,1,12), B=(6,1,8), C=(3,1,16,1,16) sign (-1)^x; target A - B - t^4 C = 0."""
import sys; sys.path.insert(0,'../round8')
import numpy as np, itertools
from collections import defaultdict
import glue
from glue import sub, norm
P=glue.P
R=40
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1)); xs=xs.ravel(); ys=ys.ravel()
def form(a,b,c,d,e,s1,s2,k0=0):
    E=a*xs*xs+2*b*xs*ys+c*ys*ys+d*xs+e*ys+k0
    assert E.min()>=0
    m=E<P; w=np.where(((s1*xs+s2*ys)%2)==0,1,-1)
    return np.bincount(E[m],weights=w[m],minlength=P).astype(np.int64)[:P]
A=(4,1,12,0,0,0,0); B=(6,1,8,0,0,0,0); C=(3,1,16,1,16,1,0)
tot=form(*A)-form(*B)-np.concatenate([np.zeros(4,dtype=np.int64),form(*C)[:P-4]])
print("identity:", not tot[:P-50].any())
SPL={None:None,'x':([[2,0],[0,1]],[(0,0),(1,0)]),'y':([[1,0],[0,2]],[(0,0),(0,1)]),'xy':([[1,1],[-1,1]],[(0,0),(1,0)]),
     'x3':([[3,0],[0,1]],[(0,0),(1,0),(2,0)]),'y3':([[1,0],[0,3]],[(0,0),(0,1),(0,2)]),
     'xy3':([[1,1],[-1,2]],[(0,0),(1,0),(2,0)]),'xmy3':([[1,1],[1,-2]],[(0,0),(1,0),(2,0)]),
     'x4':([[4,0],[0,1]],[(0,0),(1,0),(2,0),(3,0)]),'y4':([[1,0],[0,4]],[(0,0),(0,1),(0,2),(0,3)]),
     'x2y2':([[2,0],[0,2]],[(0,0),(1,0),(0,1),(1,1)])}
def pieces(F,how):
    if how is None: return [(0,1,F)]
    M,rs=SPL[how]; return [sub(F,M,r) for r in rs]
cache={}
def items_of(F,h,co,sh):
    key=(F,h)
    if key not in cache:
        out=[]
        for (k,sg,G) in pieces(F,h):
            s=form(*G,k0=k); n=norm(s)
            out.append(None if n is None else (sg*int(n[1]),n[0],n[2][:400],G))
        cache[key]=out
    return [(sh,co*x[0],x[1],x[2],x[3]) for x in cache[key] if x is not None]
for ha,hb,hc in itertools.product(list(SPL),repeat=3):
    items=items_of(A,ha,1,0)+items_of(B,hb,-1,0)+items_of(C,hc,-1,4)
    grp=defaultdict(int)
    for (k,c,k0,shape,G) in items: grp[(k+k0,shape)]+=c
    if all(v==0 for v in grp.values()):
        print("FOUND",ha,hb,hc)
        for it in items: print("   ",it[0],it[1],it[2],it[4])
print('done')
