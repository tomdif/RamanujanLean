"""round 9: gluing search for (R2) in t (q=t^2):
QS(12,2,16) - QS(16,4,48) - 2t^12 QS(16,0,752,-4,-188) - 2t^108 QS(16,0,752,-12,-564) = 0"""
import sys; sys.path.insert(0,'../round8')
import numpy as np, itertools
from collections import defaultdict
import glue
from glue import sub, norm
P=glue.P=1600
R=60
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1)); xs=xs.ravel(); ys=ys.ravel()
def form(a,b,c,d,e,s1,s2,k0=0):
    E=a*xs*xs+2*b*xs*ys+c*ys*ys+d*xs+e*ys+k0
    assert E.min()>=0
    m=E<P; w=np.where(((s1*xs+s2*ys)%2)==0,1,-1)
    return np.bincount(E[m],weights=w[m],minlength=P).astype(np.int64)[:P]
T=[((12,2,16,0,0,0,0),1,0),((16,4,48,0,0,0,0),-1,0),((16,0,752,-4,-188,0,0),-2,12),((16,0,752,-12,-564,0,0),-2,108)]
tot=np.zeros(P,dtype=np.int64)
for F,c,sh in T: tot[sh:]+=c*form(*F)[:P-sh]
print("R2 identity:", not tot[:P-300].any())
SPL={None:None,'x':([[2,0],[0,1]],[(0,0),(1,0)]),'y':([[1,0],[0,2]],[(0,0),(0,1)]),'xy':([[1,1],[-1,1]],[(0,0),(1,0)]),
     'x4':([[4,0],[0,1]],[(0,0),(1,0),(2,0),(3,0)]),'y4':([[1,0],[0,4]],[(0,0),(0,1),(0,2),(0,3)]),'x2y2':([[2,0],[0,2]],[(0,0),(1,0),(0,1),(1,1)]),
     'xy4':([[1,1],[-1,3]],[(0,0),(1,0),(2,0),(3,0)]),'xmy4':([[1,1],[1,-3]],[(0,0),(1,0),(2,0),(3,0)])}
cache={}
def items(i,h):
    F,co,sh=T[i]
    if (i,h) not in cache:
        out=[]
        ps=[(0,1,F)] if h is None else [sub(F,SPL[h][0],r) for r in SPL[h][1]]
        for (k,sg,G) in ps:
            s=form(*G,k0=k); n=norm(s)
            if n is not None: out.append((sh+n[0],co*sg*int(n[1]),n[2][:900],G,k))
        cache[(i,h)]=out
    return cache[(i,h)]
found=0
for hs in itertools.product(list(SPL),repeat=4):
    grp=defaultdict(int)
    for i,h in enumerate(hs):
        for (k,c,shape,G,kk) in items(i,h): grp[(k,shape)]+=c
    if all(v==0 for v in grp.values()):
        print("FOUND",hs); found+=1
        for i,h in enumerate(hs):
            for it in items(i,h): print('   ',i,h,it[0],it[1],it[3],it[4])
        if found>=2: break
print('done',found)
