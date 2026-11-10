"""round 9: t-scale (q = t^2) search: t^k * c * f(-t^2)f(-t^94) as one det-47 form a x^2+2bxy+c y^2+dx+ey with sign."""
import sys; sys.path.insert(0,'../round8')
import numpy as np
import lib; lib.P=300
from lib import *
P=600
ffq=mul(fm(1),fm(47))
ff=np.zeros(P,dtype=np.int64); ff[0:P:2]=ffq[:P//2]
R=40
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1))
xs=xs.ravel(); ys=ys.ravel()
forms=[(1,0,47),(2,1,24),(3,1,16),(4,1,12),(6,1,8),(7,3,8)]
found=0
for (a,b0,c) in forms:
  for b in {b0,-b0}:
    Q=a*xs*xs+2*b*xs*ys+c*ys*ys
    for d in range(-a,a+1):
      for e in range(-c,c+1):
        E=Q+d*xs+e*ys
        if E.min()<0: continue
        m=E<P
        for s1 in (0,1):
          for s2 in (0,1):
            w=np.where(((s1*xs+s2*ys)%2)==0,1,-1)
            F=np.bincount(E[m],weights=w[m],minlength=P).astype(np.int64)[:P]
            nz=np.nonzero(F)[0]
            if len(nz)==0: continue
            k=nz[0]; G=F[k:k+400]
            for cc in (1,2,-1,-2,4,-4):
              if np.array_equal(G, cc*ff[:400]): print("FOUND",(a,b,c,d,e),(s1,s2),'t-shift',k,'coef',cc); found+=1
print('done',found)
