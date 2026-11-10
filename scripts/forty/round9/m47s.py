"""round 9: is 2 q^k f(-q)f(-q^47) a single QS of a det-47 binary form with linear terms and a sign? (series in q)"""
import sys; sys.path.insert(0,'../round8')
import numpy as np
import lib; lib.P=400
from lib import *
P=400
ff=mul(fm(1),fm(47))
def form(a,b,c,d,e,s1,s2,R=30):
    o=np.zeros(P,dtype=np.int64); mn=10**9
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+2*b*x*y+c*y*y+d*x+e*y
            mn=min(mn,E)
            if 0<=E<P: o[E]+=(-1)**((s1*x+s2*y)%2)
    return o,mn
forms=[]
for a in range(1,48):
    for b in range(0,a):
        if (47+b*b)%a==0:
            c=(47+b*b)//a
            if c>=a: forms.append((a,b,c))
print(forms)
found=0
for (a,b,c) in forms:
  for (a_,b_,c_) in [(a,b,c),(a,-b,c)]:
    for d in range(-2*a,2*a+1):
      for e in range(-2*c,2*c+1):
        for s in [(0,0),(1,0),(0,1),(1,1)]:
          F,mn=form(a_,b_,c_,d,e,*s)
          if mn<0: continue
          # strip leading zeros/shift
          nz=np.nonzero(F)[0]
          if len(nz)==0: continue
          k=nz[0]
          G=F[k:]
          for cc in (1,2,-1,-2):
            if np.array_equal(G[:300], cc*ff[:300]): print("FOUND",(a_,b_,c_,d,e),s,'shift',k,'coef',cc); found+=1
print('done',found)
