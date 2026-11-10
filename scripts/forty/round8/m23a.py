# search the det-23 analogue of E18 (Cao's (71)) for the degree-23 modular equation, series in t (q=t^2)
import numpy as np, itertools
P=400
def form(a,b,c,d,e,s1,s2):
    o=np.zeros(P,dtype=np.int64)
    R=40
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+2*b*x*y+c*y*y+d*x+e*y
            if 0<=E<P: o[E]+=(-1)**((s1*x+s2*y)%2)
            elif E<0: raise Exception('neg')
    return o
def th(f):  # f: list of (exp, coef) generator -> series in t
    pass
def ser_q_to_t(a):
    o=np.zeros(P,dtype=np.int64); o[0:P:2]=a[:(P+1)//2]; return o
import sys; sys.path.insert(0,'.')
import lib; lib.P=P//2+1
from lib import *
def T(a): return ser_q_to_t(a)
Q=23
phiphi1=T(mul(phi(1,-1),phi(Q,-1))); phiphi2=T(mul(phi(2,-1),phi(2*Q,-1)))
psipsi=T(mul(psi(1,-1),psi(Q,-1))); ff=T(mul(fm(1),fm(Q)))
def tm(k,a):
    o=np.zeros(P,dtype=np.int64); o[k:]=a[:P-k]; return o
# check M23 in t
lhs=phiphi2-phiphi1; rhs=2*tm(2,ff)+2*tm(6,psipsi)
print("M23 phi form:", np.array_equal(lhs[:P-10],rhs[:P-10]))
for (a,b,c) in [(4,1,6),(2,1,12),(1,0,23),(3,1,8),(6,1,4),(12,1,2),(4,-1,6),(3,-1,8),(8,1,3)]:
    for s in [(0,0),(1,0),(0,1),(1,1)]:
        F=form(a,b,c,0,0,*s)
        for nm,tg in [("phiphi1",phiphi1),("phiphi2",phiphi2),("phi2-2psi",phiphi2-2*tm(6,psipsi)),("phi2+2psi",phiphi2+2*tm(6,psipsi))]:
            if np.array_equal(F[:P-10],tg[:P-10]): print((a,b,c),s,nm)
# C: forms det 23 with linear terms equal to 2 f f
for (a,b,c) in [(4,1,6),(2,1,12),(3,1,8),(3,-1,8),(4,-1,6),(6,1,4),(8,1,3),(1,0,23),(2,-1,12)]:
  for d in range(-12,13):
    for e in range(-24,25):
      for s in [(0,0),(1,0),(0,1),(1,1)]:
        try: F=form(a,b,c,d,e,*s)
        except Exception: continue
        if np.array_equal(F[:P-10],2*ff[:P-10]): print("C",(a,b,c,d,e),s)
