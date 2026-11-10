import sys, itertools
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty')
from ecs import *
Ba=(0,5,-1,-1); Bb=(-1,3,-1,-2)
for d,e in itertools.product(range(-15,16),repeat=2):
  for de in [(0,0),(1,0),(0,1),(1,1)]:
    if (d+e)%2==1 and False: pass
    try:
      ra=typeII(9,3,15,d,e,de[0],de[1],Ba); rb=typeII(9,3,15,d,e,de[0],de[1],Bb)
    except AssertionError: continue
    ca=canon_terms_local(ra[2]); cb=canon_terms_local(rb[2])
    sa=set(k[1][1] for k in ca); sb=set(k[2][1] for k in cb)
    if ca and cb and sa<= {12,6} and sb<={84,42} and all(k[1][2]==1 and k[2][2]==1 for k in list(ca)+list(cb)):
      print(d,e,de,ra[3],rb[3]); print("  a:",ca); print("  b:",cb)
