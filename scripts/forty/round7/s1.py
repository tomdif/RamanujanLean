import sys
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty')
from ecs import *
import itertools
for d,e in itertools.product(range(-4,5),repeat=2):
  for de1,de2 in [(0,0),(1,0),(0,1),(1,1)]:
    try:
      r4=typeII(3,1,4,d,e,de1,de2,(0,-4,1,1))
      r3=typeII(3,1,4,d,e,de1,de2,(-1,1,0,-3))
    except AssertionError as ex: continue
    c4=canon_terms_local(r4[2]); c3=canon_terms_local(r3[2])
    if len(c3)==1 and all(t[1][2]==-1 for t in c4):
      print(d,e,de1,de2,"det3:",c3,"det4:",c4)
