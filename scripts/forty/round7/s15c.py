import sys, itertools
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty')
from ecs import *
Ba=(0,5,-1,-1); Bb=(-1,3,-1,-2)
seen=0
for d,e in itertools.product(range(-9,10),repeat=2):
  for de in [(0,0),(1,0),(0,1),(1,1)]:
    try:
      ra=typeII(9,3,15,d,e,de[0],de[1],Ba); rb=typeII(9,3,15,d,e,de[0],de[1],Bb)
    except AssertionError: continue
    ca=canon_terms_local(ra[2]); cb=canon_terms_local(rb[2])
    sa=sorted(set(k[1][1] for k in ca)); sb=sorted(set(k[2][1] for k in cb))
    if 12 in sa and 6 in sa:
      print(d,e,de,"a-first:",sa,"b-second:",sb, [k[1] for k in ca][:2],[k[2] for k in cb][:2])
