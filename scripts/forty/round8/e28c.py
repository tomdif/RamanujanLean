import sys; sys.path.insert(0,'..')
from ecs import *
form=(5,17,68,1,0)
for sg in [tuple(map(int,a.split(","))) for a in sys.argv[1:]]:
  print("##### sign",sg)
  for B in [(1,17,0,-5),(-1,-17,0,5),(1,-17,0,5)]:
    for r in [(1,0),(0,1)]:
      for lo in range(-5,1):
        res=find_ecs(B,r,None,[lo])
        if res:
          show(f"F {B} {r} {lo}", typeII(*form,sg[0],sg[1],B,r,None,[lo])); break
      else: continue
      break
  show("det4", typeII(*form,sg[0],sg[1],(0,-4,1,1),(1,0),None,[-2]))
