import sys; sys.path.insert(0,'..')
from ecs import *
form=(5,17,68,1,0)
for sg in [tuple(map(int,a.split(","))) for a in sys.argv[1:]]:
  print("##### sign",sg)
  for tg in [(136,24),(24,136),(10,510),(510,10)]:
    search_II(f"F {tg}", *form, sg[0],sg[1], tg, R=12)
