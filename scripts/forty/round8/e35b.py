import sys; sys.path.insert(0,'..')
from ecs import *
form=(10,3,15,12,13)
for sg in [tuple(map(int,a.split(","))) for a in sys.argv[1:]]:
  print("##### sign",sg)
  for tg in [(470,30),(30,470),(20,2820),(2820,20)]:
    search_II(f"F {tg}", *form, sg[0],sg[1], tg, R=12)
