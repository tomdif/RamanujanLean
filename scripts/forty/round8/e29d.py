import sys; sys.path.insert(0,'..')
import ecs
ecs.PREC=400
from ecs import *
for sg in [(1,0),(0,1)]:
  print("##### sign",sg)
  for tg in [(230,30),(30,230),(20,1380),(1380,20)]:
    search_II(f"F {tg}", 7,6,15,5,1,sg[0],sg[1], tg, R=12)
