"""round 9: maps + Lean pieces for (E): theta(2,1,6) - theta(3,1,4) = 2q^2 f(-q)f(-q^47), in t (q = t^2):
A=(4,1,12), B=(6,1,8), C=(3,1,16,1,16) sign (-1)^x;  A - B = t^4 C."""
import sys
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty')
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty/round8')
import glue
import ecs
ecs.theta_series.__defaults__=(ecs.PREC,4000)
from gen3 import gen_orth, gen_sub, sub
A=(4,1,12,0,0,0,0); B=(6,1,8,0,0,0,0); C=(3,1,16,1,16,1,0)
for tag,F,Bm in [("47a",A,(2,0,0,1)),("47b",B,(1,1,-1,1)),("47c",C,(2,0,0,1))]:
    print(tag,[sub(F,Bm,(1,0),i) for i in (0,1)],file=sys.stderr)
pairs=[((16,2,12,0,0,0,0),(12,-2,16,0,0,0,0)),((16,2,12,16,2,0,0),(12,2,16,2,16,0,0)),((12,-2,16,10,14,0,0),(12,2,16,14,18,0,0))]
for G1,G2 in pairs:
    print(G1,G2,glue.find_map(G1,G2)[:4],file=sys.stderr)
out=[]
for tag,F,Bm in [("47a",A,(2,0,0,1)),("47b",B,(1,1,-1,1)),("47c",C,(2,0,0,1))]:
    s,p=gen_sub(tag,F,Bm,(1,0),[0,1]); out.append(s); print(tag,p,file=sys.stderr)
s,p=gen_sub("47r",(16,2,12,0,0,0,0),(0,1,-1,0),(0,0),[0]); out.append(s); print(p,file=sys.stderr)
s,p=gen_sub("47s",(16,2,12,16,2,0,0),(0,1,1,0),(0,0),[0]); out.append(s); print(p,file=sys.stderr)
s,p=gen_sub("47t",(12,-2,16,10,14,0,0),(-1,0,0,1),(-1,0),[1]); out.append(s); print(p,file=sys.stderr)
for tag,F,Bm in [("A47",A,(1,-1,0,4)),("B47",B,(1,-1,0,6)),("C47",C,(1,-1,0,3))]:
    s,M,ct=gen_orth(tag,F,Bm); out.append(s); print(tag,M,ct,file=sys.stderr)
open('e47_gen.lean','w').write("\n".join(out))
