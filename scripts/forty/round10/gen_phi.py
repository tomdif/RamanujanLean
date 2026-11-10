"""round 10: phi(q)^2 = phi(q^2)^2 + 4q psi(q^4)^2 as two orthogonal covers of x^2+y^2 (t = q)."""
import sys
sys.path.insert(0,'/Users/thomasdifiore/RamanujanTau/scripts/forty')
import ecs
from gen3 import gen_orth
out=[]
for tag,B in [("phA",(1,0,0,1)),("phB",(1,1,-1,1))]:
    s,M,ct=gen_orth(tag,(1,0,1,0,0,0,0),B); out.append(s); print(tag,M,ct,file=sys.stderr)
open('phi_gen.lean','w').write("\n".join(out))
