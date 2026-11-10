"""round 10: index-2 splits of Theta3(q^2) = QS(12,2,16) into C00=(24,4,32) and t^16 C11=(24,4,32,28,36)."""
import sys; sys.path.insert(0,'../round8')
import glue
from glue import sub, find_map
F=(12,2,16,0,0,0,0)
T0=(24,4,32,0,0,0,0); T1=(24,4,32,28,36,0,0)
for how,(M,rs) in glue.SPL.items():
    ps=[sub(F,M,r) for r in rs]
    print(how,ps)
    for (k,sg,G) in ps:
        for T,kt in ((T0,0),(T1,16)):
            m=find_map(G,T)
            for (MM,r,k2,sg2) in m[:2]:
                print('   ',G,'->',T,'map',MM,r,'const',k+k2,'sign',sg*sg2,'(want',kt,')')
