"""Generate RamanujanTau/Forty/E29a.lean pieces: the degree-23 modular equation by QS gluing (det-23 analogue of E18)."""
import sys
sys.path.insert(0, '/Users/thomasdifiore/RamanujanTau/scripts/forty')
from gen3 import gen_orth, gen_sub
out = []
# splits
s, p = gen_sub("23a", (4,1,6,0,0,1,1), (1,1,-1,1), (1,0), [0,1]); out.append(s); print(p, file=sys.stderr)
s, p = gen_sub("23b", (2,1,12,0,0,1,0), (2,0,0,1), (1,0), [0,1]); out.append(s); print(p, file=sys.stderr)
s, p = gen_sub("23c", (3,1,8,1,8,1,0), (2,0,0,1), (1,0), [0,1]); out.append(s); print(p, file=sys.stderr)
# unimodular maps
s, p = gen_sub("23r", (8,-2,12,0,0,0,0), (-1,0,0,1), (0,0), [0]); out.append(s); print(p, file=sys.stderr)
s, p = gen_sub("23s", (8,-2,12,6,10,0,0), (0,-1,1,0), (-1,0), [1]); out.append(s); print(p, file=sys.stderr)
s, p = gen_sub("23t", (8,2,12,8,2,0,0), (0,1,1,0), (0,0), [0]); out.append(s); print(p, file=sys.stderr)
# orthogonal covers
for tag, form, B in [("A23", (4,1,6,0,0,1,1), (1,-1,0,4)), ("B23", (2,1,12,0,0,1,0), (1,-1,0,2)), ("C23", (3,1,8,1,8,1,0), (1,-1,0,3))]:
    s, M, ct = gen_orth(tag, form, B); out.append(s); print(tag, M, ct, file=sys.stderr)
print("\n".join(out))
