"""Structure constants of V = Z[z,1/z]<1,g2,g3,g4,g6>:  J_b * J_r = sum_t s(b,r,t) J_t  (b,r in 1..4)."""
import json
from gordon_matrix import Ctx
from qs import val_p
ctx = Ctx(600)
names = ["1", "g2", "g3", "g4", "g6"]
out = {}
for b in range(1, 5):
    for r in range(b, 5):
        f = ctx.g[b] * ctx.g[r]
        e = ctx.express(f)
        out[f"{b},{r}"] = {str(k): int(v) for k, v in e.items()}
        s = " + ".join(f"{int(v)}*J{k}" for k, v in sorted(e.items()))
        print(f"{names[b]}*{names[r]} = {s}")
json.dump(out, open("structure.json", "w"))
