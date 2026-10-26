"""Smaller base windows: sizes + Gordon bound on base + inductive step from that window."""
import sys, json
from gordon_matrix import Ctx, C
from induct_check import E, prodJ, B, v11
ctx = Ctx(11*360 + 400)
res = {}
for lam in range(-26, 3):
    for i in range(0, 5):
        c = {k: int(v) for k, v in C(ctx, lam, i, 360).items()}
        res[(lam, i)] = c
def size(w0, imin=1):
    ks = [(l, i) for l in range(w0, w0 + 11) for i in range(imin, 5)]
    return sum(len(res[k]) for k in ks), sum(len(str(abs(v))) for k in ks for v in res[k].values())
for w0 in range(-26, -7):
    print(f"window [{w0},{w0+10}] i=1..4: coeffs, digits =", size(w0), "| incl. i=0:", size(w0, 0))
w0 = int(sys.argv[1]) if len(sys.argv) > 1 else -8
ok = all(v11(v) >= B(l, i, nu) for l in range(w0, w0 + 11) for i in range(5) for nu, v in res[(l, i)].items())
print(f"Gordon bound holds on base window [{w0},{w0+10}]:", ok)
bad = 0
for lam in range(w0 + 11, 140):
    for i in range(5):
        for j, e in E.items():
            for b, cb in e.items():
                for nu1 in range(-60, 11*abs(lam)//5 + 80):
                    for t, s in prodJ(b, nu1).items():
                        rhs = B(lam, i, t)
                        if rhs <= 0: continue
                        if v11(cb) + v11(s) + max(B(lam - j, i, nu1), 0) < rhs: bad += 1
print("inductive-step violations for lam in [%d,140):" % (w0 + 11), bad)
json.dump({f"{l},{i}": {str(k): str(v) for k, v in res[(l, i)].items()} for l in range(w0, w0 + 11) for i in range(5)}, open(f"base_window_{w0}.json", "w"))
for i in range(5): print(" i=%d" % i, [ (min(res[(l,i)]), max(res[(l,i)]), len(res[(l,i)])) for l in range(w0, w0+11)])
