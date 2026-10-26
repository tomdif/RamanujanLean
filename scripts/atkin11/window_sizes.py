"""Size of the base data U11(phi^lam J_i), i=1..4, for different 11-windows of lam."""
from gordon_matrix import Ctx, C
ctx = Ctx(11*300 + 400)
res = {}
for lam in range(-8, 11):
    for i in range(0, 5):
        c = C(ctx, lam, i, 300)
        res[(lam, i)] = (len(c), sum(len(str(abs(int(v.p)))) for v in c.values()), min(c), max(c))
for w0 in (-8, -5, -3, 0):
    tot = sum(res[(l, i)][1] for l in range(w0, w0 + 11) for i in range(1, 5))
    terms = sum(res[(l, i)][0] for l in range(w0, w0 + 11) for i in range(1, 5))
    print(f"window lam in [{w0},{w0+10}], i=1..4: {terms} coefficients, {tot} digits")
for l in range(-8, 11): print(l, [res[(l, i)] for i in range(5)])
