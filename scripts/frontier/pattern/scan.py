# scan primes: b_l(m) (module & proportionality versions), stable-module invariants, Newton slopes of X=DU
import sys, json, math, io, contextlib
from bstab import run
import sympy
from katzmat import dimM

def newton(vals, cap):
    pts = [(k, v) for k, v in enumerate(vals) if v < cap]
    # lower convex hull
    hull = []
    for pt in pts:
        while len(hull) >= 2 and (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-2][0]) >= (pt[1] - hull[-2][1]) * (hull[-1][0] - hull[-2][0]):
            hull.pop()
        hull.append(pt)
    slopes = []
    for a, b in zip(hull, hull[1:]):
        s = (b[1] - a[1]) / (b[0] - a[0]); slopes += [round(s, 3)] * (b[0] - a[0])
    return slopes

def one(p, PR, N, mmax):
    r = (p + 12) // 24 if p > 3 else 1
    B = 2 * mmax + 2 * (r + 4)
    with contextlib.redirect_stdout(io.StringIO()):
        res, vs, K, U, D = run(p, PR, N, B, mmax)
    sl = newton(res['X_charpoly_vals'], PR)
    return res, sl

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3]
    allres = {}
    for p in sympy.primerange(lo, hi + 1):
        PR = min(9, int(62 / math.log2(p)))
        mmax = PR
        N1, N2 = PR + 3, PR + 6
        r1, sl1 = one(p, PR, N1, mmax)
        r2, sl2 = one(p, PR, N2, mmax)
        d = dimM(p - 1) - 1
        row = dict(p=p, d=d, PR=PR, N=(N1, N2), fko_bound=(p + 12) // 24)
        bm = {}; ok = True
        for m in range(1, mmax + 1):
            a, b = r1['tab'][m], r2['tab'][m]
            same = (a['bmod'] == b['bmod'] and a['bprop'] == b['bprop'] and a['stable'] == b['stable'])
            ok &= same
            bm[m] = dict(bmod=b['bmod'], bprop=b['bprop'], inv=b['stable'] and b['stable']['invariants'],
                         agree=same)
        row['b'] = bm; row['truncation_agree'] = ok
        # slopes agree only up to precision; keep those below cap from both
        row['slopes_N1'] = sl1[:14]; row['slopes_N2'] = sl2[:14]
        row['unit_roots'] = sum(1 for s in sl2 if s == 0)
        allres[p] = row
        bs = ' '.join(f"{bm[m]['bmod']}" for m in range(1, mmax + 1))
        invs = bm[mmax]['inv']
        print(f"l={p:3d} d={d} PR={PR} ok={ok} b(m=1..{mmax})= {bs} | 2m-1? {all(bm[m]['bmod']==2*m-1 for m in bm)} "
              f"| m? {all(bm[m]['bmod']==m for m in bm)} | stable(m={mmax}) {invs} | slopes {sl2[:10]}", flush=True)
        json.dump(allres, open(out, 'w'), indent=1, default=str)
