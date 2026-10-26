"""Empirically determine the best delta(mu mod 5, nu mod 5) such that
   v11(C^lam_{mu,nu}) >= floor((11nu - mu - 5lam + delta)/10) on all computed entries; compare with Gordon's table."""
import sys
from gordon_matrix import *
N = int(sys.argv[1]); lo, hi = int(sys.argv[2]), int(sys.argv[3])
mus = range(int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else range(0, 5)
ctx = Ctx(11*N + 400)
best = [[None]*5 for _ in range(5)]
for lam in range(lo, hi):
    for mu in mus:
        c = C(ctx, lam, mu, N)
        for nu, v in c.items():
            vv = val_p(v, 11)
            # largest delta with floor((11nu-mu-5lam+delta)/10) <= vv  <=> 11nu-mu-5lam+delta <= 10vv+9
            dmax = 10*vv + 9 - (11*nu - mu - 5*lam)
            a, b = mu % 5, nu % 5
            if best[a][b] is None or dmax < best[a][b]: best[a][b] = dmax
print("empirical max delta (rows mu mod 5, cols nu mod 5), lam in [%d,%d), mu in %s:" % (lo, hi, list(mus)))
for a in range(5): print(a, best[a], " Gordon/Mestrige table:", DELTA[a])
