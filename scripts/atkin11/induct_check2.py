"""Brute-force inductiveness of Gordon's bound under the order-11 recurrence, over lam in [11,LMAX], all relevant nu."""
import sys
from induct_check import E, prodJ, B, v11
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 120
bad = []; tight = 0; minslack = 10**9
for lam in range(11, LMAX):
    for i in range(5):
        for j, e in E.items():
            for b, cb in e.items():
                for nu1 in range(-5, 11*lam//5 + 80):   # source index; beyond ~5lam/11 bounds are large
                    for t, s in prodJ(b, nu1).items():
                        lhs = v11(cb) + v11(s) + max(B(lam - j, i, nu1), 0)
                        rhs = B(lam, i, t)
                        if rhs <= 0: continue
                        minslack = min(minslack, lhs - rhs)
                        if lhs - rhs == 0: tight += 1
                        if lhs < rhs: bad.append((lam, i, j, b, nu1, t, lhs, rhs))
print("lam in [11,%d): violations=%d, min slack=%d, #tight=%d" % (LMAX, len(bad), minslack, tight))
from collections import Counter
print(Counter((x[1], x[2], x[3], x[4] % 5, x[5] % 5) for x in bad).most_common(15))
for x in bad[:10]: print(x)
