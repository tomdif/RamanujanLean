"""Check Garvan (arXiv:1907.04803, Thm 1.1): (q)_inf (chi0 - 2) as two Hecke-Rogers double sums
(sgn(m) = 1 for m >= 0, -1 for m < 0), exactly to order q^N."""
import series; series.N = 150
from series import *
N = series.N
lhs = mul(inf(1, 1), add(series.chi0(), mono(0, -2)))
h = [0] * N
sg = lambda m: 1 if m >= 0 else -1
for j in range(60):
    for m in range(-j - 1, j + 1):
        for ok, e in ((-j <= 3*m <= j, (j*(3*j+1) - m*(15*m+1))//2),
                      (j >= 1 and -j-1 <= 3*m <= j-1, (j*(3*j+1) - m*(15*m+11))//2 - 1)):
            if ok:
                for ee, s in ((e, 1), (e + 2*j + 1, -1)):
                    if 0 <= ee < N: h[ee] += s * sg(m) * (-1)**(m + j + 1)
print('mismatches:', sum(1 for a, b in zip(lhs, h) if a != b))
