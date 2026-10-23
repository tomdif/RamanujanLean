"""Check Andrews' Bailey pair for f0 (relative to a=1), exactly to order q^N:
   beta_n = 1/(-q;q)_n,
   alpha_0 = 1, alpha_n = q^{(3n^2+n)/2} S_n - q^{(3n^2-n)/2} S_{n-1},  S_n = sum_{|j|<=n} (-1)^j q^{-j^2}.
With bailey_transform (a=1) this gives (q)_inf f0(q) = sum_n q^{n^2} alpha_n, i.e. HM (0.3)."""
import series; series.N = 120
from series import *
N = series.N
def qf(n): return fac(1, 1, 1, n)
def mqf(n): return fac(1, -1, 1, n)
def part(n, e):
    r = [0] * N
    for j in range(-n, n + 1):
        k = e - j * j
        if 0 <= k < N: r[k] += (-1) ** j
    return r
def alpha(n):
    return mono(0) if n == 0 else add(part(n, (3*n*n + n)//2), sc(-1, part(n - 1, (3*n*n - n)//2)))
for n in range(9):
    s = [0] * N
    for r in range(n + 1): s = add(s, mul(alpha(r), inv(mul(qf(n - r), qf(n + r)))))
    print(n, 'pair holds' if not any(add(s, sc(-1, inv(mqf(n))))) else 'FAIL')
