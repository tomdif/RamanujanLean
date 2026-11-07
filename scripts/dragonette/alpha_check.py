"""Numerical checks for Dragonette's asymptotic for f(q) = sum q^{n^2}/(-q;q)_n^2.
Computes alpha(n) exactly (integers) for n <= N, checks the sign pattern (-1)^(n-1) alpha(n) > 0,
the ratio to e^{pi sqrt(n/6-1/144)}/(2 sqrt(n-1/24)), and the decomposition alpha = 2 phi_(-q) - b."""
import math, sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

def mul(a, b):
    c = [0]*(N+1)
    for i, x in enumerate(a):
        if x:
            for j in range(0, N+1-i):
                if b[j]: c[i+j] += x*b[j]
    return c

def inv_one_plus_xk_sq(series, k):  # series / (1+q^k)
    s = series[:]
    for m in range(k, N+1):
        s[m] -= s[m-k]
    return s

f = [0]*(N+1)
# term_n = q^{n^2} / (-q;q)_n^2, built incrementally on a truncated base
base = [0]*(N+1); base[0] = 1  # 1/(-q;q)_n^2 truncated
n = 0
while n*n <= N:
    for m in range(0, N+1-n*n):
        f[m+n*n] += base[m]
    n += 1
    base = inv_one_plus_xk_sq(inv_one_plus_xk_sq(base, n), n)

bad = [m for m in range(1, N+1) if not ((-1)**(m-1)*f[m] > 0)]
print("sign failures 1..N:", bad[:20])
for m in [10, 100, 500, 1000, 2000, N]:
    if m <= N:
        main = math.exp(math.pi*math.sqrt(m/6-1/144))/(2*math.sqrt(m-1/24))
        print(m, f[m] if m < 60 else '...', "ratio", ((-1)**(m-1)*f[m])/main)
print("first:", f[:12])
