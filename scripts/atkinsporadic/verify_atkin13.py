"""Numerical check of Atkin's p(17303 n + 237) == 0 (mod 13) and its class structure."""
import numpy as np, sys
M = 13
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
p = np.zeros(NMAX + 1, dtype=np.int64); p[0] = 1
pent = []
k = 1
while True:
    a = k * (3 * k - 1) // 2; b = k * (3 * k + 1) // 2
    if a > NMAX: break
    s = 1 if k % 2 else -1
    pent.append((a, s));
    if b <= NMAX: pent.append((b, s))
    k += 1
for n in range(1, NMAX + 1):
    t = 0
    for (g, s) in pent:
        if g > n: break
        t += s * p[n - g]
    p[n] = t % M
np.save('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/p_mod13.npy', p)
A = 17303
bad = [n for n in range(237, NMAX + 1, A) if p[n] % M]
print("Atkin progression terms checked:", len(range(237, NMAX + 1, A)), "nonzero:", bad[:5])
print("24*237-1 =", 24 * 237 - 1)
# class structure: N with 24N-1 = 121 m, m mod 3432
def leg(a, q):
    a %= q
    if a == 0: return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1
res = {}
for N in range(NMAX + 1):
    m24 = 24 * N - 1
    if m24 % 121: continue
    m = m24 // 121
    if m % 11 == 0: continue
    key = (leg(m, 11), leg(m, 13))
    res.setdefault(key, [0, 0])
    res[key][0] += 1
    if p[N] % M: res[key][1] += 1
print("classes (m/11),(m/13) -> [count, nonzero]:", res)
