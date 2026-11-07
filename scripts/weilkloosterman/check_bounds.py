"""Numerical sanity checks for WeilKloosterman: max_b |S(1,b;q)| / sqrt(q) for q = p, p^2, p^3, 2^k."""
import cmath, math
def S(b, q):
    tot = 0
    for u in range(1, q):
        if math.gcd(u, q) == 1:
            tot += cmath.exp(2j*math.pi*((u + b*pow(u, -1, q)) % q)/q)
    return abs(tot)
for q, lab in [(p, f"{p}") for p in (3,5,7,11,13,31,101)] + [(p**3, f"{p}^3") for p in (3,5,7)] + \
              [(p**5, f"{p}^5") for p in (3,)] + [(2**k, f"2^{k}") for k in (3,5,7,9)]:
    r = max(S(b, q) for b in range(q)) / math.sqrt(q)
    print(f"q={lab:6s} max|S(1,b;q)|/sqrt(q) = {r:.4f}")
