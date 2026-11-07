"""Mod-ell check: the twisted partition series is a T(Q^2) eigenvector (weight k-1/2, lambda odd)."""
import numpy as np, sys
def leg(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q - 1) // 2, q) == 1 else -1)
def pmod(M, NMAX):
    p = [0] * (NMAX + 1); p[0] = 1
    pent = []; k = 1
    while k * (3 * k - 1) // 2 <= NMAX:
        s = 1 if k % 2 else -1
        pent.append((k * (3 * k - 1) // 2, s)); pent.append((k * (3 * k + 1) // 2, s)); k += 1
    pent.sort()
    for n in range(1, NMAX + 1):
        t = 0
        for g, s in pent:
            if g > n: break
            t += s * p[n - g]
        p[n] = t % M
    return p
def twisted(ell, p):
    eps = -leg(-1, ell)
    return [p[N] if leg(24 * N - 1, ell) == eps else 0 for N in range(len(p))], eps
def eigen(ell, a, Q, lam, Nmax):
    """return set of mu values a(Q^2 N - d) + s (m/Q) Q^(lam-1) a(N) + Q^(2lam-1) a((N+d)/Q^2) / a(N)"""
    d = (Q * Q - 1) // 24; s = leg(-3, Q)
    mus = set(); zero_ok = True
    for N in range(Nmax):
        i = Q * Q * N - d
        if i >= len(a): break
        a1 = a[i] if i >= 0 else 0
        a3 = a[(N + d) // (Q * Q)] if (N + d) % (Q * Q) == 0 else 0
        b = (a1 + s * leg(24 * N - 1, Q) * pow(Q, lam - 1, ell) * a[N] + pow(Q, 2 * lam - 1, ell) * a3) % ell
        if a[N] % ell:
            mus.add(b * pow(a[N], -1, ell) % ell)
        elif b % ell:
            zero_ok = False
    return mus, zero_ok
if __name__ == "__main__":
    ell = int(sys.argv[1]); NMAX = int(sys.argv[2]); Qs = [int(x) for x in sys.argv[3].split(',')]
    p = pmod(ell, NMAX)
    a, eps = twisted(ell, p)
    lam = (ell * ell - 2 - 1) // 2  # weight (ell^2-2)/2 = lam + 1/2
    print("ell", ell, "eps", eps, "lambda", lam)
    for Q in Qs:
        mus, z = eigen(ell, a, Q, lam, NMAX)
        print("Q", Q, "mu set", mus, "consistent", z)
