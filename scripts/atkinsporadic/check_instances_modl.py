"""Mod-ell check, on actual p(N) mod ell, that T(Q^2) kills sum_N p(ell N - delta) q^N for each
Ono-Weaver instance used in WeaverMain (weight lambda+1/2, lambda=(ell-3)/2). Since
eta^{-ell} S_{ell-1} is one-dimensional, this is the mod-ell content of EtaHecke Q (ell-1) ell."""
import subprocess, sys, numpy as np
SP = '/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/'
def leg(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q - 1) // 2, q) == 1 else -1)
NMAX = int(sys.argv[1])
inst = [(13, 59), (13, 73), (17, 41), (17, 89), (17, 103), (19, 101), (23, 5), (23, 19), (23, 37), (23, 47), (23, 67)]
cache = {}
for l, Q in inst:
    if l not in cache:
        cache[l] = np.frombuffer(subprocess.run([SP + 'pmod', str(NMAX), str(l)], capture_output=True).stdout, dtype=np.uint8)
    p = cache[l]; dl = (l * l - 1) // 24; d = (Q * Q - 1) * l // 24; lam = (l - 3) // 2
    s = leg(12, Q) * leg((-1) ** lam % Q, Q)
    a = lambda N: int(p[l * N - dl]) if N >= 1 else 0
    tested = bad = 0; N = 1
    while l * (Q * Q * N - d) - dl <= NMAX:
        b = a(Q * Q * N - d) + s * leg(24 * N - l, Q) * pow(Q, lam - 1, l) * a(N)
        if (N + d) % (Q * Q) == 0: b += pow(Q, 2 * lam - 1, l) * a((N + d) // (Q * Q))
        tested += 1; bad += (b % l != 0); N += 1
    print(f"ell={l} Q={Q}: T(Q^2) coefficients tested {tested}, nonzero {bad}")
