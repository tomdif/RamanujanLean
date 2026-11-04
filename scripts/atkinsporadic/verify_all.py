"""Direct check against p(N) mod ell (C helper) of every predicted congruence.
Ono/Weaver class (ell | 24N-1):  24N-1 = ell*Q^3*n, Q !| n            (mu(Q) = 0)
                                 24N-1 = ell*Q^2*n, (n/Q) = e          (Atkin type)
Twisted class ((24N-1)/ell) = -(-1/ell): 24N-1 = Q^2*n, (n/Q)=e        (Atkin type)"""
import subprocess, numpy as np, sys
SP = '/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/'
def leg(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q - 1) // 2, q) == 1 else -1)
NMAX = int(sys.argv[1])
cache = {}
def P(ell):
    if ell not in cache:
        raw = subprocess.run([SP + 'pmod', str(NMAX), str(ell)], capture_output=True).stdout
        cache[ell] = np.frombuffer(raw, dtype=np.uint8)
    return cache[ell]
claims = [  # (ell, kind, Q, e)
    (13, 'twist', 11, 1), (13, 'twist', 37, -1),
    (13, 'ono', 59, 0), (13, 'ono', 73, 0),
    (17, 'ono', 41, 0), (17, 'atkin', 23, -1),
    (19, 'atkin', 13, -1), (19, 'atkin', 23, -1), (19, 'ono', 101, 0),
    (23, 'ono', 5, 0), (23, 'ono', 19, 0), (23, 'ono', 37, 0),
]
for ell, kind, Q, e in claims:
    p = P(ell); tot = bad = ctl = ctlbad = 0
    for N in range(NMAX + 1):
        m = 24 * N - 1
        if kind == 'ono':
            if m % (ell * Q ** 3): continue
            n = m // (ell * Q ** 3); ok = n % Q != 0; inclass = ok
        elif kind == 'atkin':
            if m % (ell * Q * Q): continue
            n = m // (ell * Q * Q); inclass = leg(n, Q) == e
            ok = leg(n, Q) != 0
        else:
            if m % (Q * Q) or leg(m, ell) != -leg(-1, ell): continue
            n = m // (Q * Q); inclass = leg(n, Q) == e; ok = leg(n, Q) != 0
        if not ok: continue
        if inclass:
            tot += 1; bad += int(p[N] != 0)
        else:
            ctl += 1; ctlbad += int(p[N] != 0)
    print(f"ell={ell} {kind:5s} Q={Q} e={e}: in-class {tot} checked, {bad} nonzero | control {ctl}, {ctlbad} nonzero")
