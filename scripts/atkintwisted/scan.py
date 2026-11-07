#!/usr/bin/env python3
"""Atkin's twisted mod-13 class: F(N) = p(N) if ((24N-1)/13) = -1 else 0 (reduction of g/eta, g in S_168).
For each prime 5 <= Q < QMAX, Q != 13, compute T(Q^2) in weight 167+1/2 on the N-coordinate
  b(N) = F(Q^2 N - d) + s ((24N-1)/Q) Q^166 F(N) + Q^333 F((N+d)/Q^2),  d = (Q^2-1)/24,
  s = (12/Q)((-1)^167/Q)   (exactly Atkin13.EB),
determine mu from the first N with F(N) != 0, and test b = mu F
  (a) on N = 0..14 (Sturm bound for S_168: decisive, given EtaHecke Q 168 1), and
  (b) on every N with Q^2 N - d <= NMAX (numerical cross-check).
Classify: Atkin-type eps = +-1 if mu = s eps Q^166 (mod 13); Ono-type if mu = 0.
Usage: scan.py PFILE QMAX OUT.json  (PFILE: raw uint32 p(n) mod 13*17*19*23*29*31, pmodM.c)"""
import sys, json
import numpy as np
from sympy import primerange, legendre_symbol

def leg(a, Q):
    a %= Q
    return 0 if a == 0 else legendre_symbol(a, Q)

def main():
    pM = np.fromfile(sys.argv[1], dtype=np.uint32); QMAX = int(sys.argv[2])
    NMAX = len(pM) - 1
    p13 = (pM % 13).astype(np.int64)
    n = np.arange(NMAX + 1, dtype=np.int64)
    r = (24 * n - 1) % 13
    nonres = np.isin(r, [2, 5, 6, 7, 8, 11])
    F = np.where(nonres, p13, 0)
    N0 = int(np.nonzero(F)[0][0])
    out = []
    for Q in primerange(5, QMAX):
        if Q == 13: continue
        d = (Q * Q - 1) // 24
        s = leg(12, Q) * leg(-1, Q)
        c = pow(Q, 166, 13); c2 = pow(Q, 333, 13)
        Ntop = (NMAX + d) // (Q * Q)
        Ns = np.arange(Ntop + 1, dtype=np.int64)
        idx = Q * Q * Ns - d
        b = np.where(idx >= 0, F[np.maximum(idx, 0)], 0)
        legs = np.array([leg(24 * int(N) - 1, Q) for N in Ns], dtype=np.int64)
        b = b + s * legs * c * F[Ns]
        j = (Ns + d)
        b = b + np.where(j % (Q * Q) == 0, c2 * F[j // (Q * Q)], 0)
        b %= 13
        mu = int(b[N0] * pow(int(F[N0]), -1, 13) % 13)
        diff = (b - mu * F[Ns]) % 13
        sturm_ok = bool(np.all(diff[:15] == 0))
        bad = int(np.count_nonzero(diff))
        typ = []
        if mu == 0: typ.append('ono')
        if (mu - s * c) % 13 == 0: typ.append('atkin+')
        if (mu + s * c) % 13 == 0: typ.append('atkin-')
        out.append(dict(Q=Q, mu=mu, s=s, sturm_ok=sturm_ok, checked=Ntop + 1, bad=bad, type=typ,
                        prefix=Q * Q * 14 - d + 1))
    json.dump(dict(N0=N0, NMAX=NMAX, res=out), open(sys.argv[3], 'w'), default=int, indent=0)
    for x in out:
        print(x['Q'], x['mu'], x['s'], 'EIGEN' if x['sturm_ok'] else 'not-eigen', x['checked'], x['bad'], x['type'])

main()
