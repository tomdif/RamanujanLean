#!/usr/bin/env python3
"""Scan primes Q < QMAX for the T(Q^2) eigenvalue mu_Q (mod ell) on G = sum_N p(ell N - delta) q^N,
ell in {13,17,19,23,29,31}; classify Ono type (mu = 0) and Atkin type (mu = eps * s * Q^(lam-1)).
Every eigen relation b(N) = mu G(N) is checked on all N available from the prefix.
Usage: scan.py PFILE QMAX   (PFILE: raw uint32 p(n) mod 13*17*19*23*29*31, from pmodM.c)"""
import sys, json
import numpy as np
from sympy import primerange, legendre_symbol

def load(path):
    return np.fromfile(path, dtype=np.uint32)

def leg(a, Q):
    a %= Q
    return 0 if a == 0 else legendre_symbol(a, Q)

def scan(pM, ell, QMAX):
    NMAX = len(pM) - 1
    pl = (pM % ell).astype(np.int64)
    delta = (ell * ell - 1) // 24
    lam = (ell - 1) - (ell + 1) // 2
    Nmax = (NMAX + delta) // ell
    G = np.zeros(Nmax + 1, dtype=np.int64)
    for N in range(Nmax + 1):
        i = ell * N - delta
        if i >= 0: G[N] = pl[i]
    N0 = next(N for N in range(Nmax + 1) if G[N] % ell)
    res = []
    for Q in primerange(5, QMAX):
        if Q == ell: continue
        d = (Q * Q - 1) * ell // 24
        s = leg(12, Q) * leg((-1) ** lam, Q)
        c = pow(Q, lam - 1, ell); c2 = pow(Q, 2 * lam - 1, ell)
        Ntop = (Nmax + d) // (Q * Q)
        if Ntop < N0: res.append(dict(Q=Q, status='TOO-SHORT')); continue
        def b(N):
            v = 0
            if Q * Q * N - d >= 0: v += G[Q * Q * N - d]
            v += s * leg(24 * N - ell, Q) * c * G[N]
            if (N + d) % (Q * Q) == 0: v += c2 * G[(N + d) // (Q * Q)]
            return v % ell
        mu = b(N0) * pow(int(G[N0]), -1, ell) % ell
        bad = [N for N in range(Ntop + 1) if (b(N) - mu * G[N]) % ell]
        typ = []
        if mu == 0: typ.append('ono')
        if (mu - s * c) % ell == 0: typ.append('atkin+')
        if (mu + s * c) % ell == 0: typ.append('atkin-')
        res.append(dict(Q=Q, mu=int(mu), s=s, checked=Ntop + 1, bad=len(bad), type=typ,
                        idx=ell * (Q * Q * N0 - d) - delta))
    return dict(ell=ell, delta=delta, lam=lam, N0=N0, res=res)

if __name__ == '__main__':
    pM = load(sys.argv[1]); QMAX = int(sys.argv[2])
    out = []
    for ell in [13, 17, 19, 23, 29, 31]:
        r = scan(pM, ell, QMAX); out.append(r)
        hits = [(x['Q'], x['type'], x['checked'], x['bad']) for x in r['res'] if x.get('type')]
        nbad = sum(1 for x in r['res'] if x.get('bad'))
        short = [x['Q'] for x in r['res'] if x.get('status')]
        print(f"ell={ell} N0={r['N0']} non-eigen Q: {nbad}  too-short: {short[:3]}..{len(short)}")
        print("   hits:", hits)
    json.dump(out, open(sys.argv[3], 'w') if len(sys.argv) > 3 else sys.stdout, default=int)
