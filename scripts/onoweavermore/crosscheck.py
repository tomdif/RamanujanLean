#!/usr/bin/env python3
"""Direct check of every congruence found by scan.py on actual p(n) mod ell, n <= 12e6:
 Ono type (ell,Q,0):  ell | p(n) whenever 24n-1 = ell*Q^3*k, Q not| k;
 Atkin type (ell,Q,e): ell | p(n) whenever 24n-1 = ell*Q^2*m, (m/Q) = e.
Also the control class (m/Q) = -e (expected mostly nonzero). Usage: crosscheck.py PFILE SCANJSON"""
import sys, json
import numpy as np
from sympy import legendre_symbol
pM = np.fromfile(sys.argv[1], dtype=np.uint32); NMAX = len(pM) - 1
data = json.load(open(sys.argv[2]))
tot = 0; fails = 0; rows = []
for r in data:
    ell = r['ell']; pl = pM % ell
    for x in r['res']:
        if not x.get('type'): continue
        Q = x['Q']; t = x['type'][0]
        if t == 'ono':
            mod = ell * Q ** 3; n_ok = n_bad = 0
            for k in range(1, (24 * NMAX + 1) // mod + 1):
                if k % Q == 0 or (mod * k + 1) % 24: continue
                n = (mod * k + 1) // 24
                n_ok += 1; n_bad += pl[n] != 0
            rows.append((ell, Q, 0, n_ok, int(n_bad), None))
        else:
            e = 1 if t == 'atkin+' else -1
            mod = ell * Q * Q; c = [0, 0]; ctrl = [0, 0]
            for m in range(1, (24 * NMAX + 1) // mod + 1):
                if (mod * m + 1) % 24: continue
                ls = legendre_symbol(m % Q, Q) if m % Q else 0
                n = (mod * m + 1) // 24
                if ls == e: c[0] += 1; c[1] += pl[n] != 0
                elif ls == -e: ctrl[0] += 1; ctrl[1] += pl[n] != 0
            rows.append((ell, Q, e, c[0], int(c[1]), ctrl))
        tot += rows[-1][3]; fails += rows[-1][4]
for row in rows: print(row)
print("total checked", tot, "failures", fails)
