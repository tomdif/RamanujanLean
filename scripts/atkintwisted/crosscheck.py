#!/usr/bin/env python3
"""Direct check of every congruence found by scan.py on exact p(N) mod 13, N <= NMAX.
Atkin type (Q, eps):  24N-1 = Q^2 m, (m/Q) = eps, (m/13) = -1  =>  13 | p(N);  control: (m/Q) = -eps.
Ono type   (Q):       24N-1 = Q^3 n, Q !| n, (Qn/13) = -1       =>  13 | p(N);  control: Q^2 || 24N-1 wait
Also the explicit progression 13 | p(13 Q^3 n + r) (Atkin) / p(13 Q^4 n + r) (Ono).
Usage: crosscheck.py PFILE scan500.json OUT.json"""
import sys, json
import numpy as np
from sympy import legendre_symbol

def leg(a, Q):
    a %= Q
    return 0 if a == 0 else legendre_symbol(a, Q)

def prog(Q, typ):
    if typ == 'ono':
        n0 = next(n for n in range(1, 10 ** 6) if (Q ** 3 * n + 1) % 24 == 0 and n % Q and leg(Q * n, 13) == -1)
        return 13 * Q ** 4, (Q ** 3 * n0 + 1) // 24, n0
    eps = 1 if typ == 'atkin+' else -1
    m0 = next(m for m in range(1, 10 ** 6) if (Q * Q * m + 1) % 24 == 0 and leg(m, Q) == eps and leg(m, 13) == -1)
    return 13 * Q ** 3, (Q * Q * m0 + 1) // 24, m0

def main():
    pM = np.fromfile(sys.argv[1], dtype=np.uint32); NMAX = len(pM) - 1
    p13 = pM % 13
    scan = json.load(open(sys.argv[2]))
    out = []
    for x in scan['res']:
        for typ in x['type']:
            Q = x['Q']; ok = fail = ctl = ctlnz = 0
            if typ == 'ono':
                n = 1
                while (Q ** 3 * n + 1) // 24 <= NMAX:
                    if (Q ** 3 * n + 1) % 24 == 0 and n % Q:
                        N = (Q ** 3 * n + 1) // 24
                        if leg(Q * n, 13) == -1:
                            ok += 1; fail += int(p13[N] != 0)
                        else:
                            ctl += 1; ctlnz += int(p13[N] != 0)
                    n += 1
            else:
                eps = 1 if typ == 'atkin+' else -1
                m = 1
                while (Q * Q * m + 1) // 24 <= NMAX:
                    if (Q * Q * m + 1) % 24 == 0 and leg(m, 13) == -1 and m % Q:
                        N = (Q * Q * m + 1) // 24
                        if leg(m, Q) == eps:
                            ok += 1; fail += int(p13[N] != 0)
                        else:
                            ctl += 1; ctlnz += int(p13[N] != 0)
                    m += 1
            A, r, w = prog(Q, typ)
            pk = [int(p13[A * t + r]) for t in range((NMAX - r) // A + 1)] if r <= NMAX else []
            row = dict(Q=Q, type=typ, mu=x['mu'], checked=ok, fail=fail, control=ctl, control_nonzero=ctlnz,
                       modulus=A, residue=r, witness=w, prog_checked=len(pk), prog_fail=sum(1 for v in pk if v))
            out.append(row); print(row)
    json.dump(out, open(sys.argv[3], 'w'), indent=0)

main()
