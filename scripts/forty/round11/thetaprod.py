#!/usr/bin/env python3
"""Is a pure eta quotient (dict k->exponent of e_k=(q^k;q^k)) a product of two scaled pure-eta thetas?"""
from collections import Counter
from itertools import combinations_with_replacement
# name -> eta exponents at base scale (e_k exponents)
BASE = {
 'phi(q)':   {2:5, 1:-2, 4:-2},
 'phi(-q)':  {1:2, 2:-1},
 'psi(q)':   {2:2, 1:-1},
 'psi(-q)':  {1:1, 4:1, 2:-1},
 'f(-q)':    {1:1},
 'f(q)':     {2:3, 1:-1, 4:-1},
 'f(q,q2)':  {2:1, 3:2, 1:-1, 6:-1},
 'f(q,q5)':  {2:2, 3:1, 12:1, 1:-1, 4:-1, 6:-1},
 'f(-q,-q5)':{1:1, 6:2, 2:-1, 3:-1},
 'f(-q,q2)': None,
}
BASE = {k: v for k, v in BASE.items() if v}
def scaled(v, s): return {k*s: e for k, e in v.items()}
def norm(c): return frozenset((k, e) for k, e in c.items() if e)
def thetas(scales):
    out = {}
    for n, v in BASE.items():
        for s in scales:
            out[f'{n}@{s}'] = scaled(v, s)
    return out
def search(target, scales):
    T = thetas(scales); items = list(T.items()); tgt = norm(target); res = []
    for (n1, v1), (n2, v2) in combinations_with_replacement(items, 2):
        c = Counter(v1); c.update(v2)
        if norm(c) == tgt: res.append((n1, n2))
    return res
if __name__ == '__main__':
    sc = [d for d in range(1, 337) if 336 % d == 0 or 168 % d == 0]
    X1 = {1:1, 4:3, 6:1, 7:1, 84:1, 2:-4, 14:-1}
    X2 = {1:3, 4:1, 6:1, 12:1, 28:1, 84:1, 2:-4, 3:-1, 14:-1}
    print('bc*f12 f84/chi^2(q):', search(X1, sc))
    print('ad*f12 f84/chi^2(q):', search(X2, sc))
