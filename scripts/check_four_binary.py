#!/usr/bin/env python3
"""Exact independent checks for the p=2m²+n² four-factor family.

Finite comparisons supplement the infinite Lean theorem; no converse is
inferred from a finite zero scan. Uses only Python integer arithmetic.
"""
import argparse
import hashlib
import json
from itertools import product
from math import gcd
from pathlib import Path
from quintuple_vanishing_scan import product_coefficients


def origin_check():
    tested, compatible = 0, 0
    for m, n, r in product(range(15), range(15), range(2)):
        p = 2*m*m+n*n
        if gcd(p, 15) != 1:
            continue
        v = (2*m, 4*m, n, 3*n)
        w = (n, 2*n, -m, -3*m)
        u = (0, 0, -3, 1) if r else (-2, 1, 0, 0)
        num = 3*n-4*m if r else 3*m+2*n-30
        k = num*pow(p, -1, 15) % 15
        raw = tuple((-u[i]+(w if r else v)[i]*k) % 15 for i in range(4))
        valid = all(x in (0, 5) for x in raw) and sum(x//5 for x in raw) % 2 == 1
        assert valid == (m % 3 == 0 and n % 5 == 0), (m, n, r, raw)
        tested += 1
        compatible += valid
    return {"unit_norm_map_parameter_combinations": tested,
            "compatible_combinations": compatible, "passed": True,
            "scope": "Finite origin test; not claimed as a Lean converse theorem"}


def check(max_m, max_n, parameters, depth):
    if max_m < 3 or max_n < 5 or parameters < 1 or depth < 0:
        raise ValueError('need max-m>=3, max-n>=5, parameters>=1, depth>=0')
    origin = origin_check()
    pairs = {(m, n) for m in range(3, max_m+1, 3) for n in range(5, max_n+1, 5)}
    pairs.update((15*t+3, 5) for t in range(parameters))
    cases = []
    for m, n in sorted(pairs):
        p = 2*m*m+n*n
        if gcd(30*m, p) != 1 or 8*m >= p or 6*n >= p:
            continue
        indices = (2*m, 4*m, n, 3*n)
        rs = ((3*m+2*n-30) % p, (3*m+2*n) % p)
        assert len(set(rs)) == 2
        limit = p*depth+max(rs)
        direct = [1]+[0]*limit
        for i in indices:
            for start, step in ((i, p), (p-i, p), (p, p), (p+2*i, 2*p), (p-2*i, 2*p)):
                for exponent in range(start, limit+1, step):
                    for degree in range(limit, exponent-1, -1):
                        direct[degree] -= direct[degree-exponent]
        watson = product_coefficients(p, indices, limit)
        assert all(value == watson.get(k, 0) for k, value in enumerate(direct))
        assert all(direct[p*j+r] == 0 for r in rs for j in range(depth+1))
        assert direct[0] == 1
        cases.append({"m": m, "n": n, "modulus": p, "indices": indices,
                      "zero_residues": rs, "terms_per_progression": depth+1,
                      "all_coefficients_compared": limit+1})
        print(f'm={m}, n={n}, p={p}: {limit+1} coefficients agree', flush=True)
    inputs = [Path(__file__), Path(__file__).with_name('quintuple_vanishing_scan.py')]
    return {"arithmetic": "Python integers; direct Pochhammer factors versus Watson sums",
            "all_checks_passed": True, "origin_check": origin, "cases": cases,
            "max_m": max_m, "max_n": max_n, "one_parameter_cases_requested": parameters, "depth": depth,
            "total_coefficients_compared": sum(c['all_coefficients_compared'] for c in cases),
            "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, default=24)
    parser.add_argument('--max-n', type=int, default=25)
    parser.add_argument('--parameters', type=int, default=5)
    parser.add_argument('--depth', type=int, default=10)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.max_m, args.max_n, args.parameters, args.depth)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f"Passed {len(result['cases'])} pairs; {result['total_coefficients_compared']} coefficients compared")
