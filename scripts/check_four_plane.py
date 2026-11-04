#!/usr/bin/env python3
"""Independent exact checks for the two-parameter four-factor theorem.

Compare direct Pochhammer multiplication against Watson sums, then check all
four predicted zero progressions. These finite checks do not prove the theorem.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from quintuple_vanishing_scan import product_coefficients


def residues(m, n):
    p = m*m+n*n
    return ((3*m+n-18)*pow(2, -1, p) % p,
            n*(m+2*n-9)*pow(n-m, -1, p) % p,
            n*(2*m-n-9)*pow(m+n, -1, p) % p,
            (3*m+n)*pow(2, -1, p) % p)


def check(max_m, depth):
    if max_m < 5 or depth < 0:
        raise ValueError("max-m must be at least 5 and depth nonnegative")
    cases = []
    for m in range(2, max_m+1):
        for n in range(1, m):
            p = m*m+n*n
            if (m+n) % 9 or gcd(n, 9) != 1 or gcd(6*n, p) != 1 or 2*(m+n) >= p:
                continue
            indices = (m-n, n, m, m+n)
            rs = residues(m, n)
            assert len(set(rs)) == 4
            limit = p*depth+max(rs)
            coefficients = [1]+[0]*limit
            for i in indices:
                for start, step in ((i, p), (p-i, p), (p, p),
                                    (p+2*i, 2*p), (p-2*i, 2*p)):
                    for exponent in range(start, limit+1, step):
                        for degree in range(limit, exponent-1, -1):
                            coefficients[degree] -= coefficients[degree-exponent]
            watson = product_coefficients(p, indices, limit)
            assert all(value == watson.get(j, 0) for j, value in enumerate(coefficients))
            assert all(coefficients[p*j+r] == 0 for r in rs for j in range(depth+1))
            assert coefficients[0] == 1
            cases.append({"m": m, "n": n, "modulus": p, "indices": indices,
                          "zero_residues": rs, "terms_per_progression": depth+1,
                          "all_coefficients_compared": limit+1})
            print(f"m={m}, n={n}, p={p}: {limit+1} coefficients agree", flush=True)
    return {"arithmetic": "Python integers; direct Pochhammer factors versus Watson sums",
            "all_checks_passed": True, "max_m": max_m, "depth": depth, "cases": cases,
            "total_coefficients_compared": sum(c["all_coefficients_compared"] for c in cases),
            "sha256": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in (Path(__file__), Path(__file__).with_name(
                           "quintuple_vanishing_scan.py"))}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=24)
    parser.add_argument("--depth", type=int, default=10)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.max_m, args.depth)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Passed {len(result['cases'])} parameter pairs; "
          f"{result['total_coefficients_compared']} coefficients compared")
