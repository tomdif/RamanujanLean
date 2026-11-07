#!/usr/bin/env python3
"""Independent exact checks for the sixteen-reflection four-factor theorem.

Checks all modulus-nine origin classes, compares direct Pochhammer products
against Watson sums, and records a finite search for converse witnesses.
The finite search is not a proof of a uniform coefficient converse.
"""
import argparse
import hashlib
import json
from itertools import product
from math import gcd
from pathlib import Path

from check_four_plane import residues
from quintuple_vanishing_scan import product_coefficients

SHORT = ((1, 1, -1, 0), (0, -1, -1, 1), (1, 2, 0, -1), (1, 0, -2, 1))
CONDITION = ((3, 2, 1, 0), (2, 3, 0, 1), (0, 1, 3, 2), (1, 0, 2, 3))


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def raw(m, n, a, b, z, k):
    v = ((m-n, n, m, m+n), (-m-n, m, -n, m-n),
         (2*m, n-m, m+n, 2*n), (-2*n, m+n, m-n, 2*m))[b]
    u = SHORT[a]
    short = sum(u)-2*dot(u, z) if a < 2 else sum(u)//2-dot(u, z)
    return tuple(3*z[i]+u[i]*short+v[i]*k for i in range(4))


def numerator(m, n, b, z):
    v = ((m-n, n, m, m+n), (-m-n, m, -n, m-n),
         (2*m, n-m, m+n, 2*n), (-2*n, m+n, m-n, 2*m))[b]
    constant = (3*m+n-18, m-3*n, m+2*n-9, 2*m-n-9)[b]
    return constant-(2 if b < 2 else 1)*dot(v, z)


def origin_check():
    tested, compatible = 0, 0
    parameter_classes = set()
    for m, n, a, b in product(range(9), range(9), range(4), range(4)):
        p = m*m+n*n
        if gcd(p, 9) != 1:
            continue
        k = numerator(m, n, b, (0,)*4)*pow(p, -1, 9) % 9
        image = tuple(x % 9 for x in raw(m, n, a, b, (0,)*4, k))
        valid = all(x in (0, 3) for x in image) and sum(x//3 for x in image) % 2 == 1
        condition = (m, n, m-n, m+n)[CONDITION[a][b]] % 9 == 0
        assert valid == condition, (m, n, a, b, image)
        tested += 1
        if valid:
            compatible += 1
            parameter_classes.add((m, n))
    return {"map_parameter_combinations_checked": tested, "compatible_combinations": compatible,
            "compatible_parameter_classes": len(parameter_classes), "passed": True}


def check(max_m, depth):
    if max_m < 9 or depth < 0:
        raise ValueError("max-m must be at least 9 and depth nonnegative")
    origin = origin_check()
    cases = []
    for m in range(2, max_m+1):
        for n in range(1, m):
            p = m*m+n*n
            classes = [label for value, label in ((m, 'm'), (n, 'n'), (m-n, 'm-n'), (m+n, 'm+n'))
                       if value % 9 == 0]
            if not classes or gcd(6*n, p) != 1 or 2*(m+n) >= p:
                continue
            indices, rs = (m-n, n, m, m+n), residues(m, n)
            assert len(set(rs)) == 4
            limit = p*depth+max(rs)
            coefficients = [1]+[0]*limit
            for i in indices:
                for start, step in ((i, p), (p-i, p), (p, p), (p+2*i, 2*p), (p-2*i, 2*p)):
                    for exponent in range(start, limit+1, step):
                        for degree in range(limit, exponent-1, -1):
                            coefficients[degree] -= coefficients[degree-exponent]
            watson = product_coefficients(p, indices, limit)
            assert all(value == watson.get(j, 0) for j, value in enumerate(coefficients))
            assert all(coefficients[p*j+r] == 0 for r in rs for j in range(depth+1))
            assert coefficients[0] == 1
            witness_depth = p//4
            search = product_coefficients(p, indices, p*witness_depth+p-1)
            first, unresolved = [], []
            for r in range(p):
                if r in rs:
                    assert all(search.get(p*j+r, 0) == 0 for j in range(witness_depth+1))
                    continue
                j = next((j for j in range(witness_depth+1) if search.get(p*j+r, 0)), None)
                if j is None:
                    unresolved.append(r)
                else:
                    first.append((j, r, search[p*j+r]))
            j, r, value = max(first)
            cases.append({"m": m, "n": n, "modulus": p, "indices": indices, "divisible_by_nine": classes,
                          "zero_residues": sorted(rs), "all_coefficients_compared": limit+1,
                          "zero_progression_terms_checked": depth+1,
                          "finite_converse_search": {"depth": witness_depth,
                            "nonzero_residues_checked": len(first), "unresolved_residues": unresolved,
                            "largest_first_witness": {"N": j, "R": r, "coefficient": value}}})
            print(f"m={m}, n={n}, p={p}: {limit+1} coefficients agree; "
                  f"largest first witness N={j}, unresolved={len(unresolved)}", flush=True)
    sources = (Path(__file__), Path(__file__).with_name('check_four_plane.py'),
               Path(__file__).with_name('quintuple_vanishing_scan.py'))
    return {"scope": "Exact finite experiments; uniform infinite vanishing and reflection compatibility are proved separately in Lean",
            "max_m": max_m, "depth": depth, "origin_check": origin,
            "all_coefficient_checks_passed": True, "cases": cases,
            "total_coefficients_compared": sum(c['all_coefficients_compared'] for c in cases),
            "total_nonzero_residue_witnesses": sum(c['finite_converse_search']['nonzero_residues_checked'] for c in cases),
            "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, default=24)
    parser.add_argument('--depth', type=int, default=10)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.max_m, args.depth)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f"Passed {len(result['cases'])} pairs; {result['total_coefficients_compared']} coefficients compared")
