#!/usr/bin/env python3
"""Compare direct Pochhammer products and Watson sums for the sparse family.

Finite integer checks complement the all-parameter Lean theorem. They do not
replace its proof of the infinite coefficient progressions.
"""
import argparse
import hashlib
import json
from pathlib import Path

from quintuple_vanishing_scan import product_coefficients


def check(parameters, depth):
    cases = []
    for t in range(parameters):
        p = 9 * t * t + 15 * t + 7
        indices = (1, 3 * t + 2, 3 * t + 3)
        residue = indices[2]
        limit = p * depth + residue
        coefficients = [1] + [0] * limit
        for i in indices:
            for start, step in ((i, p), (p - i, p), (p, p),
                                (p + 2 * i, 2 * p), (p - 2 * i, 2 * p)):
                assert start > 0
                for exponent in range(start, limit + 1, step):
                    for n in range(limit, exponent - 1, -1):
                        coefficients[n] -= coefficients[n - exponent]
        watson = product_coefficients(p, indices, limit)
        assert all(value == watson.get(n, 0) for n, value in enumerate(coefficients))
        assert all(coefficients[p * n + residue] == 0 for n in range(depth + 1))
        assert coefficients[0] == 1 and coefficients[1] < 0
        cases.append({"t": t, "modulus": p, "indices": indices,
                      "zero_residue": residue, "progression_terms_checked": depth + 1,
                      "all_coefficients_compared": limit + 1})
    return {"date": "2026-11-01", "cases": cases,
            "arithmetic": "Python integers; direct factors versus bilateral Watson sums",
            "all_checks_passed": True,
            "sha256": {Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "quintuple_vanishing_scan.py": hashlib.sha256(Path(__file__).with_name(
                           "quintuple_vanishing_scan.py").read_bytes()).hexdigest()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parameters", type=int, default=6)
    parser.add_argument("--depth", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.parameters, args.depth)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
