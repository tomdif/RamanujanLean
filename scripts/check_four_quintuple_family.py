#!/usr/bin/env python3
"""Compare direct Pochhammer factors with Watson sums in the four-factor family.

Exact finite checks complement the all-parameter Lean theorem; they are not
the proof of the infinite zero progressions. Uses only the standard library.
"""
import argparse
import hashlib
import json
from pathlib import Path

from quintuple_vanishing_scan import product_coefficients


def check(parameters, depth):
    if parameters < 1 or depth < 0:
        raise ValueError("parameters must be positive and depth nonnegative")
    cases = []
    for t in range(parameters):
        p = 5184*t*t + 720*t + 41
        indices = (72*t+1, 72*t+5, 72*t+9, 4)
        residues = (2592*t*t+468*t+21, 3240*t*t+477*t+25,
                    1944*t*t+459*t+26, 2592*t*t+468*t+30)
        assert len(set(residues)) == 4 and all(0 <= r < p for r in residues)
        limit = p*depth + max(residues)
        coefficients = [1] + [0]*limit
        for i in indices:
            for start, step in ((i, p), (p-i, p), (p, p),
                                (p+2*i, 2*p), (p-2*i, 2*p)):
                assert start > 0
                for exponent in range(start, limit+1, step):
                    for degree in range(limit, exponent-1, -1):
                        coefficients[degree] -= coefficients[degree-exponent]
        watson = product_coefficients(p, indices, limit)
        assert all(value == watson.get(n, 0) for n, value in enumerate(coefficients))
        assert all(coefficients[p*n+r] == 0 for r in residues for n in range(depth+1))
        assert coefficients[0] == 1 and coefficients[min(indices)] == -1
        cases.append({"t": t, "modulus": p, "indices": indices,
                      "zero_residues": residues,
                      "terms_per_progression": depth+1,
                      "all_coefficients_compared": limit+1})
        print(f"t={t}, modulus={p}: all {limit+1} coefficients agree", flush=True)
    return {"arithmetic": "Python integers; direct Pochhammer factors versus Watson sums",
            "all_checks_passed": True, "cases": cases,
            "sha256": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in (Path(__file__), Path(__file__).with_name(
                           "quintuple_vanishing_scan.py"))}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parameters", type=int, default=5)
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.parameters, args.depth)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
