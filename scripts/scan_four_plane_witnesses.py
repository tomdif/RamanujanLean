#!/usr/bin/env python3
"""Finite evidence for the converse of the two-parameter four-factor theorem.

For every eligible pair in the requested range, seek a nonzero coefficient
in every residue outside the four proved zero classes, through N=floor(p/4).
This does not prove a uniform converse or a uniform first-witness bound.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from check_four_plane import residues
from quintuple_vanishing_scan import product_coefficients


def scan(max_m):
    if max_m < 5:
        raise ValueError("max-m must be at least 5")
    cases = []
    for m in range(2, max_m+1):
        for n in range(1, m):
            p = m*m+n*n
            if (m+n) % 9 or gcd(n, 9) != 1 or gcd(6*n, p) != 1 or 2*(m+n) >= p:
                continue
            indices, predicted = (m-n, n, m, m+n), set(residues(m, n))
            depth = p//4
            coefficients = product_coefficients(p, indices, p*depth+p-1)
            witnesses, unresolved = [], []
            for r in range(p):
                if r in predicted:
                    assert all(coefficients.get(p*j+r, 0) == 0 for j in range(depth+1))
                    continue
                j = next((j for j in range(depth+1) if coefficients.get(p*j+r, 0)), None)
                if j is None:
                    unresolved.append(r)
                else:
                    witnesses.append((j, r, coefficients[p*j+r]))
            j, r, value = max(witnesses)
            cases.append({"m": m, "n": n, "modulus": p, "indices": indices,
                          "proved_zero_residues": sorted(predicted), "search_depth": depth,
                          "nonzero_residues_checked": len(witnesses), "unresolved_residues": unresolved,
                          "largest_first_witness": {"N": j, "R": r,
                                                    "exponent": p*j+r, "coefficient": value}})
            print(f"p={p}: {len(witnesses)} nonzero residues, "
                  f"largest first witness N={j}, unresolved={len(unresolved)}", flush=True)
    inputs = [Path(__file__), Path(__file__).with_name('check_four_plane.py'),
              Path(__file__).with_name('quintuple_vanishing_scan.py')]
    return {"scope": "Finite Python-integer experiment; not a Lean theorem or universal bound",
            "max_m": max_m, "all_converse_checks_passed": all(not c['unresolved_residues'] for c in cases),
            "cases": cases, "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, default=24)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = scan(args.max_m)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
