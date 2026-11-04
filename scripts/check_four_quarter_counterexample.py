#!/usr/bin/env python3
"""Exact replay of a four-factor quarter-prime witness-bound counterexample.

This concerns the four-congruence four-factor family, not the original
triple-product conjecture. Two term enumerators and two pairings must agree.
This finite arithmetic certificate has not been formalized in Lean.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from itertools import product
from math import isqrt
from pathlib import Path
from quintuple_vanishing_scan import quintuple_terms, multiply_truncated

P, INDICES, RESIDUES, DEPTH = 2521, (1, 35, 36, 71), (67, 2273), 632


def independent_terms(i, limit):
    bound = isqrt(2*limit//P)+3
    coefficients = defaultdict(int)
    for n, b in product(range(-bound, bound+1), (0, 1)):
        doubled = 3*P*n*n+(2*b-1)*P*n+6*i*n+2*i*b
        assert doubled % 2 == 0
        exponent = doubled//2
        if 0 <= exponent <= limit:
            coefficients[exponent] += 1 if b == 0 else -1
    return {e: c for e, c in coefficients.items() if c}


def targeted_pair_sum(terms, pairing, limit):
    (i, j), (k, l) = pairing
    left = multiply_truncated(terms[i], terms[j], limit)
    right = multiply_truncated(terms[k], terms[l], limit)
    buckets = defaultdict(list)
    for exponent, coefficient in right.items():
        buckets[exponent % P].append((exponent, coefficient))
    results = {}
    for residue in RESIDUES:
        coefficients = [0]*(DEPTH+1)
        for exponent, coefficient in left.items():
            for other, weight in buckets[(residue-exponent) % P]:
                total = exponent+other
                if total <= limit:
                    step = (total-residue)//P
                    if 0 <= step <= DEPTH:
                        coefficients[step] += coefficient*weight
        results[residue] = coefficients
    return results


def check():
    assert all(P % d for d in range(2, isqrt(P)+1))
    assert P == 36**2+35**2 and 36 % 9 == 0
    assert all(0 < 2*i < P for i in INDICES)
    limit = P*DEPTH+max(RESIDUES)
    original = [quintuple_terms(P, i, limit) for i in INDICES]
    independent = [independent_terms(i, limit) for i in INDICES]
    assert original == independent
    first = targeted_pair_sum(original, ((0, 1), (2, 3)), limit)
    second = targeted_pair_sum(independent, ((0, 2), (1, 3)), limit)
    assert first == second
    cases = []
    for residue in RESIDUES:
        step = next(j for j, coefficient in enumerate(first[residue]) if coefficient)
        expected = (631, -1) if residue == 67 else (632, 1)
        assert (step, first[residue][step]) == expected
        assert all(value == 0 for value in first[residue][:step])
        assert step > P//4
        cases.append({"residue": residue, "first_nonzero_N": step,
                      "exponent": P*step+residue, "coefficient": first[residue][step],
                      "preceding_zero_terms_checked": step})
    inputs = [Path(__file__), Path(__file__).with_name('quintuple_vanishing_scan.py')]
    return {"scope": "Exact four-factor counterexample; original triple-product conjecture unaffected",
            "lean_checked": False, "all_checks_passed": True, "modulus": P, "indices": INDICES,
            "parameters": {"m": 36, "n": 35}, "quarter_bound": P//4,
            "terms_compared_per_residue": DEPTH+1,
            "independent_checks": ["monotone Watson enumerator versus bounded doubled-exponent enumerator",
                                   "pairings (0,1)|(2,3) and (0,2)|(1,3)"],
            "counterexamples": cases,
            "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
