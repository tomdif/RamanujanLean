#!/usr/bin/env python3
"""Finite exploration of distinct isotropic four-factor tuples at small primes.

Surviving zero progressions are candidates, not infinite vanishing theorems.
"""
import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path
from quintuple_vanishing_scan import primes_through, product_coefficients


def scan(prime_limit):
    records = []
    for p in primes_through(prime_limit):
        checked, early, survivors = 0, 0, []
        for indices in combinations(range(1, (p+1)//2), 4):
            if sum(i*i for i in indices) % p:
                continue
            checked += 1
            depth = p//4
            coefficients = product_coefficients(p, indices, p*depth+p-1)
            candidates = [r for r in range(p) if all(coefficients.get(p*j+r, 0) == 0
                                                    for j in range(depth+1))]
            if not candidates:
                continue
            early += 1
            deep = product_coefficients(p, indices, p*(2*p)+p-1)
            remaining = [r for r in candidates if all(deep.get(p*j+r, 0) == 0
                                                     for j in range(2*p+1))]
            if remaining:
                survivors.append({"indices": indices, "zero_candidates": remaining})
        records.append({"prime": p, "tuples_checked": checked, "early_candidate_products": early,
                        "deep_search_N": 2*p, "deep_candidate_products": survivors})
        print(f'p={p}: {checked} tuples, {len(survivors)} surviving candidate products', flush=True)
    inputs = [Path(__file__), Path(__file__).with_name('quintuple_vanishing_scan.py')]
    return {"scope": "Finite scan only; distinct canonical indices with sum of squares divisible by the prime",
            "prime_limit": prime_limit, "tuples_checked": sum(r['tuples_checked'] for r in records),
            "surviving_candidate_products": sum(len(r['deep_candidate_products']) for r in records),
            "records": records,
            "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prime-limit', type=int, default=71)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = scan(args.prime_limit)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f"Checked {result['tuples_checked']} tuples; {result['surviving_candidate_products']} candidate products remain")
