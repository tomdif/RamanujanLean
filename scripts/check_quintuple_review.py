#!/usr/bin/env python3
"""Independent integer checks supporting the quintuple review manuscript.

Uses direct Pochhammer multiplication to check the Watson search and the
root classifier. Finite agreement is not used as an infinite vanishing proof.
"""
import argparse
import hashlib
from itertools import combinations
import json
from math import isqrt
from pathlib import Path

from classify_sparse_triple import classify
from generate_four97_converse import generate_files
from quintuple_vanishing_scan import primes_through, product_coefficients

ROOT = Path(__file__).resolve().parents[1]


def direct_product(p, indices, limit):
    coefficients = [1]+[0]*limit
    for i in indices:
        for start, step in ((i, p), (p-i, p), (p, p), (p+2*i, 2*p), (p-2*i, 2*p)):
            for exponent in range(start, limit+1, step):
                for degree in range(limit, exponent-1, -1):
                    coefficients[degree] -= coefficients[degree-exponent]
    return coefficients


def independent_roots(p, indices):
    """Enumerate the sphere directly, independently of centered scalar scanning."""
    targets = set()
    inverse_i = pow(indices[0], -1, p)
    for e in (1, 2):
        bound = isqrt(e*p)
        for x in range(-bound, bound+1):
            for y in range(-bound, bound+1):
                remaining = e*p-x*x-y*y
                if remaining < 0:
                    continue
                z = isqrt(remaining)
                if z*z != remaining:
                    continue
                for z in {z, -z}:
                    w = (x, y, z)
                    lam = x*inverse_i % p
                    if not lam or any((a-lam*b) % p for a, b in zip(w, indices)):
                        continue
                    u = sum(a*b for a, b in zip(w, indices))//p
                    for r in range(p):
                        base = 2*lam*r-sum(w)+6*u
                        if (base % p == 0 if e*p % 3 == 1 else
                                ((2//e)*lam*base-12) % p == 0):
                            targets.add(r)
    return targets


def check():
    cases, coefficients_checked = 0, 0
    for p in primes_through(43):
        for indices in combinations(range(1, (p+1)//2), 3):
            if sum(i*i for i in indices) % p:
                continue
            classified = classify(p, *indices)
            roots = set(classified['zero_residues'])
            assert roots == independent_roots(p, indices), (p, indices)
            # This is a finite consistency check, not the completeness proof.
            limit = p*(p+1)-1
            direct = direct_product(p, indices, limit)
            watson = product_coefficients(p, indices, limit)
            assert all(value == watson.get(n, 0) for n, value in enumerate(direct))
            observed = {r for r in range(p) if all(direct[p*n+r] == 0 for n in range(p+1))}
            assert observed == roots, (p, indices, roots, observed)
            cases += 1
            coefficients_checked += len(direct)
    invalid = ((9, 1, 2, 3), (13, 1, 1, 4), (13, 1, 3, 7), (13, 1, 2, 3))
    for parameters in invalid:
        try:
            classify(*parameters)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted inadmissible input: {parameters}")
    assert classify(31, 1, 5, 6)['zero_residues'] == [6, 16, 18]
    direct = direct_product(97, (5, 4, 9, 13), 97*16-1)
    watson = product_coefficients(97, (5, 4, 9, 13), len(direct)-1)
    assert all(value == watson.get(n, 0) for n, value in enumerate(direct))
    zeros = {9, 13, 55, 64}
    witnesses = []
    for r in range(97):
        if r in zeros:
            assert all(direct[97*n+r] == 0 for n in range(16))
        else:
            n = next(n for n in range(16) if direct[97*n+r])
            witnesses.append({"R": r, "N": n, "coefficient": direct[97*n+r]})
    assert max(w['N'] for w in witnesses) == 15
    assert all(direct[97*n+54] == 0 for n in range(15)) and direct[1509] == 1
    generated = generate_files()
    for name, source in generated.items():
        assert (ROOT/name).read_text() == source, f"generated Lean source is stale: {name}"
    paths = [Path(__file__), *(ROOT/name for name in generated), ROOT/'scripts/classify_sparse_triple.py',
             ROOT/'scripts/generate_four97_converse.py', ROOT/'scripts/quintuple_vanishing_scan.py']
    return {"scope": "Independent finite consistency checks; infinite conclusions are proved separately",
            "triple_census": {"prime_limit": 43, "admissible_triples": cases,
                              "direct_coefficients_compared": coefficients_checked,
                              "sphere_search_and_centered_scan_agree": True},
            "four97": {"direct_coefficients_compared": len(direct), "zero_residues": sorted(zeros),
                       "nonzero_witnesses": witnesses, "optimal_cutoff": 15,
                       "last_first_witness": {"R": 54, "N": 15, "coefficient": 1}},
            "generated_source_reproduced": True,
            "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({"triple_census": result['triple_census'],
                      "four97_witnesses": len(result['four97']['nonzero_witnesses']),
                      "optimal_cutoff": 15}, indent=2))
