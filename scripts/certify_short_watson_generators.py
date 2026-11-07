#!/usr/bin/env python3
"""Generate finite certificates for the short-generator converse argument.

Every normalized isotropic line for primes below 1250 is covered, without
identifying lines by their elliptic invariant.  Each successful entry lists
supported vectors of norm < p^2/2 whose maximal minors have gcd p^2.
The separate checker uses no LLL, scanner, SymPy, or FLINT.

This is a certificate generator, not a Lean proof of the converse.
"""
import argparse
import hashlib
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import time

import attack_phase_rigidity as attack


def determinant(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def small_generators(p, v):
    data = attack.shells_exact(p, v)
    assert data is not None, (p, v, "unexpected search cap")
    shells = data[0]
    vectors = [w for n, ws in shells if 2 * n < p * p for w in ws if w > tuple(-x for x in w)]
    chosen = []
    divisor = 0
    rank_basis = {}
    # Revisit vectors after rank three is reached: an initially dependent
    # vector can enlarge the integral span even when it does not enlarge
    # the rational span.
    for w in vectors + vectors:
        if len(chosen) < 2:
            if attack.s.add_to_rational_row_basis(rank_basis, w):
                chosen.append(w)
            continue
        new_divisor = divisor
        for a, b in combinations(chosen, 2):
            new_divisor = gcd(new_divisor, determinant((a, b, w)))
        if new_divisor != divisor:
            chosen.append(w)
            divisor = new_divisor
        if divisor == p * p:
            return chosen
    return None


def generate():
    entries = []
    exceptions = []
    for p in attack.sympy.primerange(5, 1250):
        square_roots = {k * k % p: k for k in range(1, (p + 1) // 2)}
        for j in range(2, (p + 1) // 2):
            k = square_roots.get((-1 - j * j) % p, 0)
            if not j < k:
                continue
            v = (1, j, k)
            generators = small_generators(p, v)
            if generators is None:
                exceptions.append([p, list(v)])
            else:
                entries.append([p, list(v), generators])
        if p % 100 < 4:
            print(f"through p={p}: {len(entries)} generator certificates", flush=True)
    assert exceptions and all(p == 13 for p, v in exceptions), exceptions
    small_cases = []
    for v in combinations(range(1, 7), 3):
        if sum(x * x for x in v) % 13:
            continue
        lattice = attack.s.restricted_lattice(13, v)
        roots = attack.s.short_projective_roots(13, v)
        targets = {attack.s.projective_root_target(root, lattice)[1] for root in roots}
        coefficients = attack.s.product_coefficients(13, v, 40)
        witnesses = []
        for r in range(13):
            if r not in targets:
                n, value = next((n, coefficients.get(13 * n + r, 0))
                                for n in range(3) if coefficients.get(13 * n + r, 0))
                witnesses.append([r, n, value])
        small_cases.append({"v": v, "roots": [
            {"w": root.vector, "lambda": root.scalar,
             "e": root.norm_multiplier, "R": attack.s.projective_root_target(root, lattice)[1]}
            for root in roots if root.vector > tuple(-x for x in root.vector)
        ], "nonzero_coefficients": witnesses})
    return {"date": "2026-11-01", "prime_upper_bound_exclusive": 1250,
            "normalization": "all (1,j,k) with 1<j<k<p/2 and 1+j^2+k^2=0 mod p",
            "short_generator_certificates": entries,
            "short_generator_exceptions": exceptions, "p13_cases": small_cases,
            "lean_checked": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    start = time.time()
    result = generate()
    result["generator_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print({"certificates": len(result["short_generator_certificates"]),
           "exceptions": result["short_generator_exceptions"],
           "p13_cases": len(result["p13_cases"]), "seconds": time.time() - start})
