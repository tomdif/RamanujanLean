#!/usr/bin/env python3
"""Exact checks for the prime-index lattice reflection argument.

These are bounded arithmetic checks, not a Lean proof of the general theorem.
The automorphism enumerator is independent of the proposed extraction rule.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import reduce
import hashlib
import json
from math import gcd, isqrt, lcm
from pathlib import Path

from paley_spinor_scan import (
    determinant, inverse_matrix, is_plane_reflection, isotropic_j_representatives,
    lattice_automorphisms, matrix_key, matrix_multiply, primes_through,
    restricted_lattice, short_projective_roots, short_root_reflection,
    ShortProjectiveRoot,
)

IDENTITY = [[Fraction(i == j) for j in range(3)] for i in range(3)]


def power(matrix, exponent):
    result = IDENTITY
    for _ in range(exponent):
        result = matrix_multiply(result, matrix)
    return result


def projective(p, normal, vector):
    scalar = vector[0] * pow(normal[0], -1, p) % p
    return scalar != 0 and all((x - scalar * y) % p == 0
                               for x, y in zip(vector, normal))


def eisenstein_root(p, normal):
    """Construct a norm-2p lift on an isotropic line in x+y+z=0."""
    assert sum(normal) % p == 0
    assert sum(x * x for x in normal) % p == 0
    for b in range(isqrt(4 * p // 3) + 1):
        discriminant = 4 * p - 3 * b * b
        d = isqrt(discriminant)
        if d * d == discriminant and (b + d) % 2 == 0:
            a = (b + d) // 2
            assert a * a - a * b + b * b == p
            vector = (a, b - a, -b)
            for candidate in (vector, (vector[1], vector[0], vector[2])):
                if projective(p, normal, candidate):
                    return candidate
    raise AssertionError(("no Eisenstein root", p, normal))


def primitive_normal(reflection):
    column = next(j for j in range(3)
                  if any(IDENTITY[i][j] != reflection[i][j] for i in range(3)))
    vector = [IDENTITY[i][column] - reflection[i][column] for i in range(3)]
    denominator = lcm(*(x.denominator for x in vector))
    integral = [int(x * denominator) for x in vector]
    content = reduce(gcd, integral)
    return tuple(x // content for x in integral)


def verify(max_prime, eisenstein_bound):
    counts = Counter()
    orders = Counter()
    examples = {}
    for p in primes_through(max_prime):
        for invariant, normal in isotropic_j_representatives(p).items():
            lattice = restricted_lattice(p, normal)
            inverse = inverse_matrix(lattice.basis)
            automorphisms = lattice_automorphisms(lattice)
            ambient = [matrix_multiply(matrix_multiply(lattice.basis, g), inverse)
                       for g in automorphisms]
            keys = {matrix_key(g) for g in ambient}
            root_keys = {matrix_key(short_root_reflection(root, p))
                         for root in short_projective_roots(p, normal)}
            reflection_keys = {matrix_key(g) for g in ambient if is_plane_reflection(g)}
            assert reflection_keys == root_keys
            counts["classes"] += 1
            counts["noncentral_classes"] += len(automorphisms) > 2
            for g in ambient:
                counts["automorphisms"] += 1
                assert all((p * x).denominator == 1 for row in g for x in row)
                skew = [[g[i][j] - g[j][i] for j in range(3)] for i in range(3)]
                assert all(x.denominator == 1 for row in skew for x in row)
                sign = determinant(g)
                rotation = [[sign * x for x in row] for row in g]
                order = next(n for n in range(1, 7) if power(rotation, n) == IDENTITY)
                orders[order] += 1
                if order == 1:
                    continue
                if order == 3:
                    axis = tuple(int(rotation[i][j] - rotation[j][i])
                                 for i, j in ((2, 1), (0, 2), (1, 0)))
                    assert all(abs(x) == 1 for x in axis)
                    assert all(x.denominator == 1 for row in rotation for x in row)
                    assert invariant == 0 and p % 3 == 1
                    transformed = tuple(axis[i] * normal[i] % p for i in range(3))
                    root = eisenstein_root(p, transformed)
                    vector = tuple(axis[i] * root[i] for i in range(3))
                    norm = 2 * p
                    counts["order_three_extractions"] += 1
                else:
                    assert order % 2 == 0
                    reflection = [[-x for x in row] for row in power(rotation, order // 2)]
                    assert is_plane_reflection(reflection)
                    vector = primitive_normal(reflection)
                    norm = sum(x * x for x in vector)
                    counts["even_order_extractions"] += 1
                assert norm in (p, 2 * p)
                assert sum(x * x for x in vector) == norm
                assert projective(p, normal, vector)
                root = ShortProjectiveRoot(vector[0] * pow(normal[0], -1, p) % p,
                                           vector, norm // p)
                assert matrix_key(short_root_reflection(root, p)) in keys & root_keys
                examples.setdefault(str(order), {"prime": p, "normal": normal,
                                                 "extracted_root": vector, "norm": norm})
        print(f"checked p={p}, classes={counts['classes']}", flush=True)

    for p in primes_through(eisenstein_bound):
        if p % 3 != 1:
            continue
        a = 2
        while pow(a, (p - 1) // 3, p) == 1:
            a += 1
        omega = pow(a, (p - 1) // 3, p)
        vector = eisenstein_root(p, (1, omega, omega * omega % p))
        assert sum(x * x for x in vector) == 2 * p
        counts["eisenstein_primes"] += 1

    # A rational order-three rotation need not be integral without the lattice lemma.
    axis = (1, 1, 5)
    cross = [[0, -5, 1], [5, 0, -1], [-1, 1, 0]]
    rational_rotation = [[-IDENTITY[i][j] / 2 + Fraction(axis[i] * axis[j], 18)
                          + Fraction(cross[i][j], 6) for j in range(3)] for i in range(3)]
    assert power(rational_rotation, 3) == IDENTITY
    assert determinant(rational_rotation) == 1
    assert any((rational_rotation[i][j] - rational_rotation[j][i]).denominator != 1
               for i in range(3) for j in range(3))
    return {"date": "2026-11-01", "max_prime": max_prime,
            "eisenstein_bound": eisenstein_bound, "counts": dict(counts),
            "normalized_rotation_orders": dict(sorted(orders.items())), "examples": examples,
            "nonintegral_order_three_control_passed": True,
            "all_checks_passed": True, "general_theorem_checked_in_lean": False,
            "sha256": {str(Path(__file__).name): hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "paley_spinor_scan.py": hashlib.sha256(Path(__file__).with_name(
                           "paley_spinor_scan.py").read_bytes()).hexdigest()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-prime", type=int, default=127)
    parser.add_argument("--eisenstein-bound", type=int, default=10000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.max_prime, args.eisenstein_bound)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
