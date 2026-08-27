#!/usr/bin/env python3
"""Exact experiments for products of specialized quintuple products.

For 0 < i < p/2, Watson's bilateral series gives

  Q(q^i, q^p) = sum_n (q^A(n) - q^B(n)),

where

  A(n) = p*n*(3*n-1)/2 + 3*i*n,
  B(n) = A(n) + i + p*n.

All arithmetic below is over Python integers.  No floating point expansions or
symbolic algebra packages are used.
"""

from __future__ import annotations

import argparse
from itertools import combinations, combinations_with_replacement
from math import isqrt
from typing import Iterable, Iterator


SparseSeries = dict[int, int]


KNOWN_EXAMPLES: tuple[tuple[int, tuple[int, ...], tuple[int, ...]], ...] = (
    (13, (1, 3, 4), (2, 4, 10)),
    (13, (2, 5, 6), (3, 9, 11)),
    (19, (2, 3, 5), (4, 5, 16)),
    (31, (1, 5, 6), (6, 16, 18)),
    (41, (1, 4, 5, 9), (21, 25, 26, 30)),
)


def primes_through(limit: int) -> Iterator[int]:
    for candidate in range(5, limit + 1):
        if all(candidate % divisor for divisor in range(2, isqrt(candidate) + 1)):
            yield candidate


def validate_specialization(p: int, i: int) -> None:
    if p < 5:
        raise ValueError("p must be at least 5")
    if not 0 < 2 * i < p:
        raise ValueError(f"expected a canonical index 0 < i < p/2, got p={p}, i={i}")


def quintuple_terms(p: int, i: int, limit: int) -> SparseSeries:
    """Return Q(q^i,q^p) exactly through q^limit as a sparse dictionary."""
    validate_specialization(p, i)
    if limit < 0:
        return {}

    result: SparseSeries = {}

    def add_term(exponent: int, coefficient: int) -> None:
        if 0 <= exponent <= limit:
            updated = result.get(exponent, 0) + coefficient
            if updated:
                result[exponent] = updated
            else:
                result.pop(exponent, None)

    # The two exponent sequences are increasing for n >= 0.
    n = 0
    while True:
        exponent_a = p * n * (3 * n - 1) // 2 + 3 * i * n
        exponent_b = exponent_a + i + p * n
        if exponent_a > limit and exponent_b > limit:
            break
        add_term(exponent_a, 1)
        add_term(exponent_b, -1)
        n += 1

    # With n = -m, both sequences are increasing for m >= 1 because i < p/2.
    m = 1
    while True:
        n = -m
        exponent_a = p * n * (3 * n - 1) // 2 + 3 * i * n
        exponent_b = exponent_a + i + p * n
        if exponent_a > limit and exponent_b > limit:
            break
        add_term(exponent_a, 1)
        add_term(exponent_b, -1)
        m += 1

    return result


def multiply_truncated(left: SparseSeries, right: SparseSeries, limit: int) -> SparseSeries:
    result: SparseSeries = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = left_exponent + right_exponent
            if exponent <= limit:
                result[exponent] = (
                    result.get(exponent, 0) + left_coefficient * right_coefficient
                )
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def product_coefficients(p: int, indices: Iterable[int], limit: int) -> SparseSeries:
    result = {0: 1}
    for i in indices:
        result = multiply_truncated(result, quintuple_terms(p, i, limit), limit)
    return result


def vanishing_residues(
    p: int, indices: tuple[int, ...], depth: int
) -> tuple[tuple[int, ...], SparseSeries]:
    """Residues whose coefficients vanish for q^(p*t+r), 0 <= t <= depth."""
    limit = p * depth + p - 1
    coefficients = product_coefficients(p, indices, limit)
    residues = tuple(
        residue
        for residue in range(p)
        if all(coefficients.get(p * t + residue, 0) == 0 for t in range(depth + 1))
    )
    return residues, coefficients


def first_nonzero_witnesses(p: int, coefficients: SparseSeries) -> dict[int, tuple[int, int]]:
    """Map each represented residue to its first (exponent, coefficient) witness."""
    witnesses: dict[int, tuple[int, int]] = {}
    for exponent in sorted(coefficients):
        residue = exponent % p
        witnesses.setdefault(residue, (exponent, coefficients[exponent]))
    return witnesses


def sum_of_squares(indices: tuple[int, ...]) -> int:
    return sum(i * i for i in indices)


def sigma_two_squares(indices: tuple[int, ...]) -> int:
    """Sum of pairwise products i^2*j^2."""
    return sum(
        indices[a] ** 2 * indices[b] ** 2
        for a in range(len(indices))
        for b in range(a + 1, len(indices))
    )


def quadratic_character(value: int, p: int) -> int:
    value %= p
    if value == 0:
        return 0
    return 1 if pow(value, (p - 1) // 2, p) == 1 else -1


def parse_indices(raw: str) -> tuple[int, ...]:
    try:
        result = tuple(int(part) for part in raw.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError("indices must be comma-separated integers") from error
    if not result:
        raise argparse.ArgumentTypeError("at least one index is required")
    return result


def run_known(depth: int) -> int:
    status = 0
    for p, indices, expected in KNOWN_EXAMPLES:
        actual, _ = vanishing_residues(p, indices, depth)
        matched = actual == expected
        status |= int(not matched)
        print(
            f"p={p:>2} indices={indices!s:<14} sumsq/p={sum_of_squares(indices) // p:<2} "
            f"zeros={actual} expected={expected} {'OK' if matched else 'MISMATCH'}"
        )
    return status


def run_candidate(p: int, indices: tuple[int, ...], depth: int) -> int:
    for i in indices:
        validate_specialization(p, i)
    residues, coefficients = vanishing_residues(p, indices, depth)
    square_sum = sum_of_squares(indices)
    sigma_two = sigma_two_squares(indices)
    print(f"p={p} indices={indices} depth={depth}")
    print(f"sum(i^2)={square_sum}; modulo p={square_sum % p}")
    print(
        f"sigma2={sigma_two}; quadratic character modulo p="
        f"{quadratic_character(sigma_two, p)}"
    )
    print(f"candidate vanishing residues={residues}")
    if not residues:
        witnesses = first_nonzero_witnesses(p, coefficients)
        if len(witnesses) == p:
            last_exponent = max(exponent for exponent, _ in witnesses.values())
            print(
                "finite non-vanishing certificate: every residue has a nonzero coefficient; "
                f"latest first witness is q^{last_exponent} (t={last_exponent // p})"
            )
        else:
            missing = tuple(sorted(set(range(p)) - set(witnesses)))
            print(f"residues not yet represented by a nonzero coefficient: {missing}")
    return 0


def run_canonical(p: int, depth: int) -> int:
    """Check the all-canonical product against the proved square-support prediction."""
    if p < 5 or p % 2 == 0:
        raise ValueError("canonical family expects an odd modulus p >= 5")
    indices = tuple(range(1, (p + 1) // 2))
    residues, _ = vanishing_residues(p, indices, depth)
    squares = {x * x % p for x in range(p)}
    predicted = tuple(residue for residue in range(p) if residue not in squares)
    matched = residues == predicted
    print(f"p={p} indices=1..{indices[-1]} depth={depth}")
    print(f"nonsquare residues={predicted}")
    print(f"candidate vanishing residues={residues}")
    print("MATCH" if matched else "MISMATCH")
    return int(not matched)


def run_scan(max_prime: int, arity: int, depth: int, allow_repeats: bool) -> int:
    chooser = combinations_with_replacement if allow_repeats else combinations
    print(
        "p  candidates  hits  misses  sigma2=-1(hit/total)  "
        "sigma2=0(hit/total)  sigma2=1(hit/total)"
    )
    for p in primes_through(max_prime):
        buckets = {-1: [0, 0], 0: [0, 0], 1: [0, 0]}
        candidate_count = 0
        hit_count = 0
        for indices in chooser(range(1, (p + 1) // 2), arity):
            if sum_of_squares(indices) % p:
                continue
            candidate_count += 1
            residues, _ = vanishing_residues(p, indices, depth)
            hit = bool(residues)
            hit_count += int(hit)
            character = quadratic_character(sigma_two_squares(indices), p)
            buckets[character][0] += int(hit)
            buckets[character][1] += 1
        if candidate_count:
            formatted = "  ".join(f"{buckets[c][0]}/{buckets[c][1]}" for c in (-1, 0, 1))
            print(
                f"{p:<3}{candidate_count:>10}{hit_count:>6}"
                f"{candidate_count - hit_count:>8}  {formatted}"
            )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    known = subparsers.add_parser("known", help="reproduce the five published examples")
    known.add_argument("--depth", type=int, default=160)

    candidate = subparsers.add_parser("candidate", help="inspect one product")
    candidate.add_argument("--prime", type=int, required=True)
    candidate.add_argument("--indices", type=parse_indices, required=True)
    candidate.add_argument("--depth", type=int, default=120)

    canonical = subparsers.add_parser(
        "canonical", help="check the proved all-canonical nonsquare family"
    )
    canonical.add_argument("--prime", type=int, required=True)
    canonical.add_argument("--depth", type=int, default=80)

    scan = subparsers.add_parser("scan", help="scan sum-of-squares candidates")
    scan.add_argument("--max-prime", type=int, default=97)
    scan.add_argument("--arity", type=int, default=3)
    scan.add_argument("--depth", type=int, default=80)
    scan.add_argument("--allow-repeats", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if args.command == "known":
        return run_known(args.depth)
    if args.command == "candidate":
        return run_candidate(args.prime, args.indices, args.depth)
    if args.command == "canonical":
        return run_canonical(args.prime, args.depth)
    if args.command == "scan":
        return run_scan(args.max_prime, args.arity, args.depth, args.allow_repeats)
    raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
