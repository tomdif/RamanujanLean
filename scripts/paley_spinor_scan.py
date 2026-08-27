#!/usr/bin/env python3
"""Exact reflective-lattice diagnostics for triple quintuple products.

For a distinct isotropic triple ``indices = (i,j,k)`` modulo an odd prime ``p``, a target
residue ``r``, and a bilateral branch vector ``bits in {0,1}^3``, the residue constraint

    i*(3*n1+b1) + j*(3*n2+b2) + k*(3*n3+b3) = r (mod p)

is solved by

    n3 = c1*n1 + c2*n2 + c0(bits,r) + p*v.

The homogeneous substitution defines the ternary lattice

    L_(p;i,j,k) = {(x,y,c1*x+c2*y+p*z) : x,y,z in Z}

with Gram matrix ``H = B^T B``.  This script exhaustively enumerates ``Aut(H)``.  For each
target residue it then searches for affine integral isometries pairing the four even-parity
bilateral branches with the four odd-parity branches.  Every accepted edge is checked with
exact integer/rational arithmetic; no floating point or heuristic lattice reduction is used.

The projective invariant

    J = sigma2^3 / sigma3^2 (mod p),

where ``sigma2 = i^2*j^2 + j^2*k^2 + k^2*i^2`` and
``sigma3 = i^2*j^2*k^2``, labels the signed-permutation/projective classes on the isotropic
conic.  If ``u=(j/i)^2``, then ``-256*J`` is the Legendre elliptic-curve j-invariant at
``lambda=-u``.

The automorphism census reveals a sharper arithmetic criterion.  Every reflective class
through ``p <= 401`` has a centered projective lift

    w = lambda*(i,j,k) (mod p),    ||w||^2 in {p, 2p},

and no nonreflective class has one.  Such a vector gives the Householder reflection
``x -> x - (2/e)*(x.w/p)*w``, where ``||w||^2=e*p``.  The construction is exact and the
forward implication is formalized in ``MultiQuintupleRootReflection.lean``.

The scan is experimental as a universal classification, but its affine certificates are exact.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import isqrt
from typing import Iterable

from quintuple_vanishing_scan import (
    parse_indices,
    primes_through,
    sum_of_squares,
    vanishing_residues,
)


Vector = tuple[int, int, int]
Matrix = tuple[Vector, Vector, Vector]
Branch = tuple[int, int, int]


def dot(left: Iterable[int | Fraction], right: Iterable[int | Fraction]) -> int | Fraction:
    return sum(a * b for a, b in zip(left, right))


def transpose(matrix: Matrix | list[list[Fraction]]) -> list[list[int | Fraction]]:
    return [list(column) for column in zip(*matrix)]


def matrix_vector(
    matrix: Matrix | list[list[Fraction]], vector: Iterable[int | Fraction]
) -> list[int | Fraction]:
    entries = list(vector)
    return [sum(row[j] * entries[j] for j in range(3)) for row in matrix]


def determinant(matrix: Matrix) -> int:
    a, b, c = matrix
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


def inverse_matrix(matrix: Matrix | list[list[int]]) -> list[list[Fraction]]:
    augmented = [
        [Fraction(matrix[row][column]) for column in range(3)]
        + [Fraction(row == column) for column in range(3)]
        for row in range(3)
    ]
    for column in range(3):
        pivot = next(row for row in range(column, 3) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [entry / scale for entry in augmented[column]]
        for row in range(3):
            if row == column:
                continue
            scale = augmented[row][column]
            augmented[row] = [
                augmented[row][entry] - scale * augmented[column][entry]
                for entry in range(6)
            ]
    return [row[3:] for row in augmented]


def canonical_residue(value: int, p: int) -> int:
    residue = value % p
    return min(residue, p - residue)


def projective_j_invariant(p: int, indices: tuple[int, int, int]) -> int:
    squares = tuple(index * index % p for index in indices)
    sigma2 = sum(squares[a] * squares[b] for a in range(3) for b in range(a + 1, 3)) % p
    sigma3 = squares[0] * squares[1] * squares[2] % p
    if sigma3 == 0:
        raise ValueError("J requires nonzero indices modulo p")
    return sigma2**3 * pow(sigma3 * sigma3, -1, p) % p


def legendre_elliptic_j(p: int, indices: tuple[int, int, int]) -> int:
    """The standard Legendre ``j`` at ``lambda=-(j/i)^2``."""
    return -256 * projective_j_invariant(p, indices) % p


def isotropic_j_representatives(p: int) -> dict[int, tuple[int, int, int]]:
    """One normalized distinct canonical triple for every observed projective J-class."""
    square_roots = {
        value * value % p: canonical_residue(value, p) for value in range(1, p)
    }
    representatives: dict[int, tuple[int, int, int]] = {}
    for x in range(2, (p + 1) // 2):
        y_square = (-1 - x * x) % p
        if y_square not in square_roots:
            continue
        triple = tuple(sorted((1, x, square_roots[y_square])))
        if len(set(triple)) < 3:
            continue
        representatives.setdefault(projective_j_invariant(p, triple), triple)
    return representatives


@dataclass(frozen=True)
class RestrictedLattice:
    p: int
    indices: tuple[int, int, int]
    c1: int
    c2: int
    basis: Matrix
    gram: Matrix


@dataclass(frozen=True)
class ShortProjectiveRoot:
    """A centered lift of the projective normal having norm ``p`` or ``2p``."""

    scalar: int
    vector: Vector
    norm_multiplier: int


def centered_projective_lift(
    p: int, scalar: int, indices: tuple[int, int, int]
) -> Vector:
    """The unique lift of ``scalar*indices`` whose coordinates lie in ``[-p/2,p/2]``."""
    return tuple(  # type: ignore[return-value]
        ((scalar * index + p // 2) % p) - p // 2 for index in indices
    )


def short_projective_roots(
    p: int, indices: tuple[int, int, int]
) -> list[ShortProjectiveRoot]:
    """All projective lifts ``w`` with ``||w||^2`` equal to ``p`` or ``2p``.

    Since either norm is less than ``p^2`` for odd ``p``, centering loses no possible root.
    The returned list contains both signs when a root exists.
    """
    roots: list[ShortProjectiveRoot] = []
    for scalar in range(1, p):
        vector = centered_projective_lift(p, scalar, indices)
        norm = int(dot(vector, vector))
        if norm in (p, 2 * p):
            roots.append(ShortProjectiveRoot(scalar, vector, norm // p))
    return roots


def short_root_reflection(root: ShortProjectiveRoot, p: int) -> list[list[Fraction]]:
    """The exact ambient Householder matrix attached to a short projective root."""
    coefficient = Fraction(2, root.norm_multiplier * p)
    return [
        [
            Fraction(row == column)
            - coefficient * root.vector[row] * root.vector[column]
            for column in range(3)
        ]
        for row in range(3)
    ]


def restricted_lattice(p: int, indices: tuple[int, int, int]) -> RestrictedLattice:
    i, j, k = indices
    inverse_k = pow(k, -1, p)
    c1 = -i * inverse_k % p
    c2 = -j * inverse_k % p
    # Columns are (1,0,c1), (0,1,c2), and (0,0,p).
    basis_columns: tuple[Vector, Vector, Vector] = ((1, 0, c1), (0, 1, c2), (0, 0, p))
    basis: Matrix = tuple(
        tuple(basis_columns[column][row] for column in range(3)) for row in range(3)
    )  # type: ignore[assignment]
    gram: Matrix = tuple(
        tuple(dot(basis_columns[row], basis_columns[column]) for column in range(3))
        for row in range(3)
    )  # type: ignore[assignment]
    return RestrictedLattice(p, indices, c1, c2, basis, gram)


def lattice_vectors_of_norm(lattice: RestrictedLattice, norm: int) -> list[tuple[Vector, Vector]]:
    """All coordinate/ambient vectors in the lattice having the requested Euclidean norm."""
    result: list[tuple[Vector, Vector]] = []
    radius = isqrt(norm)
    for x in range(-radius, radius + 1):
        remainder = norm - x * x
        y_radius = isqrt(remainder)
        for y in range(-y_radius, y_radius + 1):
            z_square = remainder - y * y
            ambient_z = isqrt(z_square)
            if ambient_z * ambient_z != z_square:
                continue
            candidates = (ambient_z,) if ambient_z == 0 else (ambient_z, -ambient_z)
            for third in candidates:
                numerator = third - lattice.c1 * x - lattice.c2 * y
                if numerator % lattice.p == 0:
                    result.append(((x, y, numerator // lattice.p), (x, y, third)))
    return result


def lattice_automorphisms(lattice: RestrictedLattice) -> list[Matrix]:
    """Exhaust ``A in GL(3,Z)`` satisfying ``A^T H A = H``."""
    candidates = [
        lattice_vectors_of_norm(lattice, lattice.gram[column][column])
        for column in range(3)
    ]
    automorphisms: dict[tuple[int, ...], Matrix] = {}
    for first_coordinates, first_ambient in candidates[0]:
        for second_coordinates, second_ambient in candidates[1]:
            if dot(first_ambient, second_ambient) != lattice.gram[0][1]:
                continue
            for third_coordinates, third_ambient in candidates[2]:
                if dot(first_ambient, third_ambient) != lattice.gram[0][2]:
                    continue
                if dot(second_ambient, third_ambient) != lattice.gram[1][2]:
                    continue
                matrix: Matrix = tuple(
                    tuple(column[row] for column in (first_coordinates, second_coordinates, third_coordinates))
                    for row in range(3)
                )  # type: ignore[assignment]
                if abs(determinant(matrix)) == 1:
                    automorphisms[tuple(entry for row in matrix for entry in row)] = matrix
    return list(automorphisms.values())


@dataclass(frozen=True)
class QuadraticPolynomial:
    quadratic: Matrix
    linear: Vector
    constant: int


def branch_polynomials(
    lattice: RestrictedLattice, residue: int
) -> dict[Branch, QuadraticPolynomial]:
    """Doubled product exponents after solving the target residue constraint."""
    p = lattice.p
    indices = lattice.indices
    inverse_3k = pow(3 * indices[2], -1, p)
    basis = lattice.basis
    quadratic: Matrix = tuple(
        tuple(3 * p * lattice.gram[row][column] for column in range(3))
        for row in range(3)
    )  # type: ignore[assignment]
    result: dict[Branch, QuadraticPolynomial] = {}
    for bits in product((0, 1), repeat=3):
        branch: Branch = bits
        c0 = inverse_3k * (residue - sum(i * bit for i, bit in zip(indices, branch))) % p
        displacement = (0, 0, c0)
        exponent_linear = tuple(
            6 * index + (2 * bit - 1) * p for index, bit in zip(indices, branch)
        )
        ambient_linear = tuple(
            6 * p * displacement[row] + exponent_linear[row] for row in range(3)
        )
        linear = tuple(
            sum(basis[row][column] * ambient_linear[row] for row in range(3))
            for column in range(3)
        )
        constant = (
            3 * p * dot(displacement, displacement)
            + dot(exponent_linear, displacement)
            + 2 * sum(index * bit for index, bit in zip(indices, branch))
        )
        result[branch] = QuadraticPolynomial(quadratic, linear, constant)
    return result


@dataclass(frozen=True)
class AffineEdge:
    source: Branch
    target: Branch
    matrix: Matrix
    translation: Vector


def affine_isometry(
    source: QuadraticPolynomial, target: QuadraticPolynomial, matrix: Matrix
) -> Vector | None:
    """Return integral ``c`` when ``target(A*x+c) = source(x)`` identically."""
    inverse_a_transpose = transpose(inverse_matrix(matrix))
    inverse_q = inverse_matrix(source.quadratic)
    transported_source = matrix_vector(inverse_a_transpose, source.linear)
    right_side = [transported_source[row] - target.linear[row] for row in range(3)]
    translation_fractional = [entry / 2 for entry in matrix_vector(inverse_q, right_side)]
    if any(entry.denominator != 1 for entry in translation_fractional):
        return None
    translation: Vector = tuple(int(entry) for entry in translation_fractional)  # type: ignore[assignment]
    transformed_constant = (
        dot(translation, matrix_vector(source.quadratic, translation))
        + dot(target.linear, translation)
        + target.constant
    )
    if transformed_constant != source.constant:
        return None
    return translation


def affine_branch_certificate(
    lattice: RestrictedLattice, automorphisms: list[Matrix], residue: int
) -> list[AffineEdge] | None:
    """Find a perfect even/odd branch matching by exact affine lattice isometries."""
    polynomials = branch_polynomials(lattice, residue)
    even = [branch for branch in polynomials if sum(branch) % 2 == 0]
    odd = [branch for branch in polynomials if sum(branch) % 2 == 1]
    edges: dict[tuple[Branch, Branch], AffineEdge] = {}
    for source in even:
        for target in odd:
            for matrix in automorphisms:
                translation = affine_isometry(polynomials[source], polynomials[target], matrix)
                if translation is not None:
                    edges[source, target] = AffineEdge(source, target, matrix, translation)
                    break

    def match(
        remaining: list[Branch], used: frozenset[Branch], chosen: list[AffineEdge]
    ) -> list[AffineEdge] | None:
        if not remaining:
            return chosen
        source = remaining[0]
        for target in odd:
            edge = edges.get((source, target))
            if target not in used and edge is not None:
                result = match(remaining[1:], used | {target}, chosen + [edge])
                if result is not None:
                    return result
        return None

    return match(even, frozenset(), [])


def format_matrix(matrix: Matrix) -> str:
    return "[" + ", ".join(str(list(row)) for row in matrix) + "]"


def validate_candidate(p: int, indices: tuple[int, ...]) -> tuple[int, int, int]:
    if len(indices) != 3:
        raise ValueError("reflective-lattice diagnostics currently require exactly three indices")
    triple = tuple(indices)
    if p < 5 or p % 2 == 0:
        raise ValueError("p must be odd and at least five")
    if len(set(triple)) != 3 or any(not 0 < 2 * index < p for index in triple):
        raise ValueError("indices must be distinct canonical residues 0 < i < p/2")
    return triple  # type: ignore[return-value]


def run_candidate(p: int, indices: tuple[int, ...], depth: int, show_all: bool) -> int:
    triple = validate_candidate(p, indices)
    square_sum = sum_of_squares(triple)
    print(f"p={p} indices={triple} sum(i^2)={square_sum} isotropic={square_sum % p == 0}")
    if square_sum % p:
        print("reflective criterion does not apply: the triple is not isotropic")
        return 1
    invariant = projective_j_invariant(p, triple)
    lattice = restricted_lattice(p, triple)
    automorphisms = lattice_automorphisms(lattice)
    roots = short_projective_roots(p, triple)
    observed, _ = vanishing_residues(p, triple, depth)
    print(f"J={invariant}; Legendre elliptic j={legendre_elliptic_j(p, triple)}")
    print(f"basis={format_matrix(lattice.basis)}")
    print(f"Gram={format_matrix(lattice.gram)}")
    print(f"|Aut(L)|={len(automorphisms)}; reflective={len(automorphisms) > 2}")
    print(
        "short projective roots="
        + str([(root.scalar, root.vector, root.norm_multiplier) for root in roots])
    )
    print(f"depth-{depth} candidate zero residues={observed}")
    status = 0
    residues = range(p) if show_all else observed
    certified: list[int] = []
    for residue in residues:
        certificate = affine_branch_certificate(lattice, automorphisms, residue)
        if certificate is None:
            continue
        certified.append(residue)
        print(f"certificate residue={residue}")
        for edge in certificate:
            print(
                f"  {edge.source} -> {edge.target}; A={format_matrix(edge.matrix)}; "
                f"c={edge.translation}"
            )
    print(f"affine-certified residues={tuple(certified)}")
    if any(residue not in certified for residue in observed):
        print("ERROR: an observed candidate zero has no affine certificate")
        status = 1
    return status


def run_scan(max_prime: int, depth: int) -> int:
    total_classes = 0
    mismatch_count = 0
    root_mismatch_count = 0
    uncertified_count = 0
    print(
        "p  J-classes  reflective  short-root  nonreflective  observed-hits  "
        "aut/root-mis  hit-mis  uncertified"
    )
    for p in primes_through(max_prime):
        representatives = isotropic_j_representatives(p)
        if not representatives:
            continue
        reflective_count = 0
        hit_count = 0
        prime_mismatches = 0
        prime_root_mismatches = 0
        prime_uncertified = 0
        root_count = 0
        for triple in representatives.values():
            lattice = restricted_lattice(p, triple)
            automorphisms = lattice_automorphisms(lattice)
            reflective = len(automorphisms) > 2
            has_short_root = bool(short_projective_roots(p, triple))
            observed, _ = vanishing_residues(p, triple, depth)
            hit = bool(observed)
            reflective_count += int(reflective)
            root_count += int(has_short_root)
            hit_count += int(hit)
            prime_mismatches += int(reflective != hit)
            prime_root_mismatches += int(reflective != has_short_root)
            if hit and any(
                affine_branch_certificate(lattice, automorphisms, residue) is None
                for residue in observed
            ):
                prime_uncertified += 1
        classes = len(representatives)
        total_classes += classes
        mismatch_count += prime_mismatches
        root_mismatch_count += prime_root_mismatches
        uncertified_count += prime_uncertified
        print(
            f"{p:<3}{classes:>11}{reflective_count:>12}{root_count:>12}"
            f"{classes-reflective_count:>15}{hit_count:>15}{prime_root_mismatches:>14}"
            f"{prime_mismatches:>9}{prime_uncertified:>13}"
        )
    print(
        f"total J-classes={total_classes}; automorphism/short-root mismatches={root_mismatch_count}; "
        f"reflective/hit mismatches={mismatch_count}; "
        f"observed zeros lacking affine certificates={uncertified_count}"
    )
    return int(bool(root_mismatch_count or mismatch_count or uncertified_count))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    candidate = subparsers.add_parser("candidate", help="inspect one isotropic triple")
    candidate.add_argument("--prime", type=int, required=True)
    candidate.add_argument("--indices", type=parse_indices, required=True)
    candidate.add_argument("--depth", type=int, default=160)
    candidate.add_argument(
        "--all-residues", action="store_true", help="search certificates in every residue"
    )

    scan = subparsers.add_parser("scan", help="compare reflectivity with coefficient scans")
    scan.add_argument("--max-prime", type=int, default=127)
    scan.add_argument("--depth", type=int, default=120)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if args.command == "candidate":
        return run_candidate(args.prime, args.indices, args.depth, args.all_residues)
    if args.command == "scan":
        return run_scan(args.max_prime, args.depth)
    raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
