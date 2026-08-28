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
through ``p <= 1000`` has a centered projective lift

    w = lambda*(i,j,k) (mod p),    ||w||^2 in {p, 2p},

and no nonreflective class has one.  Such a vector gives the Householder reflection
``x -> x - (2/e)*(x.w/p)*w``, where ``||w||^2=e*p``.  The construction is exact and the
forward implication is formalized in ``MultiQuintupleRootReflection.lean``.

The scan is experimental as a universal classification, but its affine certificates are exact.
Finite coefficient silence is reported separately and is never treated as a proof of vanishing.

The ``dual-shell-scan`` command supplies a separate Poisson-dual diagnostic.  It factors each
individual Watson-character amplitude, enumerates certified-complete short norm shells, and decides
their ``6p``-th-root amplitudes exactly in ``Q(zeta_3)(zeta_p)``.  It also exposes exact
counterexamples to fixed finite-shell cutoffs; bounded agreement is never treated as a universal
rigidity proof.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import isqrt
from typing import Iterable

from quintuple_vanishing_scan import (
    parse_indices,
    primes_through,
    product_coefficients,
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


def matrix_multiply(
    left: Matrix | list[list[int | Fraction]],
    right: Matrix | list[list[int | Fraction]],
) -> list[list[int | Fraction]]:
    """Multiply two exact 3-by-3 matrices."""
    return [
        [sum(left[row][middle] * right[middle][column] for middle in range(3))
         for column in range(3)]
        for row in range(3)
    ]


def matrix_key(matrix: Matrix | list[list[int | Fraction]]) -> tuple[Fraction, ...]:
    """Hashable exact key for a 3-by-3 matrix."""
    return tuple(Fraction(entry) for row in matrix for entry in row)


def is_plane_reflection(matrix: Matrix) -> bool:
    """Recognize an exact three-dimensional plane reflection."""
    identity = [[Fraction(row == column) for column in range(3)] for row in range(3)]
    square = matrix_multiply(matrix, matrix)
    return (
        determinant(matrix) == -1
        and sum(matrix[index][index] for index in range(3)) == 1
        and square == identity
    )


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


def signed_short_root_lattice_matrix(
    lattice: RestrictedLattice, root: ShortProjectiveRoot, sign: int
) -> Matrix:
    """Write ``sign*R_root`` in the integral basis of the congruence lattice."""
    if sign not in (-1, 1):
        raise ValueError("reflection sign must be +1 or -1")
    ambient = [
        [sign * entry for entry in row]
        for row in short_root_reflection(root, lattice.p)
    ]
    coordinates = matrix_multiply(
        matrix_multiply(inverse_matrix(lattice.basis), ambient), lattice.basis
    )
    if any(entry.denominator != 1 for row in coordinates for entry in row):
        raise AssertionError("short projective root did not preserve its congruence lattice")
    return tuple(tuple(int(entry) for entry in row) for row in coordinates)  # type: ignore[return-value]


def projective_root_target(root: ShortProjectiveRoot, lattice: RestrictedLattice) -> tuple[int, int]:
    """Return the signed reflection and its predicted vanishing residue.

    Put ``v=indices``, ``w=root.vector``, and ``u=(v.w)/p``.  For the positive
    reflection the target law is

        ``2*lambda*r = sum(w)-6*u (mod p)``.

    For the negative reflection, with ``c=2/e``, it is

        ``c*lambda*(2*lambda*r-sum(w)+6*u) = 12 (mod p)``.

    The sign is selected by ``e*p mod 3``.  These formulas are formalized in
    ``MultiQuintupleRootVanishingEquivalence.lean``.
    """
    p = lattice.p
    scalar = root.scalar
    e = root.norm_multiplier
    pairing = int(dot(lattice.indices, root.vector))
    if pairing % p:
        raise AssertionError("projective root pairing was not divisible by p")
    u = pairing // p
    offset = sum(root.vector) - 6 * u
    inverse_two_scalar = pow(2 * scalar, -1, p)
    ep_mod_three = e * p % 3
    if ep_mod_three == 1:
        return 1, offset * inverse_two_scalar % p
    if ep_mod_three == 2:
        c = 2 // e
        negative_base = 12 * pow(c * scalar, -1, p) % p
        return -1, (offset + negative_base) * inverse_two_scalar % p
    raise ValueError("root transport requires p not divisible by 3")


def projective_root_branch_certificate(
    lattice: RestrictedLattice, root: ShortProjectiveRoot
) -> tuple[int, int, list[AffineEdge] | None]:
    """Check the exact affine certificate predicted by one short projective root."""
    sign, residue = projective_root_target(root, lattice)
    matrix = signed_short_root_lattice_matrix(lattice, root, sign)
    return sign, residue, affine_branch_certificate(lattice, [matrix], residue)


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


def six_p_cyclotomic_sum_is_zero(p: int, terms: Counter[int]) -> bool:
    """Decide an integral sum of ``6p``-th roots of unity exactly.

    ``terms[e]`` is the coefficient of ``zeta_(6p)^e``.  For odd
    ``p != 3``, the fields ``Q(zeta_(6p))`` and ``Q(zeta_(3p))`` agree.
    We first write ``zeta_(6p)`` as a signed power of ``zeta_(3p)`` and
    then use

    ``Q(zeta_(3p)) = Q(zeta_3)(zeta_p)``.

    The only relation among ``1,zeta_p,...,zeta_p^(p-1)`` over
    ``Q(zeta_3)`` is their sum.  Coefficients in ``Z[zeta_3]`` are stored
    as pairs in the basis ``(1,zeta_3)``.  Thus the original cyclotomic
    sum is zero exactly when all ``p`` coefficient pairs are equal.
    """
    if p % 2 == 0 or p % 3 == 0:
        raise ValueError("the 6p cyclotomic reduction requires odd p != 3")
    modulus = 6 * p
    modulus_3p = 3 * p
    # zeta_(6p) = -zeta_(3p)^a, where 2a = 1-3p (mod 6p).
    exponent_multiplier = ((1 - 3 * p) // 2) % modulus_3p
    cube_component = pow(p, -1, 3)
    p_component = pow(3, -1, p)
    coefficients: dict[int, list[int]] = {}
    cube_basis = ((1, 0), (0, 1), (-1, -1))
    for exponent, coefficient in terms.items():
        if not coefficient:
            continue
        exponent %= modulus
        sign = -1 if exponent % 2 else 1
        exponent_3p = exponent_multiplier * exponent % modulus_3p
        cube_exponent = cube_component * exponent_3p % 3
        prime_exponent = p_component * exponent_3p % p
        first, second = cube_basis[cube_exponent]
        pair = coefficients.setdefault(prime_exponent, [0, 0])
        pair[0] += sign * coefficient * first
        pair[1] += sign * coefficient * second
    nonzero_coefficients = [
        tuple(pair) for pair in coefficients.values() if pair != [0, 0]
    ]
    if not nonzero_coefficients:
        return True
    # A missing prime-exponent coefficient is zero, so equality of all p
    # coefficients is then impossible.  This sparse branch is the common one:
    # the dual amplitudes below contain at most eight roots of unity.
    if len(nonzero_coefficients) < p:
        return False
    return all(
        coefficient == nonzero_coefficients[0]
        for coefficient in nonzero_coefficients[1:]
    )


def dual_character_amplitude_terms(
    lattice: RestrictedLattice,
    residue: int,
    vector: Vector,
) -> Counter[int]:
    """The exact Fourier amplitude of one projective dual vector.

    The completed branch polynomials have a common quadratic part and a
    common completed-square constant.  Their centers differ by rational
    vectors with denominator dividing ``6p``.  The signed Fourier amplitude
    is therefore an integral sum of ``6p``-th roots of unity.
    """
    p = lattice.p
    indices = lattice.indices
    pairing = int(dot(indices, vector))
    if pairing % p:
        raise AssertionError("projective vector did not lie in the integral dual lattice")
    inverse_3k = pow(3 * indices[2], -1, p)
    terms: Counter[int] = Counter()
    for branch in product((0, 1), repeat=3):
        c0 = inverse_3k * (
            residue - sum(index * bit for index, bit in zip(indices, branch))
        ) % p
        # If x is the completed-square center, direct cancellation of the
        # lattice basis in ``6p * <B^T*w/p, x>`` gives this integral formula.
        phase = (
            6 * vector[2] * c0
            + 6 * (pairing // p)
            + sum(vector[index] * (2 * branch[index] - 1) for index in range(3))
        )
        terms[phase % (6 * p)] += (-1) ** sum(branch)
    return Counter(
        {exponent: coefficient for exponent, coefficient in terms.items() if coefficient}
    )


def dual_character_amplitude_is_supported(
    lattice: RestrictedLattice, vector: Vector
) -> bool:
    """Decide whether one dual vector carries nonzero Watson character.

    Modulo ``6p``, the branch phase is affine in the three branch bits.
    Hence its signed eight-term sum factors as

    ``zeta^C * product_s (1 - zeta^delta_s)``, where
    ``delta_s = 2*w_s - 6*w_3*(3*k)^(-1)*i_s``.

    A product in the cyclotomic field is nonzero exactly when none of the
    three factors vanishes.  The condition is independent of the target
    residue.
    """
    p = lattice.p
    modulus = 6 * p
    inverse_3k = pow(3 * lattice.indices[2], -1, p)
    return all(
        (
            2 * vector[index]
            - 6 * vector[2] * inverse_3k * lattice.indices[index]
        )
        % modulus
        != 0
        for index in range(3)
    )


def first_dual_character_shells(
    lattice: RestrictedLattice, shell_count: int, shift_radius: int
) -> tuple[list[tuple[int, tuple[Vector, ...]]], int]:
    """Enumerate the first dual norm shells carrying the Watson character.

    A dual vector is represented integrally by ``w congruent lambda*(i,j,k)
    (mod p)``.  Centering the projective lift and then adding ``p*z`` is
    exhaustive.  The returned lower bound is the norm of every vector omitted
    by the requested shift radius, so it certifies completeness of the
    selected shells when their norms are smaller.
    """
    if shell_count <= 0 or shift_radius < 0:
        raise ValueError("shell count must be positive and shift radius nonnegative")
    p = lattice.p
    shells: dict[int, set[Vector]] = {}
    shifts = range(-shift_radius, shift_radius + 1)
    modulus = 6 * p
    inverse_3k = pow(3 * lattice.indices[2], -1, p)
    for scalar in range(p):
        base = (0, 0, 0) if scalar == 0 else centered_projective_lift(
            p, scalar, lattice.indices
        )
        # The support factor indexed by ``s`` depends on the shift in
        # coordinate ``s`` modulo three.  A shift of the third coordinate in
        # the cross term contributes a multiple of ``6p`` and is invisible.
        # We can therefore discard unsupported coordinate shifts before
        # taking their Cartesian product (eight rather than 27 choices when
        # ``shift_radius=1``).
        supported_shifts: list[tuple[int, ...]] = []
        for index in range(3):
            coordinate_shifts: list[int] = []
            for shift in shifts:
                shifted_coordinate = base[index] + p * shift
                third_coordinate = shifted_coordinate if index == 2 else base[2]
                delta = (
                    2 * shifted_coordinate
                    - 6
                    * third_coordinate
                    * inverse_3k
                    * lattice.indices[index]
                ) % modulus
                if delta:
                    coordinate_shifts.append(shift)
            supported_shifts.append(tuple(coordinate_shifts))
        for shift in product(*supported_shifts):
            vector: Vector = tuple(  # type: ignore[assignment]
                base[index] + p * shift[index] for index in range(3)
            )
            if vector == (0, 0, 0):
                continue
            norm = int(dot(vector, vector))
            if norm % p:
                raise AssertionError("dual norm was not divisible by the isotropic prime")
            shells.setdefault(norm, set()).add(vector)
    selected = [
        (norm, tuple(sorted(shells[norm]))) for norm in sorted(shells)[:shell_count]
    ]
    # An omitted shift has some coordinate at distance at least
    # ``(shift_radius + 1/2)*p`` from zero.  Avoid fractions by flooring the
    # strict lower bound; selected norms must be strictly smaller.
    omitted_norm_lower_bound = ((2 * shift_radius + 1) * p) ** 2 // 4
    return selected, omitted_norm_lower_bound


def dual_shell_amplitude_is_zero(
    lattice: RestrictedLattice, residue: int, vectors: tuple[Vector, ...]
) -> bool:
    """Decide one complete dual-shell amplitude exactly."""
    terms: Counter[int] = Counter()
    for vector in vectors:
        terms.update(dual_character_amplitude_terms(lattice, residue, vector))
    return six_p_cyclotomic_sum_is_zero(lattice.p, terms)


def run_dual_shell_candidate(
    p: int,
    indices: tuple[int, ...],
    residue: int,
    shell_count: int,
    shift_radius: int,
) -> int:
    """Print an exact, auditable dual-shell certificate for one residue."""
    triple = validate_candidate(p, indices)
    if p not in primes_through(p):
        print(f"p={p} is not prime; the cyclotomic certificate requires a prime")
        return 1
    if sum_of_squares(triple) % p:
        print(f"p={p} triple={triple} is not isotropic")
        return 1
    lattice = restricted_lattice(p, triple)
    roots = short_projective_roots(p, triple)
    root_targets = sorted(
        {projective_root_target(root, lattice)[1] for root in roots}
    )
    shells, omitted_norm_lower_bound = first_dual_character_shells(
        lattice, shell_count + 1, shift_radius
    )
    complete = bool(shells) and (
        4 * shells[-1][0] < ((2 * shift_radius + 1) * p) ** 2
    )
    print(
        f"p={p} triple={triple} residue={residue % p}; "
        f"root-targets={root_targets}; omitted-norm-lower-bound="
        f"{omitted_norm_lower_bound}; listed-shells-complete={complete}"
    )
    common_zero = True
    for number, (norm, vectors) in enumerate(shells, 1):
        terms: Counter[int] = Counter()
        for vector in vectors:
            terms.update(dual_character_amplitude_terms(lattice, residue % p, vector))
        terms = Counter(
            {exponent: coefficient for exponent, coefficient in terms.items() if coefficient}
        )
        zero = six_p_cyclotomic_sum_is_zero(p, terms)
        if number <= shell_count:
            common_zero = common_zero and zero
        print(
            f"shell={number}; norm={norm}={norm // p}p; vectors={vectors}; "
            f"phase-terms={dict(sorted(terms.items()))}; exact-zero={zero}"
        )
    print(
        f"first-{shell_count}-shells-common-zero={common_zero}; "
        f"residue-is-root-target={residue % p in root_targets}"
    )
    coefficient_limit = p * (p // 4) + p - 1
    coefficients = product_coefficients(p, triple, coefficient_limit)
    product_witness = next(
        (
            (exponent // p, exponent, coefficient)
            for exponent, coefficient in sorted(coefficients.items())
            if exponent % p == residue % p and coefficient
        ),
        None,
    )
    print(f"first-product-witness-through-N<=p/4={product_witness}")
    return int(not complete)


def dual_residue_phase_step(lattice: RestrictedLattice, vector: Vector) -> int:
    """The common ``6p``-phase increment when the target residue increases by one.

    Solving the congruence changes the third affine displacement by
    ``(3*k)^(-1)`` modulo ``p``.  Its possible branch-dependent wrap is a
    multiple of ``p`` and hence invisible to the ``6p``-th root phase.  Thus
    all eight branch terms belonging to ``vector`` acquire this same phase.
    """
    p = lattice.p
    inverse_3k = pow(3 * lattice.indices[2], -1, p)
    return 6 * vector[2] * inverse_3k % (6 * p)


def shift_cyclotomic_terms(
    terms: Counter[int], phase: int, modulus: int
) -> Counter[int]:
    """Multiply a root-of-unity sum by one root of unity."""
    shifted: Counter[int] = Counter()
    for exponent, coefficient in terms.items():
        shifted[(exponent + phase) % modulus] += coefficient
    return shifted


def run_dual_shell_rigidity_scan(
    max_prime: int, shell_count: int, shift_radius: int, min_prime: int = 5
) -> int:
    """Compare exact short-root targets with exact dual-shell cancellation.

    Poisson summation turns an identically zero progression theta series into
    cancellation on every complete dual norm shell.  This command asks whether
    the first ``shell_count`` Watson-supported shells already force exactly the
    residues supplied by short projective roots.  Every cyclotomic zero test is
    exact.  The finite vector box is accepted only when a geometric lower bound
    proves that all selected shells are complete.

    Agreement is only a bounded result.  A mismatch is an exact counterexample
    to the requested fixed shell cutoff; four shells first fail at ``p=1439``
    and five first fail at ``p=1523``.
    """
    classes = 0
    residues = 0
    incomplete_classes = 0
    mismatches: list[
        tuple[int, tuple[int, int, int], tuple[int, ...], tuple[int, ...]]
    ] = []
    shell_norm_profiles: Counter[tuple[int, ...]] = Counter()
    for p in primes_through(max_prime):
        if p < min_prime or p == 3:
            continue
        for triple in isotropic_j_representatives(p).values():
            classes += 1
            residues += p
            lattice = restricted_lattice(p, triple)
            shells, omitted_norm_lower_bound = first_dual_character_shells(
                lattice, shell_count, shift_radius
            )
            if (
                len(shells) < shell_count
                or 4 * shells[-1][0] >= ((2 * shift_radius + 1) * p) ** 2
            ):
                incomplete_classes += 1
                print(
                    f"INCOMPLETE: p={p} triple={triple} shells={len(shells)} "
                    f"last-norm={shells[-1][0] if shells else None} "
                    f"omitted-lower-bound={omitted_norm_lower_bound}"
                )
                continue
            shell_norm_profiles[
                tuple(norm // p for norm, _vectors in shells)
            ] += 1
            affine_shell_terms = [
                tuple(
                    (
                        dual_character_amplitude_terms(lattice, 0, vector),
                        dual_residue_phase_step(lattice, vector),
                    )
                    for vector in vectors
                )
                for _norm, vectors in shells
            ]
            common_zeros: set[int] = set()
            for residue in range(p):
                all_shells_zero = True
                for vector_terms in affine_shell_terms:
                    terms: Counter[int] = Counter()
                    for base_terms, phase_step in vector_terms:
                        terms.update(
                            shift_cyclotomic_terms(
                                base_terms, residue * phase_step, 6 * p
                            )
                        )
                    if not six_p_cyclotomic_sum_is_zero(p, terms):
                        all_shells_zero = False
                        break
                if all_shells_zero:
                    common_zeros.add(residue)
            root_targets = {
                projective_root_target(root, lattice)[1]
                for root in short_projective_roots(p, triple)
            }
            if common_zeros != root_targets:
                mismatch = (
                    p,
                    triple,
                    tuple(sorted(root_targets)),
                    tuple(sorted(common_zeros)),
                )
                mismatches.append(mismatch)
                print(
                    f"MISMATCH: p={p} triple={triple} "
                    f"root-targets={mismatch[2]} shell-common-zeros={mismatch[3]}"
                )
    print(
        f"classes={classes}; residues={residues}; shells={shell_count}; "
        f"shift-radius={shift_radius}; incomplete={incomplete_classes}; "
        f"mismatches={len(mismatches)}"
    )
    maximum_last_multiplier = max(
        (profile[-1] for profile in shell_norm_profiles if profile), default=None
    )
    print(
        f"distinct shell norm-multiplier profiles={len(shell_norm_profiles)}; "
        f"largest selected-shell multiplier={maximum_last_multiplier}"
    )
    return int(bool(incomplete_classes or mismatches))


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
    predicted = tuple(sorted({projective_root_target(root, lattice)[1] for root in roots}))
    print(f"J={invariant}; Legendre elliptic j={legendre_elliptic_j(p, triple)}")
    print(f"basis={format_matrix(lattice.basis)}")
    print(f"Gram={format_matrix(lattice.gram)}")
    print(f"|Aut(L)|={len(automorphisms)}; reflective={len(automorphisms) > 2}")
    print(
        "short projective roots="
        + str([(root.scalar, root.vector, root.norm_multiplier) for root in roots])
    )
    print(f"root-predicted residues={predicted}")
    print(f"depth-{depth} finite-silent residues={observed}")
    status = 0
    residues = range(p) if show_all else sorted(set(observed) | set(predicted))
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
    if any(residue not in certified for residue in predicted):
        print("ERROR: a root-predicted residue has no affine certificate")
        status = 1
    if any(residue not in observed for residue in predicted):
        print("ERROR: a root-predicted residue has a finite nonzero witness")
        status = 1
    finite_extras = tuple(sorted(set(observed) - set(predicted)))
    if finite_extras:
        print(
            "NOTE: finite-depth silence without a root is not classified as vanishing; "
            f"unresolved residues={finite_extras}"
        )
    return status


def run_scan(max_prime: int, depth: int, confirmation_depth: int) -> int:
    total_classes = 0
    mismatch_count = 0
    root_mismatch_count = 0
    missing_certificate_count = 0
    missing_prediction_count = 0
    finite_extra_count = 0
    delayed_witness_count = 0
    unresolved_extra_count = 0
    print(
        "p  J-classes  reflective  short-root  nonreflective  predicted-hits "
        "aut/root-mis  hit-mis  root-cert-mis  finite-extra  delayed  unresolved"
    )
    for p in primes_through(max_prime):
        representatives = isotropic_j_representatives(p)
        if not representatives:
            continue
        reflective_count = 0
        hit_count = 0
        prime_mismatches = 0
        prime_root_mismatches = 0
        prime_missing_certificate = 0
        prime_missing_prediction = 0
        prime_finite_extra = 0
        prime_delayed = 0
        prime_unresolved = 0
        root_count = 0
        for triple in representatives.values():
            lattice = restricted_lattice(p, triple)
            automorphisms = lattice_automorphisms(lattice)
            reflective = len(automorphisms) > 2
            roots = short_projective_roots(p, triple)
            has_short_root = bool(roots)
            predicted = {projective_root_target(root, lattice)[1] for root in roots}
            observed, _ = vanishing_residues(p, triple, depth)
            observed_set = set(observed)
            missing_prediction = predicted - observed_set
            finite_extra = observed_set - predicted
            unresolved = set(finite_extra)
            if finite_extra and confirmation_depth > depth:
                confirmed, _ = vanishing_residues(p, triple, confirmation_depth)
                unresolved.intersection_update(confirmed)
            delayed = finite_extra - unresolved
            hit = bool(predicted)
            reflective_count += int(reflective)
            root_count += int(has_short_root)
            hit_count += int(hit)
            prime_mismatches += int(reflective != hit)
            prime_root_mismatches += int(reflective != has_short_root)
            prime_missing_prediction += len(missing_prediction)
            prime_finite_extra += len(finite_extra)
            prime_delayed += len(delayed)
            prime_unresolved += len(unresolved)
            if predicted and any(
                affine_branch_certificate(lattice, automorphisms, residue) is None
                for residue in predicted
            ):
                prime_missing_certificate += 1
        classes = len(representatives)
        total_classes += classes
        mismatch_count += prime_mismatches
        root_mismatch_count += prime_root_mismatches
        missing_certificate_count += prime_missing_certificate
        missing_prediction_count += prime_missing_prediction
        finite_extra_count += prime_finite_extra
        delayed_witness_count += prime_delayed
        unresolved_extra_count += prime_unresolved
        print(
            f"{p:<3}{classes:>11}{reflective_count:>12}{root_count:>12}"
            f"{classes-reflective_count:>15}{hit_count:>15}{prime_root_mismatches:>14}"
            f"{prime_mismatches:>9}{prime_missing_certificate:>15}"
            f"{prime_finite_extra:>14}{prime_delayed:>9}{prime_unresolved:>12}"
        )
    print(
        f"total J-classes={total_classes}; automorphism/short-root mismatches={root_mismatch_count}; "
        f"reflective/predicted-hit mismatches={mismatch_count}; "
        f"predicted residues missing from finite scan={missing_prediction_count}; "
        f"predicted residues lacking affine certificates={missing_certificate_count}; "
        f"finite-depth extra silent residues={finite_extra_count}; "
        f"delayed nonzero witnesses by depth {confirmation_depth}={delayed_witness_count}; "
        f"unresolved finite-depth extras={unresolved_extra_count}"
    )
    return int(bool(root_mismatch_count or mismatch_count or missing_prediction_count
                    or missing_certificate_count))


def run_root_transport_scan(max_prime: int, depth: int) -> int:
    """Verify the uniform projective-root residue and signed-reflection certificate."""
    checked = 0
    missing_certificate = 0
    missing_observed_zero = 0
    print("p  triple                 root             sign  residue  affine  observed-zero")
    for p in primes_through(max_prime):
        for triple in isotropic_j_representatives(p).values():
            roots = short_projective_roots(p, triple)
            if not roots:
                continue
            # The opposite root gives the same reflection and target residue.
            root = roots[0]
            lattice = restricted_lattice(p, triple)
            sign, residue, certificate = projective_root_branch_certificate(lattice, root)
            observed, _ = vanishing_residues(p, triple, depth)
            affine = certificate is not None
            observed_zero = residue in observed
            checked += 1
            missing_certificate += int(not affine)
            missing_observed_zero += int(not observed_zero)
            print(
                f"{p:<3}{str(triple):<23}{str(root.vector):<17}{sign:>5}"
                f"{residue:>9}{str(affine):>8}{str(observed_zero):>15}"
            )
    print(
        f"checked reflective classes={checked}; "
        f"missing exact root certificates={missing_certificate}; "
        f"predicted residues not observed zero={missing_observed_zero}"
    )
    return int(bool(missing_certificate or missing_observed_zero))


def run_converse_scan(max_prime: int) -> int:
    """Compare noncentral automorphisms, plane reflections, and short roots.

    This is an exact bounded census of the missing structural implication
    ``Aut(L) > {±I} => L has a reflection``.  It also checks equality between
    the full reflection set and the Householder maps supplied by short roots.
    """
    classes = 0
    reflective_classes = 0
    missing_reflection = 0
    reflection_root_mismatch = 0
    group_types: Counter[tuple[int, int, int]] = Counter()
    for p in primes_through(max_prime):
        for triple in isotropic_j_representatives(p).values():
            classes += 1
            lattice = restricted_lattice(p, triple)
            automorphisms = lattice_automorphisms(lattice)
            reflections = {
                matrix_key(matrix) for matrix in automorphisms if is_plane_reflection(matrix)
            }
            roots = short_projective_roots(p, triple)
            root_reflections = {
                matrix_key(signed_short_root_lattice_matrix(lattice, root, 1))
                for root in roots
            }
            group_types[(len(automorphisms), len(reflections), len(root_reflections))] += 1
            if len(automorphisms) > 2:
                reflective_classes += 1
                if not reflections:
                    missing_reflection += 1
                    print(f"NO REFLECTION: p={p} triple={triple} |Aut|={len(automorphisms)}")
            if reflections != root_reflections:
                reflection_root_mismatch += 1
                print(
                    f"REFLECTION/ROOT MISMATCH: p={p} triple={triple} "
                    f"reflections={len(reflections)} root-reflections={len(root_reflections)}"
                )
    print("(|Aut|, plane reflections, distinct root reflections) -> class count")
    for group_type, count in sorted(group_types.items()):
        print(f"  {group_type} -> {count}")
    print(
        f"classes={classes}; noncentral classes={reflective_classes}; "
        f"noncentral classes without a reflection={missing_reflection}; "
        f"reflection/root-set mismatches={reflection_root_mismatch}"
    )
    return int(bool(missing_reflection or reflection_root_mismatch))


def run_witness_dichotomy_scan(max_prime: int, depth: int, min_prime: int = 5) -> int:
    """Check the root-or-finite-coefficient certificate dichotomy exactly.

    For every projective isotropic class and every residue, a short root
    targeting that residue is the first certificate alternative.  Otherwise
    the command searches the actual triple-product coefficients through
    ``q^(p*depth+p-1)`` for one explicit nonzero witness.
    """
    classes = 0
    residues = 0
    root_certificates = 0
    coefficient_witnesses = 0
    unresolved: list[tuple[int, tuple[int, int, int], int]] = []
    root_conflicts: list[tuple[int, tuple[int, int, int], int, tuple[int, int]]] = []
    latest_witness: tuple[int, tuple[int, tuple[int, int, int], int, int, int]] | None = None
    latest_reflective_witness: tuple[
        int, tuple[int, tuple[int, int, int], int, int, int]
    ] | None = None
    latest_nonreflective_witness: tuple[
        int, tuple[int, tuple[int, int, int], int, int, int]
    ] | None = None
    largest_relative_witness: tuple[
        Fraction, tuple[int, tuple[int, int, int], int, int, int]
    ] | None = None
    quarter_bound_violations: list[
        tuple[int, tuple[int, int, int], int, int, int, int]
    ] = []
    for p in primes_through(max_prime):
        if p < min_prime:
            continue
        limit = p * depth + p - 1
        for triple in isotropic_j_representatives(p).values():
            classes += 1
            roots = short_projective_roots(p, triple)
            predicted: set[int] = set()
            if roots:
                lattice = restricted_lattice(p, triple)
                predicted = {projective_root_target(root, lattice)[1] for root in roots}
            coefficients = product_coefficients(p, triple, limit)
            first: dict[int, tuple[int, int]] = {}
            for exponent in sorted(coefficients):
                first.setdefault(exponent % p, (exponent, coefficients[exponent]))
            for residue in range(p):
                residues += 1
                witness = first.get(residue)
                if residue in predicted:
                    root_certificates += 1
                    if witness is not None:
                        root_conflicts.append((p, triple, residue, witness))
                    continue
                if witness is None:
                    unresolved.append((p, triple, residue))
                    continue
                coefficient_witnesses += 1
                exponent, coefficient = witness
                progression_index = exponent // p
                record = (progression_index, (p, triple, residue, exponent, coefficient))
                if latest_witness is None or record > latest_witness:
                    latest_witness = record
                if roots:
                    if latest_reflective_witness is None or record > latest_reflective_witness:
                        latest_reflective_witness = record
                elif latest_nonreflective_witness is None or record > latest_nonreflective_witness:
                    latest_nonreflective_witness = record
                relative_record = (
                    Fraction(progression_index, p),
                    (p, triple, residue, exponent, coefficient),
                )
                if largest_relative_witness is None or relative_record > largest_relative_witness:
                    largest_relative_witness = relative_record
                if 4 * progression_index > p:
                    quarter_bound_violations.append(
                        (p, triple, residue, progression_index, exponent, coefficient)
                    )
    print(
        f"classes={classes}; residues={residues}; root certificates={root_certificates}; "
        f"coefficient witnesses={coefficient_witnesses}; depth={depth}"
    )
    print(f"latest first coefficient witness={latest_witness}")
    print(f"latest reflective-class witness={latest_reflective_witness}")
    print(f"latest nonreflective-class witness={latest_nonreflective_witness}")
    print(f"largest relative witness N/p={largest_relative_witness}")
    print(f"N <= p/4 violations={len(quarter_bound_violations)}")
    print(
        f"unresolved residues={len(unresolved)}; "
        f"root/nonzero conflicts={len(root_conflicts)}"
    )
    for p, triple, residue in unresolved[:20]:
        print(f"UNRESOLVED: p={p} triple={triple} residue={residue}")
    for p, triple, residue, witness in root_conflicts[:20]:
        print(
            f"ROOT CONFLICT: p={p} triple={triple} residue={residue} "
            f"witness={witness}"
        )
    for (
        p, triple, residue, progression_index, exponent, coefficient
    ) in quarter_bound_violations[:20]:
        print(
            f"QUARTER-BOUND VIOLATION: p={p} triple={triple} residue={residue} "
            f"N={progression_index} exponent={exponent} coefficient={coefficient}"
        )
    return int(bool(unresolved or root_conflicts))


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
    scan.add_argument(
        "--confirmation-depth", type=int, default=256,
        help="recheck finite-silent residues not predicted by roots at this deeper cutoff",
    )
    root_scan = subparsers.add_parser(
        "root-scan", help="verify the uniform projective-root residue transport"
    )
    root_scan.add_argument("--max-prime", type=int, default=127)
    root_scan.add_argument("--depth", type=int, default=120)
    converse_scan = subparsers.add_parser(
        "converse-scan", help="compare noncentral automorphisms, reflections, and roots"
    )
    converse_scan.add_argument("--max-prime", type=int, default=401)
    witness_scan = subparsers.add_parser(
        "witness-scan", help="check the root-or-finite-coefficient certificate dichotomy"
    )
    witness_scan.add_argument("--max-prime", type=int, default=1000)
    witness_scan.add_argument("--min-prime", type=int, default=5)
    witness_scan.add_argument("--depth", type=int, default=256)
    dual_shell_scan = subparsers.add_parser(
        "dual-shell-scan",
        help="compare short-root targets with exact Poisson-dual shell cancellation",
    )
    dual_shell_scan.add_argument("--max-prime", type=int, default=300)
    dual_shell_scan.add_argument("--min-prime", type=int, default=5)
    dual_shell_scan.add_argument("--shells", type=int, default=4)
    dual_shell_scan.add_argument("--shift-radius", type=int, default=1)
    dual_candidate = subparsers.add_parser(
        "dual-candidate", help="print one exact Poisson-dual shell certificate"
    )
    dual_candidate.add_argument("--prime", type=int, required=True)
    dual_candidate.add_argument("--indices", type=parse_indices, required=True)
    dual_candidate.add_argument("--residue", type=int, required=True)
    dual_candidate.add_argument("--shells", type=int, default=4)
    dual_candidate.add_argument("--shift-radius", type=int, default=1)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if args.command == "candidate":
        return run_candidate(args.prime, args.indices, args.depth, args.all_residues)
    if args.command == "scan":
        return run_scan(args.max_prime, args.depth, args.confirmation_depth)
    if args.command == "root-scan":
        return run_root_transport_scan(args.max_prime, args.depth)
    if args.command == "converse-scan":
        return run_converse_scan(args.max_prime)
    if args.command == "witness-scan":
        return run_witness_dichotomy_scan(args.max_prime, args.depth, args.min_prime)
    if args.command == "dual-shell-scan":
        return run_dual_shell_rigidity_scan(
            args.max_prime, args.shells, args.shift_radius, args.min_prime
        )
    if args.command == "dual-candidate":
        return run_dual_shell_candidate(
            args.prime,
            args.indices,
            args.residue,
            args.shells,
            args.shift_radius,
        )
    raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
