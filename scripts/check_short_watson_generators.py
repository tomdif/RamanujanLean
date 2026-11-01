#!/usr/bin/env python3
"""Check the finite arithmetic in the proposed full converse paper proof.

Standard-library-only verification, independent of the certificate generator,
LLL implementation, root scanner, and Watson-series coefficient implementation.
This does not certify the analytic or geometric arguments, or replace Lean.
"""
import argparse
import hashlib
from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path


def det(rows):
    return sum((-1 if (j - i) % 3 == 2 else 1) * rows[0][i] * rows[1][j] * rows[2][3 - i - j]
               for i in range(3) for j in range(3) if i != j)


def norm(w):
    return sum(x * x for x in w)


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def minors_gcd(vectors):
    value = 0
    for rows in combinations(vectors, 3):
        value = gcd(value, det(rows))
        if value == 1:
            break
    return value


def product_coefficients(p, v, limit):
    result = [1] + [0] * limit
    for i in v:
        for start, step in ((i, p), (p-i, p), (p, p), (p+2*i, 2*p), (p-2*i, 2*p)):
            assert start > 0
            for exponent in range(start, limit + 1, step):
                for n in range(limit, exponent - 1, -1):
                    result[n] -= result[n-exponent]
    return result


def check_finite_field_geometry():
    count = 0
    for a, b, c, d, e, f in product(range(3), repeat=6):
        gram = ((a, d, e), (d, b, f), (e, f, c))
        if det(gram) % 3 == 0:
            continue
        vectors = []
        for x, y, z in product(range(-2, 3), range(-2, 3), (0, 1)):
            q = a*x*x + b*y*y + c*z*z + 2*d*x*y + 2*e*x*z + 2*f*y*z
            if q % 3 == 0 and any(t % 3 for t in (x, y, z)):
                vectors.append((x, y, z))
        assert minors_gcd(vectors) == 1, gram
        count += 1
    orthogonal = 0
    for entries in product(range(3), repeat=9):
        matrix = tuple(entries[3*i:3*i+3] for i in range(3))
        if not all(sum(matrix[k][i]*matrix[k][j] for k in range(3)) % 3 == int(i == j)
                   for i in range(3) for j in range(3)):
            continue
        assert all(sum(x != 0 for x in row) == 1 for row in matrix)
        orthogonal += 1
    assert orthogonal == 48
    return count, orthogonal


def check(path):
    # Rational endpoint inequalities in the universal p >= 1250 argument.
    assert 27 * 1250**2 > 64 * 80**3
    assert 1250 >= 1200 and 1250 > 633 and 2 * 427 < 960
    data = json.loads(path.read_text())
    assert data['prime_upper_bound_exclusive'] == 1250
    expected = set()
    primes = 0
    for p in range(5, 1250):
        if not is_prime(p):
            continue
        primes += 1
        roots = {k*k % p: k for k in range(1, (p+1)//2)}
        for j in range(2, (p+1)//2):
            k = roots.get((-1-j*j) % p, 0)
            if j < k:
                expected.add((p, (1, j, k)))
    actual = set()
    max_vectors = 0
    for p, v, vectors in data['short_generator_certificates']:
        key = (p, tuple(v))
        assert key in expected and key not in actual
        actual.add(key)
        max_vectors = max(max_vectors, len(vectors))
        assert all(all(x % 3 for x in w) and 2 * norm(w) < p*p
                   and all((w[i] - w[0]*v[i]) % p == 0 for i in range(3))
                   for w in vectors), key
        assert minors_gcd(vectors) == p*p, key
    exceptions = {(p, tuple(v)) for p, v in data['short_generator_exceptions']}
    assert exceptions == {(13, (1, 3, 4))}
    assert actual.isdisjoint(exceptions) and actual | exceptions == expected
    expected13 = {v for v in combinations(range(1, 7), 3) if norm(v) % 13 == 0}
    actual13 = set()
    nonzero = root_count = 0
    for case in data['p13_cases']:
        v = tuple(case['v'])
        assert v in expected13 and v not in actual13
        actual13.add(v)
        root_residues = set()
        for root in case['roots']:
            w, lam, e, r = root['w'], root['lambda'], root['e'], root['R']
            assert e in (1, 2) and norm(w) == e*13 and lam % 13 != 0
            assert all((x-lam*y) % 13 == 0 for x, y in zip(w, v))
            pairing = sum(x*y for x, y in zip(w, v))
            assert pairing % 13 == 0
            base = 2*lam*r-sum(w)+6*(pairing//13)
            assert (base % 13 == 0 if e*13 % 3 == 1
                    else ((2//e)*lam*base-12) % 13 == 0)
            root_residues.add(r)
            root_count += 1
        coefficients = product_coefficients(13, v, 40)
        witness_residues = set()
        for r, n, value in case['nonzero_coefficients']:
            assert 0 <= r < 13 and n >= 0 and value != 0
            assert 13*n+r <= 40 and coefficients[13*n+r] == value
            assert r not in witness_residues
            witness_residues.add(r)
            nonzero += 1
        assert not root_residues & witness_residues
        assert root_residues | witness_residues == set(range(13))
    assert actual13 == expected13
    quadratic_forms, orthogonal_matrices = check_finite_field_geometry()
    return {'passed': True, 'primes_below_1250': primes,
            'normalized_lines': len(expected), 'generator_certificates': len(actual),
            'exceptional_normalized_lines': len(exceptions),
            'maximum_vectors_per_certificate': max_vectors,
            'p13_canonical_triples': len(actual13), 'p13_root_certificates': root_count,
            'p13_nonzero_coefficients': nonzero,
            'nondegenerate_ternary_forms_mod_3': quadratic_forms,
            'orthogonal_matrices_mod_3': orthogonal_matrices,
            'universal_bound_endpoint_inequalities_checked': True,
            'certificate_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'lean_checked': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.certificate)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
