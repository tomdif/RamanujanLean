#!/usr/bin/env python3
"""Independently replay the finite parts of the prime-family converse argument.

Uses exact standard-library arithmetic, including direct Pochhammer products
for the small-prime witnesses. Analytic necessity and its Lean assembly are
separate obligations; this checker does not certify them.
"""
import argparse
from copy import deepcopy
import hashlib
from itertools import permutations, product
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def point(m, n, a, b, c, d):
    p = m*m+n*n
    x, y = m*a-n*b, n*a+m*b
    z = (x-y+p*c, y+p*c-p*d, x-p*c-p*d, x+y+p*d)
    assert all(t % 3 == 0 for t in z)
    return tuple(t//3 for t in z)


def character(w):
    out = 1
    for x in w:
        out *= x % 3
    return out % 3


def act(matrix, v):
    return tuple(sum(x*y for x, y in zip(row, v)) for row in matrix)


def signed_permutations():
    return [tuple(tuple(signs[i] if j == perm[i] else 0 for j in range(2)) for i in range(2))
            for perm in permutations(range(2)) for signs in product((-1, 1), repeat=2)]


def direct_product(p, indices, limit):
    out = [1]+[0]*limit
    for i in indices:
        for start, step in ((i, p), (p-i, p), (p, p), (p+2*i, 2*p), (p-2*i, 2*p)):
            for exponent in range(start, limit+1, step):
                for degree in range(limit, exponent-1, -1):
                    out[degree] -= out[degree-exponent]
    return out


def check(record):
    expected = {(m, n) for m, n in product(range(9), repeat=2) if (m*m+n*n) % 3}
    classes = record['residue_classes']
    assert len(classes) == len(expected) == 72
    assert {(c['m'], c['n']) for c in classes} == expected
    assert record['long_norm_bound'] == 50 and record['large_prime_threshold'] == 100
    identity = ((1, 0), (0, 1))
    minus_identity = ((-1, 0), (0, -1))
    matrices = signed_permutations()
    involutions = [a for a in matrices if all(act(a, act(a, e)) == e for e in identity)]
    assert len(matrices) == 8 and len(involutions) == 6
    compatible = 0
    max_points = 0
    for case in classes:
        m, n = case['m'], case['n']
        bases, points, coordinates = case['bases'], case['points'], case['coordinates']
        assert bases == [[(m-n+1) % 3-1, (-m-n+1) % 3-1],
                         [(m+n+1) % 3-1, (m-n+1) % 3-1]]
        assert len(points) == len(coordinates)
        max_points = max(max_points, len(points))
        for (a, b, c, d), coordinate in zip(points, coordinates):
            assert (c, d) in ((1, 0), (0, 1)) and a*a+b*b <= 50
            w = point(m, n, a, b, c, d)
            assert character(w) != 0
            p = m*m+n*n
            assert 3*sum(t*t for t in w) == p*(a*a+b*b+p*(c*c+d*d))
            aa, bb = bases[0 if c else 1]
            assert (a-aa) % 3 == (b-bb) % 3 == 0
            assert coordinate == [(a-aa)//3, (b-bb)//3, c, d]
        inverse = case['spanning_coefficients']
        assert len(inverse) == 4 and all(len(row) == len(points) for row in inverse)
        assert all(sum(inverse[i][k]*coordinates[k][j] for k in range(len(points))) == int(i == j)
                   for i in range(4) for j in range(4))
        good = []
        for a, b in product(involutions, repeat=2):
            valid = True
            for x, y, c, d in points:
                try:
                    image = point(m, n, *act(a, (x, y)), *act(b, (c, d)))
                except AssertionError:
                    valid = False
                    break
                if character(image) != -character(point(m, n, x, y, c, d)) % 3:
                    valid = False
                    break
            if valid:
                good.append((a, b))
        predicted = any(x % 9 == 0 for x in (m, n, m-n, m+n))
        assert len(good) == (4 if predicted else 0), (m, n, good)
        assert all(a not in (identity, minus_identity) for a, b in good)
        assert len({a for a, b in good}) == len(good)
        compatible += len(good)
    expected_small = {(m, n) for m in range(2, 11) for n in range(1, m)
                      if 5 <= m*m+n*n <= 100 and 2*(m+n) < m*m+n*n
                      and all((m*m+n*n) % d for d in range(2, isqrt(m*m+n*n)+1))}
    assert len(record['small_prime_cases']) == len(expected_small) == 10
    assert {(c['m'], c['n']) for c in record['small_prime_cases']} == expected_small
    witnesses, coefficients_checked = 0, 0
    for case in record['small_prime_cases']:
        m, n, p = case['m'], case['n'], case['p']
        assert p == m*m+n*n
        zs = sorted(((3*m+n-18)*pow(2, -1, p) % p, (3*m+n)*pow(2, -1, p) % p,
                     n*(m+2*n-9)*pow(n-m, -1, p) % p, n*(2*m-n-9)*pow(m+n, -1, p) % p)) \
            if any(x % 9 == 0 for x in (m, n, m-n, m+n)) else []
        assert case['zero_residues'] == zs
        ws = case['witnesses']
        assert len(ws) == p-len(zs) and {w['R'] for w in ws} == set(range(p))-set(zs)
        limit = max(p*w['N']+w['R'] for w in ws)
        direct = direct_product(p, (m-n, n, m, m+n), limit)
        for w in ws:
            assert w['N'] >= 0 and direct[p*w['N']+w['R']] == w['coefficient'] != 0
        witnesses += len(ws)
        coefficients_checked += len(direct)
    return dict(passed=True, residue_classes=72, symmetry_pairs_checked=72*36,
                compatible_pairs=compatible, maximum_generators=max_points,
                small_prime_cases=10, nonzero_witnesses=witnesses,
                direct_coefficients_checked=coefficients_checked,
                scope="Finite certificate replay only; not the analytic or full Lean converse")


def rejection_checks(record):
    """Reject corrupted coverage, integer spans, norm bounds, and coefficients."""
    mutations = []
    bad = deepcopy(record)
    bad['residue_classes'].pop()
    mutations.append(('missing residue class', bad))
    bad = deepcopy(record)
    bad['residue_classes'][0]['spanning_coefficients'][0][0] += 1
    mutations.append(('corrupted integer inverse', bad))
    bad = deepcopy(record)
    bad['residue_classes'][0]['points'][0][0] = 100
    mutations.append(('invalid short generator', bad))
    bad = deepcopy(record)
    bad['small_prime_cases'][0]['witnesses'].pop()
    mutations.append(('missing nonzero witness', bad))
    bad = deepcopy(record)
    bad['small_prime_cases'][0]['witnesses'][0]['coefficient'] += 1
    mutations.append(('incorrect coefficient', bad))
    for name, bad in mutations:
        try:
            check(bad)
        except AssertionError:
            continue
        raise AssertionError(f'Checker accepted {name}')
    return len(mutations)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=ROOT/'docs/verification/four_prime_converse_certificates.json')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--self-test', action='store_true', help='also reject five corrupted certificates')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Run this checker without Python optimization (-O).')
    record = json.loads(args.certificate.read_text())
    result = check(record)
    if args.self_test:
        result['corrupted_certificates_rejected'] = rejection_checks(record)
    result['certificate_sha256'] = hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
