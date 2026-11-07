#!/usr/bin/env python3
"""Check the saved 607 rank witness using only Python's standard library.

This checks finite integer arithmetic, not identification with partition series.
It deliberately does not import the generator, FLINT, SymPy, or zmod.py.
"""
import argparse
import hashlib
import json
from pathlib import Path


def determinant(matrix):
    """Exact fraction-free Bareiss elimination, with row pivoting."""
    a = [r[:] for r in matrix]
    n, previous, sign = len(a), 1, 1
    for k in range(n - 1):
        at = next((i for i in range(k, n) if a[i][k]), None)
        if at is None:
            return 0
        if at != k:
            a[k], a[at] = a[at], a[k]
            sign *= -1
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def check(path):
    data = json.loads(path.read_text())
    assert data['prime'] == 607 and data['precision'] == 2
    p = data['prime']
    cols, rows = data['initial_q_coefficients'], data['witness_rows']
    matrix = data['witness_matrix']
    assert rows == list(range(26, 51))
    assert matrix == [[cols[j][i] for j in range(25)] for i in rows]
    assert data['initial_q_sha256'] == hashlib.sha256(json.dumps(cols).encode()).hexdigest()
    minor = [row[:24] for row in matrix[:24]]
    d24, d25 = determinant(minor), determinant(matrix)
    assert d24 % p == data['unit_minor_det_mod_p'] == 112
    assert d25 % p == 0 and (d25 // p) % p == data['determinant_div_p_mod_p'] == 504
    c = data['lifting_relation']
    residual = [(row[-1] - sum(x * y for x, y in zip(row[:-1], c))) % (p * p)
                for row in matrix]
    assert residual == [0] * 24 + [p * 308]
    assert data['residual_div_p_mod_p'] == 308
    assert (112 * 308) % p == 504
    # The invertible 24-by-24 block and its Schur complement p*308 give
    # (Z/p^2)^24 + Z/p, hence 25 generators and 24 full-size factors.
    print(f'{path}: verified det24 mod p = 112; det25/p mod p = 504; Schur/p = 308')
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args()
    data = [check(path) for path in args.files]
    if len(data) > 1:
        for other in data[1:]:
            for key in ('initial_q_coefficients', 'lifting_relation', 'witness_matrix'):
                assert other[key] == data[0][key], key
        print('All supplied cutoffs agree on the saved q-coefficients and rank witness.')


if __name__ == '__main__':
    main()
