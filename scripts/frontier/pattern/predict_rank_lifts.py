#!/usr/bin/env python3
"""Test the first divided-relation criterion against exact Smith forms.

The predictor uses only modular Gaussian elimination. FLINT's integer Smith
form is an independent comparison, not an input to the prediction. These
computations are outside Lean's kernel.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

from flint import fmpz_mat


def rank_mod(matrix, p):
    a = [[x % p for x in row] for row in matrix]
    if not a:
        return 0
    rank = 0
    for j in range(len(a[0])):
        k = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if k is None:
            continue
        a[rank], a[k] = a[k], a[rank]
        u = pow(a[rank][j], -1, p)
        a[rank] = [(x * u) % p for x in a[rank]]
        for i in range(rank + 1, len(a)):
            q = a[i][j]
            a[i] = [(x - q * y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def predict_two(matrix, p):
    """Return (rank mod p, new generators at p^2) via the divided Schur block."""
    mod = p * p
    a = [[x % mod for x in row] for row in matrix]
    if not a or not a[0]:
        return 0, 0
    nr, nc, r = len(a), len(a[0]), 0
    while r < min(nr, nc):
        pivot = next(((i, j) for i in range(r, nr) for j in range(r, nc)
                      if a[i][j] % p), None)
        if pivot is None:
            break
        i, j = pivot
        a[r], a[i] = a[i], a[r]
        for row in a:
            row[r], row[j] = row[j], row[r]
        u = pow(a[r][r], -1, mod)
        a[r] = [(x * u) % mod for x in a[r]]
        for i in range(nr):
            if i != r:
                q = a[i][r]
                a[i] = [(x - q * y) % mod for x, y in zip(a[i], a[r])]
        for j in range(r + 1, nc):
            q = a[r][j]
            for i in range(nr):
                a[i][j] = (a[i][j] - q * a[i][r]) % mod
        r += 1
    tail = [row[r:] for row in a[r:]]
    assert all(x % p == 0 for row in tail for x in row)
    obstruction = [[x // p for x in row] for row in tail]
    return r, rank_mod(obstruction, p)


def smith_exponents(matrix, p):
    s = fmpz_mat(matrix).snf()
    out = []
    for i in range(min(s.nrows(), s.ncols())):
        x, e = abs(int(s[i, i])), 0
        if x == 0:
            out.append(None)
            continue
        while x % p == 0:
            x //= p
            e += 1
        out.append(e)
    return out


def krylov(t, y):
    cols, v = [], y[:]
    for _ in y:
        cols.append(v)
        v = [sum(x * z for x, z in zip(row, v)) for row in t]
    return [list(row) for row in zip(*cols)]


def run(output):
    rng = random.Random(607)
    checks = 0
    for p in (2, 3, 5, 7, 13):
        for nr, nc in ((2, 2), (3, 4), (4, 3), (5, 5)):
            for _ in range(20):
                a = [[rng.randrange(-p * p, p * p) for _ in range(nc)] for _ in range(nr)]
                # Include matrices with forced hidden layers and exact zeros.
                for i in range(nr):
                    a[i] = [x * p ** rng.randrange(3) for x in a[i]]
                r, jump = predict_two(a, p)
                e = smith_exponents(a, p)
                assert r == e.count(0) and jump == e.count(1)
                checks += 1
    cases = []
    p = 5
    for depth in (1, 2, 3):
        cases.append((f'two-mode gap depth {depth}', [[1, 0], [0, 1 + p ** depth]], [1, 1], [0, depth]))
    cases += [
        ('permanent scalar collision', [[1, 0], [0, 1]], [1, 1], [0, None]),
        ('seed misses second mode', [[1, 0], [0, 6]], [1, 0], [0, None]),
        ('Jordan collision already cyclic', [[1, 1], [0, 1]], [0, 1], [0, 0]),
        ('nonsplit first correction', [[1, 10], [5, 1]], [1, 0], [0, 1]),
        ('three-mode collision', [[1, 0, 0], [0, 6, 0], [0, 0, 31]], [1, 1, 1], [0, 1, 3]),
    ]
    examples = []
    for name, t, y, expected in cases:
        a = krylov(t, y)
        e = smith_exponents(a, p)
        assert e == expected
        r, jump = predict_two(a, p)
        assert (r, jump) == (e.count(0), e.count(1))
        examples.append(dict(name=name, prime=p, operator=t, seed=y,
                             smith_exponents=e, predicted_first_jump=jump,
                             generator_counts=[sum(v is not None and v < m for v in e)
                                               for m in range(1, 6)]))
    root = Path(__file__).resolve().parents[3]
    witness_path = root / 'docs/verification/rank607-uniform-n2.json'
    witness = json.loads(witness_path.read_text())
    r, jump = predict_two(witness['witness_matrix'], 607)
    assert (r, jump) == (24, 1)
    # Correcting the last column to the old span removes the obstruction.
    control = [row[:] for row in witness['witness_matrix']]
    c = witness['lifting_relation']
    for row in control:
        row[-1] = sum(x * y for x, y in zip(row[:-1], c)) % (607 * 607)
    assert predict_two(control, 607) == (24, 0)
    # Apply the same predictor to actual reconstructed partition orbits.
    # The reconstruction generator and the Smith comparison are not formal
    # arithmetic certificates; the independent 607 replay is recorded separately.
    from rank_lift_check import UniformBasis
    partitions = []
    for p in (13, 29, 31, 47, 71, 113, 197, 607, 859):
        space = UniformBasis(p, 2, 4)
        bound = (p + 12) // 24
        series, cols = space.P([1]), []
        for b in range(1, 2 * (bound + 2) + 2):
            series, prefix = space.step(series, b % 2 == 1)
            if b >= 3 and b % 2:
                cols.append(prefix)
        matrix = [list(row) for row in zip(*cols)]
        rank, new = predict_two(matrix, p)
        e = smith_exponents(matrix, p)
        assert rank == e.count(0) and new == e.count(1)
        assert rank + new <= bound
        partitions.append(dict(prime=p, bound=bound, rank_mod_p=rank,
                               divided_relation_rank=new,
                               predicted_rank_mod_p_squared=rank + new,
                               smith_comparison_passed=True))
        print(f'p={p}: first rank {rank}, predicted new generators {new}', flush=True)
    record = dict(random_matrix_checks=checks, examples=examples,
                  partition_cases=partitions,
                  rank607=dict(mod_p_rank=r, divided_relation_rank=jump,
                               predicted_mod_p_squared_generators=r + jump,
                               zero_obstruction_control_passed=True),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  witness_sha256=hashlib.sha256(witness_path.read_bytes()).hexdigest(),
                  lean_kernel_numeric_verification=False)
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args().output)
