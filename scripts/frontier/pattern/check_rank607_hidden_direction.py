#!/usr/bin/env python3
"""Check the recovered 607 direction in saved reconstruction coordinates.

This is external exact arithmetic, not a Lean kernel certificate. It checks
that the divided relation adds one direction and that X acts by 240 on its
quotient by the original 24-dimensional orbit.
"""
import argparse
import hashlib
import json
from pathlib import Path


def check(replay_path, witness_path, output):
    p = 607
    replay = json.loads(replay_path.read_text())
    witness = json.loads(witness_path.read_text())
    assert replay['prime'] == witness['prime'] == p
    assert replay['dimension'] == 102 and replay['modulus'] == p * p
    assert replay['initial_q_sha256'] == witness['initial_q_sha256']
    coords = replay['iterate_coordinates']
    assert len(coords) == 55 and all(len(row) == 102 for row in coords)
    assert all(0 <= t < p * p for row in coords for t in row)
    v = [coords[b - 1] for b in range(3, 56, 2)]
    c = witness['lifting_relation']
    assert len(c) == 24
    residuals = [[(v[24 + shift][i] - sum(c[j] * v[j + shift][i] for j in range(24)))
                  % (p * p) for i in range(102)] for shift in range(2)]
    assert all(t % p == 0 for row in residuals for t in row)
    w, xw = [[t // p for t in row] for row in residuals]
    cols = [[t % p for t in row] for row in v[:24]] + [w]
    a = [[cols[j][i] for j in range(25)] + [xw[i]] for i in range(102)]
    # A pivot in every column proves rank 25 over F_607.
    for j in range(25):
        k = next(i for i in range(j, 102) if a[i][j])
        a[j], a[k] = a[k], a[j]
        factor = pow(a[j][j], -1, p)
        a[j] = [(t * factor) % p for t in a[j]]
        for i in range(102):
            if i != j:
                factor = a[i][j]
                a[i] = [(x - factor * y) % p for x, y in zip(a[i], a[j])]
    assert all(row[-1] == 0 for row in a[25:])
    sol = [row[-1] for row in a[:25]]
    # Verify the original system as well as the elimination result.
    assert all((sum(sol[j] * cols[j][i] for j in range(25)) - xw[i]) % p == 0
               for i in range(102))
    assert sol[-1] == 240
    record = dict(prime=p, recovered_rank=25, quotient_eigenvalue=240,
                  divided_relation=w, shifted_divided_relation=xw,
                  action_coefficients=sol,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  replay_sha256=hashlib.sha256(replay_path.read_bytes()).hexdigest(),
                  witness_sha256=hashlib.sha256(witness_path.read_bytes()).hexdigest(),
                  lean_kernel_numeric_verification=False)
    output.write_text(json.dumps(record, indent=2) + '\n')
    print('Verified: divided relation increases rank to 25; quotient X-eigenvalue is 240 modulo 607.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('replay', type=Path)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.replay, args.witness, args.output)
