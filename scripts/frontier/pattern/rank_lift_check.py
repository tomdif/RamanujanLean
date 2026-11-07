#!/usr/bin/env python3
"""Independent finite experiment for the rank lift at 607 (not a Lean proof).

Uses a single weight N*(p-1) basis Delta^t E4^a E6^b / E_(p-1)^N,
instead of katzmat.py's successive Katz complements. Every reconstructed
iterate is checked on extra q-coefficients not used to solve for coordinates.
An integer Smith form and a determinant independently check the rank witness.

Run from any directory:
  python3 rank_lift_check.py --prime 607 --cutoff 3 --output /tmp/rank607-n3.json
  python3 rank_lift_check.py --prime 607 --cutoff 4 --output /tmp/rank607-n4.json

Only precision two is used. Stability under increasing N and holdout checks
are evidence, not a proof of the comparison with infinite partition series.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

from flint import fmpz_mat, nmod_mat, nmod_poly
import sympy


def valuation(x, p, cap=2):
    if x == 0:
        return cap
    v = 0
    while v < cap and x % p == 0:
        x //= p
        v += 1
    return v


def pivot_rows(columns, p):
    """Rows giving an invertible minor, using plain modular elimination."""
    a = [list(r) for r in zip(*columns)]
    ids = list(range(len(a)))
    rank = 0
    for c in range(len(columns)):
        at = next((r for r in range(rank, len(a)) if a[r][c] % p), None)
        if at is None:
            continue
        a[rank], a[at] = a[at], a[rank]
        ids[rank], ids[at] = ids[at], ids[rank]
        inv = pow(a[rank][c] % p, -1, p)
        a[rank] = [x * inv % p for x in a[rank]]
        for r in range(rank + 1, len(a)):
            mul = a[r][c] % p
            a[r] = [(x - mul * y) % p for x, y in zip(a[r], a[rank])]
        rank += 1
    return ids[:rank]


class UniformBasis:
    def __init__(self, p, cutoff, holdout):
        self.p, self.mod = p, p * p
        self.weight = cutoff * (p - 1)
        self.dim = self.weight // 12 + (self.weight % 12 != 2)
        self.short = self.dim + holdout
        self.length = p * (self.short - 1) + 1
        self.holdout_checks = 0
        self.P = lambda xs: nmod_poly(xs, self.mod)

        def eisenstein(k):
            b = sympy.bernoulli(k)
            c = Fraction(-2 * k) / Fraction(int(b.p), int(b.q))
            scale = c.numerator * pow(c.denominator, -1, self.mod) % self.mod
            coeff = [0] * self.length
            coeff[0] = 1
            for d in range(1, self.length):
                x = scale * pow(d, k - 1, self.mod) % self.mod
                for i in range(d, self.length, d):
                    coeff[i] += x
            return self.P([x % self.mod for x in coeff])

        e4, e6, e = eisenstein(4), eisenstein(6), eisenstein(p - 1)
        eta_coeff = [0] * self.length
        eta_coeff[0] = 1
        for n in range(1, self.length):
            low = n * (3 * n - 1) // 2
            if low >= self.length:
                break
            eta_coeff[low] = (-1) ** n % self.mod
            high = low + n
            if high < self.length:
                eta_coeff[high] = (-1) ** n % self.mod
        eta = self.P(eta_coeff)
        delta = self.mul(self.P([0, 1]), self.power(eta, 24))
        inv_e = self.inverse(e)
        ratio = self.mul(delta, self.power(self.inverse(e4), 3))
        self.basis = []
        for t in range(self.dim):
            remaining = self.weight - 12 * t
            b = (remaining // 2) % 2
            a = (remaining - 6 * b) // 4
            if t == 0:
                cur = self.mul(self.power(e4, a), self.power(e6, b))
                cur = self.mul(cur, self.power(inv_e, cutoff))
            else:
                cur = self.mul(cur, ratio)
            assert int(cur[t]) == 1
            self.basis.append(cur)
        self.low = [[int(f[i]) for i in range(self.short)] for f in self.basis]
        eta_p2 = [0] * self.length
        for n in range(0, self.length, p * p):
            eta_p2[n] = eta_coeff[n // (p * p)]
        phi = self.mul(self.P(eta_p2), self.inverse(eta))
        self.phi = self.mul(self.P([0] * ((p * p - 1) // 24) + [1]), phi)

    def mul(self, a, b):
        return self.P((a * b).coeffs()[:self.length])

    def inverse(self, f):
        out = self.P([pow(int(f[0]), -1, self.mod)])
        length = 1
        while length < self.length:
            length = min(2 * length, self.length)
            out = self.P((out * (self.P([2]) - f * out)).coeffs()[:length])
        return out

    def power(self, a, n):
        out = self.P([1])
        while n:
            if n & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            n //= 2
        return out

    def step(self, f, odd):
        if odd:
            f = self.mul(f, self.phi)
        values = [int(f[self.p * i]) for i in range(self.short)]
        rem = values[:]
        coords = []
        for t in range(self.dim):
            c = rem[t] % self.mod
            coords.append(c)
            if c:
                for i in range(t, self.short):
                    rem[i] = (rem[i] - c * self.low[t][i]) % self.mod
        assert not any(rem), ("holdout reconstruction failed", rem)
        self.holdout_checks += self.short - self.dim
        out = self.P([])
        for c, base in zip(coords, self.basis):
            if c:
                out += base * c
        return out, values[:self.dim]


def analyze(p, cutoff, holdout=16):
    assert p == 607, "This experiment's expected Smith profile is specific to prime 607"
    assert sympy.isprime(p) and cutoff >= 2 and holdout > 0
    start = time.time()
    space = UniformBasis(p, cutoff, holdout)
    bound = (p + 12) // 24
    print(f"uniform basis ready: p={p}, N={cutoff}, dimension={space.dim}", flush=True)
    f = space.P([1])
    cols = []
    for b in range(1, 2 * (bound + 2) + 2):
        f, coeffs = space.step(f, b % 2 == 1)
        if b >= 3 and b % 2:
            cols.append(coeffs)
    # Independent integer Smith form; only p-adic valuations are relevant.
    smith = fmpz_mat(cols).snf()
    invariants = [valuation(int(smith[i, i]), p) for i in range(len(cols))]
    initial = cols[:bound]
    rows = pivot_rows(initial[:-1], p)
    assert len(rows) == bound - 1
    square = nmod_mat(bound - 1, bound - 1,
                      [initial[j][i] for i in rows for j in range(bound - 1)], p * p)
    last = nmod_mat(bound - 1, 1, [initial[-1][i] for i in rows], p * p)
    relation = square.inv() * last
    c = [int(relation[i, 0]) for i in range(bound - 1)]
    residual = [(initial[-1][i] - sum(c[j] * initial[j][i] for j in range(bound - 1))) % (p * p)
                for i in range(space.dim)]
    assert all(x % p == 0 for x in residual)
    extra = next(i for i, x in enumerate(residual) if x)
    witness_rows = rows + [extra]
    witness = [[initial[j][i] for j in range(bound)] for i in witness_rows]
    det = int(fmpz_mat(witness).det())
    assert valuation(det, p) == 1
    assert invariants == [0] * (bound - 1) + [1] + [2] * (len(cols) - bound)
    # The next two odd iterates add nothing: integer Smith invariants unchanged.
    prefix_smith = fmpz_mat(initial).snf()
    assert [valuation(int(prefix_smith[i, i]), p) for i in range(bound)] == invariants[:bound]
    short_columns = [col[:min(80, space.dim)] for col in cols]
    return dict(prime=p, precision=2, cutoff=cutoff, uniform_weight=space.weight,
                dimension=space.dim, coefficient_length=space.length,
                first_odd_index=3, odd_vectors=len(cols),
                holdout_coefficients_checked=space.holdout_checks,
                smith_valuations=invariants, number_of_generators=bound,
                free_summands=bound - 1,
                witness_rows=witness_rows, witness_matrix=witness,
                unit_minor_det_mod_p=int(square.det()) % p,
                determinant_div_p_mod_p=(det // p) % p,
                lifting_relation=c, residual_witness_coefficient=extra,
                residual_div_p_mod_p=residual[extra] // p,
                initial_q_coefficients=short_columns,
                initial_q_sha256=hashlib.sha256(json.dumps(short_columns).encode()).hexdigest(),
                elapsed_seconds=round(time.time() - start, 2),
                status="Finite experiment; arithmetic identification not kernel certified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=607)
    parser.add_argument("--cutoff", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = analyze(args.prime, args.cutoff)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in {"witness_matrix", "initial_q_coefficients", "lifting_relation"}}, indent=2))


if __name__ == "__main__":
    main()
