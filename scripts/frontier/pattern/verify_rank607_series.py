#!/usr/bin/env python3
"""Replay the 607 series witness with exact standard-library arithmetic.

No FLINT, SymPy, Katz-coordinate code, or generator code is used. Polynomial
convolution uses integer multiplication with base 2^64; a checked coefficient
bound prevents carries between slots. The reconstruction space is
  E606^-2 * span{Delta^t E4^(303-3t): 0 <= t <= 101}.

The mathematical comparison uses the Katz envelope bounds and the finite
q-expansion theorem (FormalSturm / EnvelopePrecision). This program's arithmetic
is independently checked computation, not execution in Lean's kernel.
"""
from array import array
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

P = 607
MOD = P * P
DIM = 102
LENGTH = P * (DIM - 1) + 1
SHIFT = (P * P - 1) // 24
BITS = 64
MASK = (1 << (BITS * LENGTH)) - 1


def pack(values):
    return int.from_bytes(array('Q', values).tobytes(), 'little')


def unpack(value, length=LENGTH):
    out = array('Q')
    out.frombytes((value & ((1 << (BITS * length)) - 1)).to_bytes(8 * length, 'little'))
    return out


def normalize(value, length=LENGTH):
    return pack(x % MOD for x in unpack(value, length))


def mul(a, b, length=LENGTH):
    # Both operands have reduced coefficients and degree < LENGTH.
    assert LENGTH * (MOD - 1) ** 2 < 2 ** BITS
    return normalize(a * b, length)


def power(a, exponent):
    out = 1
    while exponent:
        if exponent & 1:
            out = mul(out, a)
        exponent //= 2
        if exponent:
            a = mul(a, a)
    return out


def inverse(a):
    out, length = pow(a % (1 << BITS), -1, MOD), 1
    while length < LENGTH:
        length = min(2 * length, LENGTH)
        prod = unpack(mul(a, out, length), length)
        correction = pack(((2 if i == 0 else 0) - x) % MOD for i, x in enumerate(prod))
        out = mul(out, correction, length)
    return out


def divisor_sums(exponent, modulus):
    values = [0] * LENGTH
    for d in range(1, LENGTH):
        v = pow(d, exponent, modulus)
        for i in range(d, LENGTH, d):
            values[i] += v
    return [v % modulus for v in values]


def verify(witness_path, output):
    assert sys.byteorder == 'little' and array('Q').itemsize == 8
    assert SHIFT == 15352 and LENGTH == 61308
    start = time.time()
    sigma3 = divisor_sums(3, MOD)
    e4 = pack([(1 if i == 0 else 0) + (240 * sigma3[i]) % MOD for i in range(LENGTH)])
    # Von Staudt-Clausen: p*B_(p-1) == -1 mod p, hence
    # E_(p-1) == 1 - 2p*sum sigma_(p-2)(n) q^n mod p^2.
    # Squaring its inverse gives 1 + 4p*sum sigma_(p-2)(n) q^n.
    sigma605 = divisor_sums(605, P)
    einv2 = pack([(1 if i == 0 else 0) + (4 * P * sigma605[i]) % MOD for i in range(LENGTH)])
    eta = [0] * LENGTH
    eta[0] = 1
    for n in range(1, LENGTH):
        a = n * (3 * n - 1) // 2
        if a >= LENGTH:
            break
        eta[a] = (-1) ** n % MOD
        if a + n < LENGTH:
            eta[a + n] = (-1) ** n % MOD
    eta = pack(eta)
    delta = (power(eta, 24) << BITS) & MASK
    phi = (inverse(eta) << (BITS * SHIFT)) & MASK
    ratio = mul(delta, power(inverse(e4), 3))
    current = mul(power(e4, 303), einv2)
    basis, low = [], []
    for t in range(DIM):
        basis.append(current)
        coefficients = list(unpack(current, DIM))
        assert coefficients[:t] == [0] * t and coefficients[t] == 1
        low.append(coefficients)
        if t + 1 < DIM:
            current = mul(current, ratio)
        if t % 25 == 0:
            print(f'basis {t}/{DIM - 1}, elapsed {time.time() - start:.1f}s', flush=True)
    saved = json.loads(witness_path.read_text())
    expected = saved['initial_q_coefficients']
    f, observed, coordinates = 1, [], []
    for b in range(1, 56):
        if b % 2:
            f = mul(phi, f)
        coefficients = unpack(f)
        prefix = [coefficients[P * i] for i in range(DIM)]
        remainder = prefix[:]
        coords = []
        for t in range(DIM):
            c = remainder[t] % MOD
            coords.append(c)
            for i in range(t, DIM):
                remainder[i] = (remainder[i] - c * low[t][i]) % MOD
        assert not any(remainder)
        # This sum cannot carry between 64-bit slots either.
        assert DIM * (MOD - 1) ** 2 < 2 ** BITS
        f = normalize(sum(c * base for c, base in zip(coords, basis)))
        coordinates.append(coords)
        if b >= 3 and b % 2:
            observed.append(prefix[:80])
            assert observed[-1] == expected[len(observed) - 1], ('iterate differs', b)
        if b % 10 == 0:
            print(f'iterate L({b}) checked, elapsed {time.time() - start:.1f}s', flush=True)
    assert len(observed) == 27 and observed == expected
    witness = [[observed[j][i] for j in range(25)] for i in range(26, 51)]
    assert witness == saved['witness_matrix']
    # This relation holds in the entire 102-dimensional reconstruction
    # space modulo p, not just on the 25 rows of the determinant witness.
    orbit = [coordinates[b - 1] for b in range(3, 52, 2)]
    relation = saved['lifting_relation']
    assert all((orbit[-1][i] - sum(relation[j] * orbit[j][i] for j in range(24))) % P == 0
               for i in range(DIM))
    assert relation[0] % P == 36  # A unit; the 24-dimensional tail is stable.
    record = dict(prime=P, modulus=MOD, dimension=DIM, coefficient_length=LENGTH,
                  odd_iterates_matched=27, matched_coefficients=27 * 80,
                  witness_matrix_matched=True,
                  full_mod_p_relation_checked=True,
                  mod_p_relation_constant=relation[0] % P,
                  arithmetic='Python integers, carry-free Kronecker convolution',
                  generator_imported=False, flint_or_sympy_used=False,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  initial_q_sha256=hashlib.sha256(json.dumps(observed).encode()).hexdigest(),
                  iterate_coordinates=coordinates,
                  elapsed_seconds=round(time.time() - start, 2),
                  lean_kernel_numeric_verification=False)
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k != 'iterate_coordinates'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    verify(args.witness, args.output)
