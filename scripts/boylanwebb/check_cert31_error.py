#!/usr/bin/env python3
"""Fast independent arithmetic check; the Lean kernel remains the proof authority.

Encode coefficient lists in base 2**32 and use integer multiplication, instead
of the generator's nested convolution loops. The coefficient bound prevents
carries between digits before reduction modulo 961.
"""
import ast
from math import isqrt
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2] / "RamanujanTau/FiniteArithmetic"
source = (root / "Cert31ErrorData.lean").read_text()
data = {name: ast.literal_eval(values) for name, values in
        re.findall(r"def (\w+) : List ℤ := (\[[^\n]*\])", source)}
assert data and all(0 <= x < 961 for values in data.values() for x in values)
def packed_product(a, b, degree):
    assert min(len(a), len(b)) * 960**2 < 2**32
    assert all(0 <= x < 961 for x in a + b)
    length = min(degree + 1, len(a) + len(b) - 1)
    pack = lambda values: int.from_bytes(b"".join(x.to_bytes(4, "little") for x in values), "little")
    product = pack(a) * pack(b)
    raw = (product % (1 << (32 * length))).to_bytes(4 * length, "little")
    return [int.from_bytes(raw[4*i:4*i+4], "little") % 961 for i in range(length)]

files = sorted((root / "Cert31ErrorProducts").glob("*.lean"))
assert len(files) == 17, "Unexpected certificate layout"
blocks = 0
for file in files:
    source = file.read_text()
    checks = re.findall(r"theorem (\w+)_check : Cg 961 1922 \(toPS (\w+) \* toPS (\w+)\) \(toPS (\w+)\)", source)
    assert len(checks) == 1, file
    label, a, b, result = checks[0]
    assert file.stem == label
    assert packed_product(data[a], data[b], 1922) == data[result], label
    local = {}
    for name, value in re.findall(r"def (\w+) : List ℤ := (\[[^\n]*\]|\w+)", source):
        local[name] = ast.literal_eval(value) if value.startswith("[") else data[value]
    offsets = sorted(int(name[5:]) for name in local if name.startswith("block"))
    assert offsets == list(range(0, min(1923, len(data[a])), 64)), label
    for offset in offsets:
        assert local[f"tail{offset}"] == data[a][offset:]
        assert local[f"block{offset}"] == data[a][offset:offset + 64]
        assert local[f"out{offset}"] == packed_product(data[a][offset:], data[b], 1922 - offset)
        blocks += 1

# Check the non-product facts too. Divisor pairs are independent of the
# generator's sieve over multiples.
def sigma_mod(exponent, n):
    total = 0
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            total += pow(d, exponent, 961)
            if d * d != n:
                total += pow(n // d, exponent, 961)
    return total % 961

assert data["E4L"] == [1] + [240 * sigma_mod(3, n) % 961 for n in range(1, 1923)]
assert data["E6L"] == [1] + [-504 * sigma_mod(5, n) % 961 for n in range(1, 1923)]
assert data["EL"] == [1] + [899 * sigma_mod(29, n) % 961 for n in range(1, 1923)]
euler = [0] * 1923
for k in range(-1922, 1923):
    index = k * (3 * k - 1) // 2
    if index <= 1922:
        euler[index] = (-1 if k % 2 else 1) % 961
while euler[-1] == 0:
    euler.pop()
assert data["Q"] == euler
assert data["One"] == [1] + [0] * 1922
assert data["EV"] == [euler[n // 961] if n % 961 == 0 else 0 for n in range(1923)]
assert data["Delta"] == ([0] + data["Q24"])[:1923]
assert data["Phi"] == ([0] * 40 + data["EP"])[:1923]
assert data["LG"] == [(29 * h + 14 * f) % 961 for h, f in zip(data["LH"], data["LF"])]
for name, value in [("YF", 217), ("YG", 651), ("Phi", 0)]:
    assert (29 * data[name][1922] - 2 * data[name][961]) % 961 == value, name
print(f"Passed: 17 products, {blocks} blocks, divisor formulas, Euler coefficients, shifts, linear combination, and 3 observations.")
