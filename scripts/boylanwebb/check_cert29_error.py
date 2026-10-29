#!/usr/bin/env python3
"""Fast independent arithmetic check; the Lean kernel remains the proof authority.

Encode coefficient lists in base 2**32 and use integer multiplication, instead
of the generator's nested convolution loops. The coefficient bound prevents
carries between digits before reduction modulo 841.
"""
import ast
from math import isqrt
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2] / "RamanujanTau/FiniteArithmetic"
source = (root / "Cert29ErrorData.lean").read_text()
data = {name: ast.literal_eval(values) for name, values in
        re.findall(r"def (\w+) : List ℤ := (\[[^\n]*\])", source)}
assert data and all(0 <= x < 841 for values in data.values() for x in values)
def packed_product(a, b, degree):
    assert min(len(a), len(b)) * 840**2 < 2**32
    assert all(0 <= x < 841 for x in a + b)
    length = min(degree + 1, len(a) + len(b) - 1)
    pack = lambda values: int.from_bytes(b"".join(x.to_bytes(4, "little") for x in values), "little")
    product = pack(a) * pack(b)
    raw = (product % (1 << (32 * length))).to_bytes(4 * length, "little")
    return [int.from_bytes(raw[4*i:4*i+4], "little") % 841 for i in range(length)]

files = sorted((root / "Cert29ErrorProducts").glob("*.lean"))
assert len(files) == 16, "Unexpected certificate layout"
blocks = 0
for file in files:
    source = file.read_text()
    checks = re.findall(r"theorem (\w+)_check : Cg 841 1682 \(toPS (\w+) \* toPS (\w+)\) \(toPS (\w+)\)", source)
    assert len(checks) == 1, file
    label, a, b, result = checks[0]
    assert file.stem == label
    assert packed_product(data[a], data[b], 1682) == data[result], label
    local = {}
    for name, value in re.findall(r"def (\w+) : List ℤ := (\[[^\n]*\]|\w+)", source):
        local[name] = ast.literal_eval(value) if value.startswith("[") else data[value]
    offsets = sorted(int(name[5:]) for name in local if name.startswith("block"))
    assert offsets == list(range(0, min(1683, len(data[a])), 64)), label
    for offset in offsets:
        assert local[f"tail{offset}"] == data[a][offset:]
        assert local[f"block{offset}"] == data[a][offset:offset + 64]
        assert local[f"out{offset}"] == packed_product(data[a][offset:], data[b], 1682 - offset)
        blocks += 1

# Check the non-product facts too. Divisor pairs are independent of the
# generator's sieve over multiples.
def sigma_mod(exponent, n):
    total = 0
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            total += pow(d, exponent, 841)
            if d * d != n:
                total += pow(n // d, exponent, 841)
    return total % 841

assert data["E4L"] == [1] + [240 * sigma_mod(3, n) % 841 for n in range(1, 1683)]
assert data["EL"] == [1] + [783 * sigma_mod(27, n) % 841 for n in range(1, 1683)]
euler = [0] * 1683
for k in range(-1682, 1683):
    index = k * (3 * k - 1) // 2
    if index <= 1682:
        euler[index] = (-1 if k % 2 else 1) % 841
while euler[-1] == 0:
    euler.pop()
assert data["Q"] == euler
assert data["One"] == [1] + [0] * 1682
assert data["EV"] == [euler[n // 841] if n % 841 == 0 else 0 for n in range(1683)]
assert data["Delta"] == ([0] + data["Q24"])[:1683]
assert data["Phi"] == ([0] * 35 + data["EP"])[:1683]
assert data["LG"] == [(3 * h + 6 * f) % 841 for h, f in zip(data["LH"], data["LF"])]
for name, value in [("YF", 348), ("YG", 725), ("Phi", 696)]:
    assert (3 * data[name][1682] - data[name][841]) % 841 == value, name
print(f"Passed: 16 products, {blocks} blocks, divisor formulas, Euler coefficients, shifts, linear combination, and 3 observations.")
