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

source = (Path(__file__).resolve().parents[2] /
          "RamanujanTau/FiniteArithmetic/Cert29Error.lean").read_text()
data = {name: ast.literal_eval(values) for name, values in
        re.findall(r"def (\w+) : List ℤ := (\[[^\n]*\])", source)}
assert data and all(0 <= x < 841 for values in data.values() for x in values)
encoded = {name: int.from_bytes(b"".join(x.to_bytes(4, "little") for x in values), "little")
           for name, values in data.items()}
checks = re.findall(r"theorem (\w+) : tmul 841 1682 (\w+) (\w+) = (\w+)", source)
assert len(checks) == 16, "Unexpected certificate layout"
for label, a, b, result in checks:
    assert min(len(data[a]), len(data[b])) * 840**2 < 2**32
    length = min(1683, len(data[a]) + len(data[b]) - 1)
    product = encoded[a] * encoded[b]
    raw = (product % (1 << (32 * length))).to_bytes(4 * length, "little")
    actual = [int.from_bytes(raw[4*i:4*i+4], "little") % 841 for i in range(length)]
    assert actual == data[result], label

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
print("Passed: 16 products, divisor formulas, Euler coefficients, shifts, linear combination, and 3 observations.")
