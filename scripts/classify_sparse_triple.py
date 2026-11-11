#!/usr/bin/env python3
"""Classify persistent zero progressions of an admissible sparse triple.

Uses the root criterion proved in MultiQuintupleFullConverse.lean, together
with the centered-root argument in docs/paper/sparse-triples.tex. This exact
reference implementation is not extracted Lean code. No coefficient cutoff
is used to decide vanishing. Arithmetic-operation count is O(p log p) using
Python's modular inverses; this is not a bit-complexity claim.
"""
import argparse
import json
from math import isqrt


def classify(p, i, j, k):
    if p < 7 or any(p % d == 0 for d in range(2, isqrt(p)+1)):
        raise ValueError("the modulus must be prime and at least 7")
    if not 0 < i < j < k or 2*k >= p:
        raise ValueError("indices must satisfy 0 < i < j < k and 2*k < p")
    indices = (i, j, k)
    if sum(a*a for a in indices) % p:
        raise ValueError("the squared sum of the indices must be divisible by p")
    roots = []
    half = p//2
    for lam in range(1, p):
        w = tuple((lam*a+half) % p-half for a in indices)
        norm = sum(a*a for a in w)
        if norm not in (p, 2*p):
            continue
        e = norm//p
        c = 2//e
        pairing = sum(a*b for a, b in zip(indices, w))
        if pairing % p:
            raise AssertionError("isotropy failed to give an integral pairing")
        u = pairing//p
        base = sum(w)-6*u
        if norm % 3 == 1:
            r = base*pow(2*lam, -1, p) % p
        else:
            r = (12+c*lam*base)*pow(2*c*lam*lam, -1, p) % p
        roots.append({"lambda": lam, "w": w, "e": e, "c": c, "u": u, "R": r})
    return {"modulus": p, "indices": indices,
            "zero_residues": sorted({root['R'] for root in roots}),
            "root_certificates": roots,
            "scalars_checked": p-1,
            "scope": "Exact root-criterion reference implementation; not extracted Lean code"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int)
    parser.add_argument("i", type=int)
    parser.add_argument("j", type=int)
    parser.add_argument("k", type=int)
    args = parser.parse_args()
    try:
        result = classify(args.p, args.i, args.j, args.k)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
