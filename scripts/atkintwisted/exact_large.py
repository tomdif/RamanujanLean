#!/usr/bin/env python3
"""Exact p(N) (FLINT's Hardy-Ramanujan-Rademacher, python-flint fmpz.partitions_p) mod 13 at the first
few members of each progression from crosscheck.json, including the large-Q Ono residues beyond the
sieved prefix. Usage: exact_large.py crosscheck.json [K]"""
import sys, json, flint
rows = json.load(open(sys.argv[1])); K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
for r in rows:
    vals = [int(flint.fmpz(r['modulus'] * t + r['residue']).partitions_p() % 13) for t in range(K)]
    print(r['Q'], r['type'], f"13 | p({r['modulus']} n + {r['residue']})", 'n<%d:' % K, vals)
