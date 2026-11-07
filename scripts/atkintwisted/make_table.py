#!/usr/bin/env python3
"""Markdown tables for docs/ATKIN_TWISTED_ALL_Q.md from scan500.json, crosscheck.json, theorem_names.json."""
import json
scan = json.load(open('scan500.json'))['res']; cc = {r['Q']: r for r in json.load(open('crosscheck.json'))}
names = {n[0]: n for n in json.load(open('theorem_names.json'))}
known = {11: 'Atkin 1968', 37: 'repo (Atkin13Main)'}
print('| Q | μ | s | type | class (13 ∣ p(N)) | progression | Lean (class / progression) | class N≤1.2e7 checked (fail) | control nonzero | exact p at n=0,1 |')
print('|---|---|---|---|---|---|---|---|---|---|')
for x in scan:
    Q = x['Q']
    if Q not in cc: continue
    r = cc[Q]; n = names[Q]
    if r['type'] == 'ono':
        cls = f"24N−1 = {Q}³n, {Q}∤n, ({Q}n/13)=−1"; typ = 'Ono (μ=0)'
    else:
        e = '+1' if r['type'] == 'atkin+' else '−1'
        cls = f"24N−1 = {Q}²m, (m/{Q})={e}, (m/13)=−1"; typ = f'Atkin ε={e}'
    print(f"| {Q} | {x['mu']} | {x['s']:+d} | {typ} | {cls} | p({r['modulus']}n+{r['residue']}) | `{n[3]}` / `{n[4]}` | {r['checked']} ({r['fail']}) | {r['control_nonzero']}/{r['control']} | 0, 0 |")
print()
print('All eigenvalues μ(Q) (T(Q²)F̄ = μF̄ mod 13), every prime 5 ≤ Q < 500, Q ≠ 13:')
print()
print(', '.join(f"{x['Q']}:{x['mu']}" for x in scan))
