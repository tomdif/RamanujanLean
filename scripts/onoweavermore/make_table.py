#!/usr/bin/env python3
"""Markdown table of all congruences proved in RamanujanTau/OnoWeaverMore (from scan500.json and
crosscheck.txt). Usage: make_table.py scan500.json crosscheck.txt"""
import json, sys, ast
EXISTING = {(13, 59), (13, 73), (17, 41), (17, 89), (17, 103), (19, 101), (23, 5), (23, 19), (23, 37), (23, 47), (23, 67)}
data = json.load(open(sys.argv[1]))
cc = {}
for line in open(sys.argv[2]):
    if line.startswith('('):
        t = ast.literal_eval(line); cc[(t[0], t[1])] = t
print('| ℓ | Q | ε | statement | Lean theorem | new? | eigen coeffs checked | direct p(n) checks (fail) |')
print('|---|---|---|---|---|---|---|---|')
for r in data:
    l = r['ell']
    for x in r['res']:
        if not x.get('type'): continue
        Q = x['Q']; t = x['type'][0]; e = 0 if t == 'ono' else (1 if t == 'atkin+' else -1)
        st = f'{l} ∣ p(({l}·{Q}³n+1)/24), {Q}∤n' if e == 0 else f'{l} ∣ p(({l}·{Q}²m+1)/24), (m/{Q})={e:+d}'
        nm = f'L{l}.' + (f'ono_{l}_{Q}' if e == 0 else f'atkin_{l}_{Q}')
        new = 'existing' if (l, Q) in EXISTING else 'new'
        c = cc[(l, Q)]
        print(f'| {l} | {Q} | {e:+d} | {st} | `{nm}` | {new} | {x["checked"]} | {c[3]} ({c[4]}) |')
