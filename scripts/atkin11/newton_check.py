"""Check 11*U11(phi^k) = p_k (power sums of the roots of the modular equation), k=1..10, via Newton's identities in V."""
import json
from induct_check import E, mulV
base = {tuple(map(int, k.split(","))): {int(a): int(b) for a, b in v.items()} for k, v in json.load(open("base_C.json")).items()}
def add(a, b, s=1):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, 0) + s*v
    return {k: v for k, v in out.items() if v}
p = {0: {0: 11}}
ok = True
for k in range(1, 11):
    acc = {}
    for j in range(1, k):
        acc = add(acc, mulV(E[j], p[k-j]), (-1)**(j+1))
    acc = add(acc, {nu: k*c for nu, c in E[k].items()}, (-1)**(k+1))
    p[k] = acc
    target = {nu: 11*c for nu, c in base[(k, 0)].items()}
    ok &= (acc == target)
print("11*U(phi^k) == Newton power sum p_k for k=1..10:", ok)
