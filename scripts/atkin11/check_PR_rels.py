"""Cross-check a few of Paule-Radu's 550 fundamental relations (RISC site) against our direct computation:
rel_s_m_k.txt = U11(u^s * J_m * t^k) with u=phi, t=z, J[0]=t?, J[1..4]=g2,g3,g4,g6 ; compare with C^s_{5k+m}."""
import re, sys
from gordon_matrix import Ctx, C
def parse(fn):
    s = open(fn).read().strip().rstrip(";").split(":=")[1]
    out = {}
    for m in re.finditer(r'([+-]?)(\d*)\*?((?:J\[\d\](?:\^\d+)?\*?)*)', s):
        sg, c, mon = m.groups()
        if not c and not mon: continue
        c = int(c) if c else 1
        a = 0; i = 0
        for jm in re.finditer(r'J\[(\d)\](?:\^(\d+))?', mon):
            idx, e = int(jm.group(1)), int(jm.group(2) or 1)
            if idx == 0: a += e
            else: i = idx; assert e == 1
        nu = 5*a + i
        out[nu] = out.get(nu, 0) + (-c if sg == '-' else c)
    return {k: v for k, v in out.items() if v}
ctx = Ctx(11*300 + 400)
for (s, m, k) in [(1, 0, 0), (0, 0, 1), (1, 1, 0), (0, 3, 1), (1, 2, 1), (1, 4, 2), (0, 4, 3)]:
    pr = parse(f"dl/rels/rel_{s}_{m}_{k}.txt")
    ours = {nu: int(v) for nu, v in C(ctx, s, 5*k + m, 300).items()}
    print((s, m, k), "PR terms", len(pr), "ours", len(ours), "MATCH" if pr == ours else "DIFFER")
