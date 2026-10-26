"""(1) base data C^lam_{i,.}, lam=0..10, i=0..4 (sizes);
(2) recurrence  C^lam_i = sum_j (-1)^{j+1} e_j * C^{lam-j}_i  (product in V via structure constants) checked against direct U computation;
(3) finite check that Gordon's bound B(lam,i,nu)=floor((11nu-i-5lam+delta(i,nu%5))/10) (delta(2,3)=3) is INDUCTIVE under the recurrence."""
import json, sys
from fractions import Fraction
from gordon_matrix import Ctx, C
from qs import val_p

DELTA = [[-1, 8, 7, 6, 15], [0, 9, 8, 2, 11], [1, 10, 4, 3, 12], [2, 6, 5, 4, 13], [3, 7, 6, 5, 9]]
def B(lam, i, nu): return (11*nu - i - 5*lam + DELTA[i][nu % 5]) // 10
def v11(x): return val_p(x, 11)

# modular equation phi^11 = sum_j (-1)^{j+1} e_j(q^11) phi^{11-j}; e_j as {nu: coeff} in J basis (J1=g2,J2=g3,J3=g4,J5=z)
E = {1: {1: 121, 2: 2662, 3: 14641, 5: 161051}, 2: {1: -11, 2: 968, 3: 11979, 5: 161051},
     3: {2: 242, 3: 5324, 5: 73205}, 4: {2: 22, 3: 1452, 5: 14641}, 5: {3: 242, 5: -1331},
     6: {3: 22, 5: -1331}, 7: {5: -121}, 8: {5: 121}, 9: {5: 55}, 10: {5: 11}, 11: {5: 1}}
ST = {tuple(map(int, k.split(","))): {int(t): v for t, v in d.items()} for k, d in json.load(open("structure.json")).items()}
def prodJ(b, nu):
    """J_b * J_nu as dict (b in 0..4 or b=5 meaning z)."""
    a, r = divmod(nu, 5)
    if b == 5: return {nu + 5: 1}
    if b == 0: return {nu: 1}
    if r == 0: return {b + 5*a: 1}
    key = (min(b, r), max(b, r))
    return {t + 5*a: s for t, s in ST[key].items()}
def mulV(e, c):
    out = {}
    for b, cb in e.items():
        for nu, cn in c.items():
            for t, s in prodJ(b, nu).items():
                out[t] = out.get(t, 0) + cb*cn*s
    return {k: v for k, v in out.items() if v != 0}

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 260
    ctx = Ctx(11*N + 400)
    base = {}
    tot_terms = 0; tot_digits = 0
    for i in range(5):
        for lam in range(0, 11):
            c = {k: int(v) for k, v in C(ctx, lam, i, N).items()}
            base[(lam, i)] = c
            tot_terms += len(c); tot_digits += sum(len(str(abs(x))) for x in c.values())
    print("base data lam=0..10, i=0..4: 55 relations, %d nonzero coefficients, %d total decimal digits" % (tot_terms, tot_digits))
    for i in range(5):
        print("  i=%d: max nu per lam:" % i, [max(base[(l, i)]) for l in range(11)])
    json.dump({f"{l},{i}": {str(k): str(v) for k, v in c.items()} for (l, i), c in base.items()}, open("base_C.json", "w"))
    # (2) recurrence vs direct for lam = 11..14
    cur = dict(base)
    for lam in range(11, 15):
        for i in range(5):
            acc = {}
            for j, e in E.items():
                for k, v in mulV(e, cur[(lam-j, i)]).items():
                    acc[k] = acc.get(k, 0) + (-1)**(j+1)*v
            acc = {k: v for k, v in acc.items() if v != 0}
            cur[(lam, i)] = acc
            direct = {k: int(v) for k, v in C(ctx, lam, i, N).items()}
            assert acc == direct, (lam, i)
    print("recurrence (modular eq + structure constants) reproduces direct U11 computation for lam=11..14: OK")
    # base cases satisfy bound
    okb = all(v11(v) >= B(l, i, nu) for (l, i), c in base.items() for nu, v in c.items())
    print("Gordon bound holds on all 55 base relations:", okb)
    # (3) inductive check over residues: X = -i - 5lam + 55a; need for all j, b in e_j, nu'=r'+5a, t:
    #   v(c_jb) + v(s) + max(B(lam-j,i,nu'),0) >= B(lam,i,t+5a)
    bad = []; minslack = 99
    for i in range(5):
        for lp in range(2):          # lam parity (lam large, take lam = 100 + lp)
            for ap in range(2):      # a parity (a large: 40+ap)
                lam = 1000 + lp; a = 40 + ap
                for j, e in E.items():
                    for b, cb in e.items():
                        for r in range(5):
                            nu1 = r + 5*a
                            for t, s in prodJ(b, nu1).items():
                                lhs = v11(cb) + v11(s) + max(B(lam-j, i, nu1), 0)
                                rhs = B(lam, i, t)
                                minslack = min(minslack, lhs - rhs)
                                if lhs < rhs: bad.append((i, lp, ap, j, b, r, t, lhs, rhs))
    print("inductive step check (large lam, nu): violations =", len(bad), "min slack =", minslack)
    for x in bad[:20]: print("  ", x)
