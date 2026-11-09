#!/usr/bin/env python3
"""Matrix-ECS expansions of products of two theta functions (Cao, arXiv:2503.11445), in the Lean conventions
of RamanujanTau/Forty/Lattice.lean:

  theta_N(e, w) = sum_k (-1)^k w^k t^{N C(k,2) + e k}         (w = +-1)

Type I : theta_{N1}(e1,w1) theta_{N2}(e2,w2) = sum_{i in I} t^{N1 C(i,2) + e1 i} (-w1)^i theta_{M1}(f1,d1) theta_{M2}(f2,d2)
Type II: sum_{x in Z^2} (-1)^{d.x} t^{Q(x)} split along two ECSs.

The script finds a shift direction and window making B an exact cover, prints every coset term in canonical form
(theta arguments reduced to 0 <= e <= N/2 by reflection; quasi-period shifts reported), and checks numerically.
"""
import itertools
import sys

PREC = 120


def c2(k):
    return k * (k - 1) // 2


def theta_series(N, e, w, prec=PREC, shift=200):
    """coefficients of t^{n} for n in [-shift, prec) (dict)"""
    out = {}
    for k in range(-60, 61):
        E = N * c2(k) + e * k
        if -shift <= E < prec:
            out[E] = out.get(E, 0) + ((-1) ** (k % 2)) * (w ** (k % 2) if w in (1, -1) else w ** k)
    return out


def smul(a, b, prec=PREC):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            if i + j < prec:
                out[i + j] = out.get(i + j, 0) + x * y
    return out


def sadd(a, b, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}


def mono(E, C):
    return {E: C}


def find_ecs(b, rr=None, window=None, lo_range=None):
    b11, b12, b21, b22 = b
    det = b11 * b22 - b12 * b21
    k = abs(det)
    cands = [rr] if rr else [(1, 0), (0, 1)]
    for r in cands:
        for lo in (lo_range if lo_range is not None else range(-k, 1)):
            I = list(range(lo, lo + k)) if window is None else window
            ok = True
            seen = {}
            # exact cover check on a box (periodic mod k*... enough)
            for m in range(-2 * k, 2 * k):
                for n in range(-2 * k, 2 * k):
                    hits = []
                    for i in I:
                        x, y = m - r[0] * i, n - r[1] * i
                        u_num = b22 * x - b12 * y
                        v_num = b11 * y - b21 * x
                        if u_num % det == 0 and v_num % det == 0:
                            hits.append(i)
                    if len(hits) != 1:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                return r, I
            if window is not None:
                break
    return None


def canon(N, f, w):
    """theta_N(f,w) = coef * t^E * theta_N(f0, w) with 0 <= f0 < N, then reflection to f0 <= N/2.
    returns (coef, E, f0, w) ; coef=0 if vanishing"""
    # theta(e0 + N k, w) = (-1)^k w^{-k} t^{-(k e0 + N C(k,2))} theta(e0, w)
    k = f // N
    e0 = f - N * k
    coef = ((-1) ** (k % 2)) * (w ** (k % 2))
    E = -(k * e0 + N * c2(k))
    if e0 == 0 and w == 1:
        return (0, 0, 0, w)
    refl = False
    if e0 > N - e0:  # theta(N - e, 1/w) = theta(e, w)
        e0 = N - e0
        refl = True
    return (coef, E, e0, w, k, refl)


def typeI(N1, e1, w1, N2, e2, w2, b, rr=(1, 0), window=None):
    b11, b12, b21, b22 = b
    assert N1 * b11 * b12 + N2 * b21 * b22 == 0, "not orthogonal"
    M1 = N1 * b11 ** 2 + N2 * b21 ** 2
    M2 = N1 * b12 ** 2 + N2 * b22 ** 2
    res = find_ecs(b, rr, window)
    assert res, "no ECS"
    r, I = res
    terms = []
    for i in I:
        E = N1 * c2(i) + e1 * i
        C = ((-1) ** (i % 2)) * (w1 ** (i % 2))
        f1 = N1 * c2(b11) + N2 * c2(b21) + N1 * b11 * i + e1 * b11 + e2 * b21
        f2 = N1 * c2(b12) + N2 * c2(b22) + N1 * b12 * i + e1 * b12 + e2 * b22
        d1 = -((-1) ** ((b11 + b21) % 2)) * (w1 ** (b11 % 2)) * (w2 ** (b21 % 2))
        d2 = -((-1) ** ((b12 + b22) % 2)) * (w1 ** (b12 % 2)) * (w2 ** (b22 % 2))
        terms.append((i, E, C, (M1, f1, d1), (M2, f2, d2)))
    lhs = smul(theta_series(N1, e1, w1), theta_series(N2, e2, w2))
    rhs = {}
    for (i, E, C, t1, t2) in terms:
        rhs = sadd(rhs, smul(mono(E, C), smul(theta_series(*t1), theta_series(*t2))))
    ok = all(lhs.get(n, 0) == rhs.get(n, 0) for n in range(-50, PREC - 10))
    return r, I, terms, ok


def typeII(A, Bq, C, d, e, de1, de2, b, rr=None, window=None, lo_range=None):
    b11, b12, b21, b22 = b
    assert A * b11 * b12 + Bq * (b11 * b22 + b12 * b21) + C * b21 * b22 == 0, "not orthogonal"
    res = find_ecs(b, rr, window, lo_range)
    assert res, "no ECS"
    r, I = res
    A1 = A * b11 ** 2 + 2 * Bq * b11 * b21 + C * b21 ** 2
    A2 = A * b12 ** 2 + 2 * Bq * b12 * b22 + C * b22 ** 2
    terms = []
    for i in I:
        p1, p2 = r[0] * i, r[1] * i
        f1 = A1 + (2 * A * b11 * p1 + 2 * Bq * (b11 * p2 + b21 * p1) + 2 * C * b21 * p2 + d * b11 + e * b21)
        f2 = A2 + (2 * A * b12 * p1 + 2 * Bq * (b12 * p2 + b22 * p1) + 2 * C * b22 * p2 + d * b12 + e * b22)
        E = A * p1 ** 2 + 2 * Bq * p1 * p2 + C * p2 ** 2 + d * p1 + e * p2
        Cc = (-1) ** ((de1 * p1 + de2 * p2) % 2)
        s1 = -((-1) ** ((de1 * b11 + de2 * b21) % 2))
        s2 = -((-1) ** ((de1 * b12 + de2 * b22) % 2))
        terms.append((i, E, Cc, (2 * A1, f1, s1), (2 * A2, f2, s2)))
    # direct sum
    S = {}
    for x1 in range(-40, 41):
        for x2 in range(-40, 41):
            Q = A * x1 * x1 + 2 * Bq * x1 * x2 + C * x2 * x2 + d * x1 + e * x2
            if Q < PREC:
                S[Q] = S.get(Q, 0) + (-1) ** ((de1 * x1 + de2 * x2) % 2)
    rhs = {}
    for (i, E, Cc, t1, t2) in terms:
        rhs = sadd(rhs, smul(mono(E, Cc), smul(theta_series(*t1), theta_series(*t2))))
    ok = all(S.get(n, 0) == rhs.get(n, 0) for n in range(-50, PREC - 10))
    return r, I, terms, ok


def show(name, res):
    r, I, terms, ok = res
    print(f"== {name}: r={r} I={I} numeric={'OK' if ok else 'FAIL'}")
    for (i, E, C, t1, t2) in terms:
        c1 = canon(*t1)
        c2_ = canon(*t2)
        print(f"  i={i:3d}: t^{E} * {C:+d} * th{t1} * th{t2}   canon1={c1} canon2={c2_}")


def canon_terms_local(terms):
    out = {}
    for (i, E, C, t1, t2) in terms:
        tot_E, tot_C, gs, zero = E, C, [], False
        for (M, f, c) in (t1, t2):
            k = f // M
            e0 = f - M * k
            if e0 == 0 and c == 1:
                zero = True
                break
            tot_E += -(M * c2(k + 1)) - e0 * k + M * k
            tot_C *= ((-1) ** (k % 2)) * (c ** (k % 2))
            gs.append((M, e0 if e0 <= M - e0 else M - e0, c))
        if zero:
            continue
        key = (tot_E, gs[0], gs[1])
        out[key] = out.get(key, 0) + tot_C
    return {k: v for k, v in out.items() if v}


def nshift(terms):
    tot = 0
    for (i, E, C, t1, t2) in terms:
        for t in (t1, t2):
            cn = canon(*t)
            if cn[0] != 0 and cn[4] != 0:
                tot += 1
    return tot


def search_II(name, A, Bq, C, d, e, de1, de2, targets, R=7):
    """search matrices B whose split has theta moduli `targets` (sorted pair), fewest quasi-shifts"""
    best = None
    for b in itertools.product(range(-R, R + 1), repeat=4):
        b11, b12, b21, b22 = b
        det = b11 * b22 - b12 * b21
        if det <= 0:
            continue
        if A * b11 * b12 + Bq * (b11 * b22 + b12 * b21) + C * b21 * b22 != 0:
            continue
        M1 = 2 * (A * b11 ** 2 + 2 * Bq * b11 * b21 + C * b21 ** 2)
        M2 = 2 * (A * b12 ** 2 + 2 * Bq * b12 * b22 + C * b22 ** 2)
        if (M1, M2) != tuple(targets):
            continue
        for r in [(1, 0), (0, 1)]:
            for lo in range(-det, 1):
                res = find_ecs(b, r, None, [lo])
                if not res:
                    continue
                out = typeII(A, Bq, C, d, e, de1, de2, b, r, None, [lo])
                nbar = sum(1 for (i, E, Cc, t1, t2) in out[2] for t in (t1, t2)
                           if t[2] == -1 and canon(*t1)[0] != 0 and canon(*t2)[0] != 0)
                ncan = len(canon_terms_local(out[2]))
                sc = (nbar, ncan, nshift(out[2]), sum(abs(x) for x in b))
                if best is None or sc < best[0]:
                    best = (sc, b, out)
    if best is None:
        print(f"== {name}: NONE for {targets}")
        return None
    print(f"   B={best[1]} shifts={best[0][0]}")
    show(name, best[2])
    return best


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "search":
    jobs = {
        "3.4": ((3, 1, 4, 1, 4, 1, 0), [(6, 66), (10, 110)]),
        "3.6": ((2, 1, 5, 1, 2, 1, 0), [(10, 90), (18, 18)]),
        "3.9": ((3, 1, 5, 1, 4, 1, 0), [(20, 70), (6, 84)]),
        "3.10": ((3, 1, 5, 3, 1, 0, 1), [(10, 140), (12, 42)]),
        "3.19": ((5, 1, 8, 1, 8, 1, 0), [(10, 390), (30, 130)]),
        "3.28": ((5, 1, 7, 1, 7, 1, 0), [(20, 170), (10, 340)]),
        "3.5": ((4, 2, 5, 2, -3, 1, 1), [(10, 160), (8, 32)]),
        "3.11": ((4, 2, 7, 2, 7, 1, 0), [(30, 80), (8, 48)]),
        "3.12": ((5, 1, 5, 1, 5, 1, 0), [(10, 240), (16, 24)]),
    }
    which = sys.argv[2:] or list(jobs)
    for tag in which:
        form, tg = jobs[tag]
        for t in tg:
            for tt in (t, (t[1], t[0])):
                r = search_II(f"{tag} {tt}", *form, tt)
                if r:
                    break
    sys.exit(0)

if __name__ == "__main__":
    show("3.2 ", typeI(1, 0, -1, 4, 2, 1, (1, 4, -1, 1)))
    show("3.7 ", typeI(1, 0, -1, 6, 3, 1, (2, 3, -1, 1)))
    show("3.8 ", typeI(2, 1, 1, 3, 0, -1, (1, 3, -1, 2)))
    # Type II (Cao)
    show("3.4 B1", typeII(3, 1, 4, 1, 4, 1, 0, (1, -1, 0, 3)))
    show("3.4 B2", typeII(3, 1, 4, 1, 4, 1, 0, (1, 3, -1, 2)))
    show("3.6 B1", typeII(2, 1, 5, 1, 2, 1, 0, (1, 1, -2, 1)))
    show("3.6 B2", typeII(2, 1, 5, 1, 2, 1, 0, (0, -5, 1, 1)))
    show("3.9 B1", typeII(3, 1, 5, 1, 4, 1, 0, (1, -1, 0, 3)))
    show("3.9 B2", typeII(3, 1, 5, 1, 4, 1, 0, (1, -3, 1, 2)))
    show("3.10 B1", typeII(3, 1, 5, 3, 1, 0, 1, (1, 2, -1, 1)))
    show("3.10 B2", typeII(3, 1, 5, 3, 1, 0, 1, (0, -5, 1, 1)))
    show("3.19 B1", typeII(5, 1, 8, 1, 8, 1, 0, (1, -1, 0, 5)))
    show("3.19 B2", typeII(5, 1, 8, 1, 8, 1, 0, (1, -3, 1, 2)))
    show("3.28 B1", typeII(5, 1, 7, 1, 7, 1, 0, (1, 3, -1, 2)))
    show("3.28 B2", typeII(5, 1, 7, 1, 7, 1, 0, (1, -1, 0, 5)))
    show("3.5 B1", typeII(4, 2, 5, 2, -3, 1, 1, (1, -1, 0, 2)))
    show("3.5 B2", typeII(4, 2, 5, 2, -3, 1, 1, (0, -5, 1, 2)))
    show("3.11 B1", typeII(4, 2, 7, 2, 7, 1, 0, (1, -1, 0, 2)))
    show("3.11 B2", typeII(4, 2, 7, 2, 7, 1, 0, (1, -3, 1, 2)))
    show("3.12 B1", typeII(5, 1, 5, 1, 5, 1, 0, (1, 1, -1, 1)))
    show("3.12 B2", typeII(5, 1, 5, 1, 5, 1, 0, (1, -1, 0, 5)))
