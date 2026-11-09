#!/usr/bin/env python3
"""Find a target theta-product identity as a linear combination of ECS relations ("Type III" search).

For binary forms Q of a given determinant, linear terms (d,e), and sign characters δ, every exact cover with given
theta moduli expands S_{Q,d,e,δ} = Σ (−1)^{δ·x} t^{Q(x)+dx1+ex2}. Two expansions of the same S give a relation.
We collect the relations whose theta factors lie in an allowed set and solve target = Σ c_k (relation_k) over ℚ.
"""
import itertools
import io
import contextlib
import sys
from fractions import Fraction
import ecs


def canon_dict(terms):
    return ecs.canon_terms_local(terms)


def expansions(form, de, targets, R=6, lin=range(-6, 7), dets=None):
    A, Bq, C = form
    mats = []
    for b in itertools.product(range(-R, R + 1), repeat=4):
        b11, b12, b21, b22 = b
        det = b11 * b22 - b12 * b21
        if det <= 0 or (dets and det not in dets):
            continue
        if A * b11 * b12 + Bq * (b11 * b22 + b12 * b21) + C * b21 * b22 != 0:
            continue
        M1 = 2 * (A * b11 ** 2 + 2 * Bq * b11 * b21 + C * b21 ** 2)
        M2 = 2 * (A * b12 ** 2 + 2 * Bq * b12 * b22 + C * b22 ** 2)
        if (M1, M2) not in targets:
            continue
        for r in [(1, 0), (0, 1)]:
            for lo in range(-det, 1):
                if ecs.find_ecs(b, r, None, [lo]):
                    mats.append((b, r, lo))
                    break
            else:
                continue
            break
    out = {}
    for d, e in itertools.product(lin, repeat=2):
        for dd in de:
            exps = []
            for (b, r, lo) in mats:
                with contextlib.redirect_stdout(io.StringIO()):
                    res = ecs.typeII(A, Bq, C, d, e, dd[0], dd[1], b, r, None, [lo])
                exps.append(((b, r, lo), canon_dict(res[2])))
            out[(d, e, dd)] = exps
    return out


def solve(target, rels):
    """target: dict key->coef ; rels: list of dicts. Solve target = Σ c_k rels_k (exact)."""
    keys = sorted(set(target) | set(k for r in rels for k in r))
    n = len(rels)
    rows = [[Fraction(r.get(k, 0)) for r in rels] + [Fraction(target.get(k, 0))] for k in keys]
    # gaussian elimination
    m = len(rows)
    piv = []
    row = 0
    for col in range(n):
        p = next((i for i in range(row, m) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[row], rows[p] = rows[p], rows[row]
        pv = rows[row][col]
        rows[row] = [x / pv for x in rows[row]]
        for i in range(m):
            if i != row and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[row])]
        piv.append(col)
        row += 1
    for i in range(row, m):
        if rows[i][n] != 0:
            return None
    sol = [Fraction(0)] * n
    for i, col in enumerate(piv):
        sol[col] = rows[i][n]
    return sol
