#!/usr/bin/env python3
"""Atomize products (q^b;q^a)_inf at a common modulus M and find the monomial ratio between two product
identities (used to choose `linear_combination` coefficients).  Expressions use P(b,a), J(e,N), X."""
import sys
import sympy as sp

def make_env(M):
    xs = {r: sp.Symbol(f"x{r}") for r in range(1, M + 1)}
    X = sp.Symbol("X")
    def P(b, a):
        assert M % a == 0, (b, a)
        r = sp.Integer(1)
        for j in range(M // a):
            r *= xs[(b + a * j - 1) % M + 1] if b + a * j <= M else xs[b + a * j] if False else xs[((b + a * j - 1) % M) + 1]
        return r
    def J(e, N):
        return P(e, N) * P(N - e, N) * P(N, N)
    return {"P": P, "J": J, "X": X, "sp": sp}

def ratio(M, goal_l, goal_r, h_l, h_r):
    env = make_env(M)
    g = sp.expand(eval(goal_l, env) - eval(goal_r, env))
    h = sp.expand(eval(h_l, env) - eval(h_r, env))
    return sp.factor(sp.cancel(g / h))

if __name__ == "__main__":
    M = int(sys.argv[1])
    print(ratio(M, *sys.argv[2:6]))


def lean_monomial(expr, M):
    """sympy monomial in x_r -> Lean product of `Pinf r M ^ k`, with sign"""
    expr = sp.factor(expr)
    c, terms = expr.as_coeff_mul()
    parts = []
    for t in terms:
        b, e = t.as_base_exp()
        r = int(str(b)[1:])
        parts.append(f"Pinf {r} {M}" + (f" ^ {e}" if e != 1 else ""))
    return str(c), " * ".join(parts)


def lam(M, goal_l, goal_r, h_l, h_r, pre=None):
    env = make_env(M)
    g = sp.expand(eval(goal_l, env) - eval(goal_r, env))
    if pre:
        g = sp.expand(g * eval(pre, env))
    h = sp.expand(eval(h_l, env) - eval(h_r, env))
    q = sp.cancel(g / h)
    num, den = sp.fraction(sp.factor(q))
    assert den == 1, f"not polynomial; denominator {den}"
    return lean_monomial(num, M)
