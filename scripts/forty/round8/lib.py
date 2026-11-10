"""numpy power-series helpers for round 8 searches (truncated at lib.P)."""
import numpy as np
P = 300
def z(): return np.zeros(P, dtype=np.int64)
def mono(e, c=1):
    a = z()
    if 0 <= e < P: a[e] = c
    return a
def mul(a, b): return np.convolve(a, b)[:P]
def add(*xs): return sum(xs[1:], xs[0].copy())
def sub(a, b): return a - b
def sc(c, a): return c*a
def sh(k, a):
    o = z()
    if k >= 0: o[k:] = a[:P-k]
    else: o[:P+k] = a[-k:]
    return o
def inv(a):
    assert a[0] in (1, -1)
    b = z(); b[0] = a[0]
    for n in range(1, P):
        b[n] = -a[0]*np.dot(a[1:n+1], b[n-1::-1])
    return b
def pw(a, n):
    r = mono(0)
    for _ in range(n): r = mul(r, a)
    return r
def subq(a, k, sign=1):
    b = z()
    for i in range(0, (P-1)//k+1):
        b[i*k] = a[i]*(sign**i)
    return b
def f(a, b):
    (s1, e1), (s2, e2) = a, b
    o = z()
    for n in range(-300, 301):
        E = e1*n*(n+1)//2 + e2*n*(n-1)//2
        if 0 <= E < P:
            o[E] += (s1**((n*(n+1)//2) % 2))*(s2**((n*(n-1)//2) % 2))
    return o
def fm(k): return f((-1, k), (-1, 2*k))
def poch(r, m, sign=1):
    res = mono(0); j = r
    while j < P:
        res[j:] = res[j:] - sign*res[:P-j].copy() if False else res[j:] - sign*res[:P-j]
        j += m
    return res
def chi(k, sign=1): return poch(k, 2*k, -sign)
def phi(k, sign=1): return f((sign, k), (sign, k))
def psi(k, sign=1): return f((sign, k), (sign, 3*k))
def G(k=1, sign=1): return subq(inv(mul(poch(1, 5), poch(4, 5))), k, sign)
def H(k=1, sign=1): return subq(inv(mul(poch(2, 5), poch(3, 5))), k, sign)
def eq(a, b, n=None): return bool(np.array_equal(a[:n or P], b[:n or P]))
def exps(a, upto=None):
    """a = prod (1-q^n)^{c_n}"""
    assert a[0] == 1
    upto = upto or P
    c = {}; cur = a.copy()
    for n in range(1, upto):
        cn = -int(cur[n])
        if cn:
            c[n] = cn
            # cur *= (1-q^n)^{-cn}
            if abs(cn) > 50: c['BAD']=n; return c
            for _ in range(abs(cn)):
                if cn > 0:  # divide by (1-q^n): prefix sums with step n
                    for j in range(n, P): cur[j] += cur[j-n]
                else:
                    cur[n:] = cur[n:] - cur[:P-n]
    return c
