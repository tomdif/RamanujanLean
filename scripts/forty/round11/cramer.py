#!/usr/bin/env python3
"""Round 11: Cramer elimination for L(q^2), L = G(q^3)G(q^7)+q^2 H(q^3)H(q^7).
Entries 3.8, 3.7(q^2) solve G(q^6),H(q^6); 3.10, 3.9(q^2) solve G(q^14),H(q^14); det = q chi^2(q) (Entry 3.2).
Claim: chi^2(q) L(q^2) = b c + q a d,  a=chi(-q)/chi(-q^3), b=chi(-q^6)/chi(-q^2), c=chi(-q^7)/chi(-q), d=chi(-q^2)/chi(-q^14).
"""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300

def mul(a, b):
    c = [0]*N
    for i, x in enumerate(a):
        if x:
            for j in range(N-i):
                if b[j]: c[i+j] += x*b[j]
    return c
def inv(a):
    assert a[0] == 1
    b = [0]*N; b[0] = 1
    for n in range(1, N):
        b[n] = -sum(a[k]*b[n-k] for k in range(1, n+1))
    return b
def S(k, a):
    c = [0]*N
    for i, x in enumerate(a):
        if i*k < N: c[i*k] = x
    return c
def Ng(a): return [x if i % 2 == 0 else -x for i, x in enumerate(a)]
def sh(e, a): return [0]*e + a[:N-e]
def add(*xs): return [sum(t) for t in zip(*xs)]
def sc(k, a): return [k*x for x in a]

def G():
    # sum q^{n^2}/(q;q)_n
    g = [0]*N; n = 0
    while n*n < N:
        t = [0]*N; t[n*n] = 1
        for k in range(1, n+1):
            # divide by (1-q^k)
            for i in range(k, N): t[i] += t[i-k]
        g = add(g, t); n += 1
    return g
def H():
    g = [0]*N; n = 0
    while n*n+n < N:
        t = [0]*N; t[n*n+n] = 1
        for k in range(1, n+1):
            for i in range(k, N): t[i] += t[i-k]
        g = add(g, t); n += 1
    return g
def chim(a):  # chi(-q^a) = prod (1-q^{a(2k+1)})
    p = [0]*N; p[0] = 1
    k = 0
    while a*(2*k+1) < N:
        e = a*(2*k+1)
        for i in range(N-1, e-1, -1): p[i] -= p[i-e]
        k += 1
    return p
def chip(a): return Ng(chim(a)) if a % 2 else None

g, h = G(), H()
def L(k):  # L(q^k)
    return add(mul(S(3*k, g), S(7*k, g)), sh(2*k, mul(S(3*k, h), S(7*k, h))))
chi1 = Ng(chim(1))
a = mul(chim(1), inv(chim(3))); b = mul(chim(6), inv(chim(2)))
c = mul(chim(7), inv(chim(1))); d = mul(chim(2), inv(chim(14)))
lhs = mul(mul(chi1, chi1), L(2))
rhs = add(mul(b, c), sh(1, mul(a, d)))
print("chi^2 L(q^2) == bc + q ad :", lhs == rhs)
# Entry 3.15(ii): Odd[A](q) = q L(q^2), A = chi(q)chi(-q^3)chi(q^7)chi(-q^21)
A = mul(mul(Ng(chim(1)), chim(3)), mul(Ng(chim(7)), chim(21)))
odd = [x if i % 2 else 0 for i, x in enumerate(A)]
print("Odd[A] == q L(q^2):", odd == sh(1, L(2)))
