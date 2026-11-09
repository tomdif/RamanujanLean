"""Exact integer power-series checks (to q^N) for the septic chain, variable q = Rebak's q^{1/7}.
a = phi(q^49) = sum_{k=0 mod 7} q^{k^2}, b,c,d = sum_{k = 1,2,3 mod 7} q^{k^2}, Phi = phi(q^7).
 (A)   Phi^4 = a^4 + 24abcd + 8(b^3c + c^3d + d^3b)              [PROVED in Lean: quaternion_identity]
 (B)   a(b^2c^3 + c^2d^3 + d^2b^3) = a^3bcd + 2(bcd)^2            [SonSextic, gap]
 (iii) a Phi^8 + (a^3-8bcd)^3 = (2a^5 + 40a^2 bcd) Phi^4           [SonEntryIII, gap]
With u=2b/a, v=2c/a, w=2d/a, p=uvw, R=Phi^4/a^4: (A) <=> u^3v+v^3w+w^3u = 2R-6p-2, (B) <=> u^2v^3+v^2w^3+w^2u^3 = p^2+4p,
so u^3v, v^3w, w^3u are the roots of r(xi) = xi^3 + 2(1+3p-R)xi^2 + p^2(p+4)xi - p^4 (Entry 1.1(iv)/(v)).
Also checks the six sextic relations (the ideal of relations among a,b,c,d starts in degree 6) and that
(iii) lies in their ideal (sympy Groebner)."""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
def cls(r, scale=1):
    s = [0] * N
    n = -N
    while n <= N:
        e = scale * (7 * n + r) ** 2
        if e < N: s[e] += 1
        n += 1
    return s
def mul(A, B):
    C = [0] * N
    nzA = [(i, x) for i, x in enumerate(A) if x]
    nzB = [(j, y) for j, y in enumerate(B) if y]
    for i, x in nzA:
        for j, y in nzB:
            if i + j >= N: break
            C[i + j] += x * y
    return C
def add(*S): return [sum(t) for t in zip(*S)]
def sc(k, A): return [k * x for x in A]
def pw(A, k):
    R = [1] + [0] * (N - 1)
    for _ in range(k): R = mul(R, A)
    return R
a, b, c, d = cls(0), cls(1), cls(2), cls(3)
Phi = [0] * N
for n in range(-N, N + 1):
    if 7 * n * n < N: Phi[7 * n * n] += 1
phi = [0] * N
for n in range(-N, N + 1):
    if n * n < N: phi[n * n] += 1
assert phi == add(a, sc(2, b), sc(2, c), sc(2, d)), "dissection"
abcd = mul(mul(a, b), mul(c, d)); bcd = mul(b, mul(c, d))
P4 = pw(Phi, 4)
A_rhs = add(pw(a, 4), sc(24, abcd), sc(8, add(mul(pw(b, 3), c), mul(pw(c, 3), d), mul(pw(d, 3), b))))
assert P4 == A_rhs, "(A)"
B_l = mul(a, add(mul(pw(b, 2), pw(c, 3)), mul(pw(c, 2), pw(d, 3)), mul(pw(d, 2), pw(b, 3))))
B_r = add(mul(pw(a, 3), bcd), sc(2, pw(bcd, 2)))
assert B_l == B_r, "(B)"
m = add(pw(a, 3), sc(-8, bcd))
I_l = add(mul(a, pw(P4, 2)), pw(m, 3))
I_r = mul(add(sc(2, pw(a, 5)), sc(40, mul(pw(a, 2), bcd))), P4)
assert I_l == I_r, "(iii)"
print(f"dissection, (A), (B), (iii) hold exactly to q^{N}")
try:
    import sympy as sp
    A, B, C, D = sp.symbols('a b c d')
    rels = [A**2*C*D**3 - A*B**2*C*D**2 - A*B*C**4 + B**4*C*D - B**2*D**4 + B*C**3*D**2,
            A**2*B*C**3 - A*B**4*D - A*B*C**2*D**2 + B**3*C**2*D + B*C*D**4 - C**4*D**2,
            A**2*B**3*D - A*B**2*C**2*D - A*C*D**4 - B**4*C**2 + B**2*C*D**3 + B*C**4*D,
            A**3*C*D**2 - A**2*B**2*C*D - A*B**2*D**3 + B**3*C**3 + B*C**2*D**3 - C**5*D,
            A**3*B*C*D - A*B**3*D**2 - A*B**2*C**3 - A*C**2*D**3 + 2*B**2*C**2*D**2,
            A**3*B*C**2 - A**2*B*C*D**2 - A*C**3*D**2 - B**5*C + B**3*D**3 + B**2*C**3*D]
    ser = {A: a, B: b, C: c, D: d}
    for R in rels:
        tot = [0] * N
        for mon, co in sp.Poly(R, A, B, C, D).terms():
            t = [1] + [0] * (N - 1)
            for v, e in zip((a, b, c, d), mon): t = mul(t, pw(v, e))
            tot = add(tot, sc(int(co), t))
        assert all(x == 0 for x in tot)
    Phi4 = A**4 + 24*A*B*C*D + 8*(B**3*C + C**3*D + D**3*B)
    iii = sp.expand(A*Phi4**2 + (A**3 - 8*B*C*D)**3 - (2*A**5 + 40*A**2*B*C*D)*Phi4)
    print("six sextic relations hold; (iii) with (A) substituted is in their ideal:",
          sp.groebner(rels, A, B, C, D, order='grevlex').contains(iii))
except ImportError:
    pass
