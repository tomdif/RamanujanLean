"""Numerical check of Ramanujan's septic theta identity (Lost Notebook Entry 1.1(i)),
in the q -> q^7 form:  phi(q)/phi(q^49) = 1 + u + v + w, with (Rebak 2023, eq. (11))
  u = 2 q   f(q^35, q^63)/phi(q^49),
  v = 2 q^4 f(q^21, q^77)/phi(q^49),
  w = 2 q^9 f(q^7,  q^91)/phi(q^49),
where f(a,b) = sum_{n in Z} a^{n(n+1)/2} b^{n(n-1)/2} and phi(q) = f(q,q).
Checks (a) the exact power-series identity to order M, (b) the exponent identities
1+35n(n+1)/2+63n(n-1)/2 = (7n-1)^2 etc., (c) the Jacobi-triple-product form of f,
(d) the real-variable identity at q^{1/7} with mpmath, and Rebak's ordering 2>u>v>w>0."""
import mpmath as mp

M = 4000

def f_series(a, b, M):
    c = [0] * (M + 1)
    n = 0
    while True:
        hit = False
        for m in ({n, -n} if n else {0}):
            e = a * m * (m + 1) // 2 + b * m * (m - 1) // 2
            if e <= M:
                c[e] += 1; hit = True
        if not hit and n > 0:
            break
        n += 1
    return c

def shift(c, j):
    return [0] * j + c[: len(c) - j]

phi = f_series(1, 1, M)
lhs = phi
rhs = [x + 2 * y + 2 * z + 2 * t for x, y, z, t in zip(
    f_series(49, 49, M), shift(f_series(35, 63, M), 1),
    shift(f_series(21, 77, M), 4), shift(f_series(7, 91, M), 9))]
assert lhs == rhs, "dissection fails"
print(f"(a) phi(q) = phi(q^49)+2q f(q^35,q^63)+2q^4 f(q^21,q^77)+2q^9 f(q^7,q^91)  OK to q^{M}")

for n in range(-50, 51):
    assert 2 + 35 * n * (n + 1) + 63 * n * (n - 1) == 2 * (7 * n - 1) ** 2
    assert 8 + 21 * n * (n + 1) + 77 * n * (n - 1) == 2 * (7 * n - 2) ** 2
    assert 18 + 7 * n * (n + 1) + 91 * n * (n - 1) == 2 * (7 * n - 3) ** 2
print("(b) exponent identities OK")

# (c) JTP: f(a,b) = (-a;ab)(-b;ab)(ab;ab) as power series, a=q^A, b=q^B
def jtp(A, B, M):
    p = [0] * (M + 1); p[0] = 1
    def mulbin(p, e, s):  # multiply by (1 + s q^e)
        if e > M: return p
        r = p[:]
        for i in range(M - e, -1, -1):
            r[i + e] += s * p[i]
        return r
    k = 0
    while A + k * (A + B) <= M or B + k * (A + B) <= M or (k + 1) * (A + B) <= M:
        p = mulbin(p, A + k * (A + B), 1)
        p = mulbin(p, B + k * (A + B), 1)
        p = mulbin(p, (k + 1) * (A + B), -1)
        k += 1
    return p
for A, B in [(1, 1), (35, 63), (21, 77), (7, 91), (49, 49)]:
    assert jtp(A, B, 1500) == f_series(A, B, 1500)
print("(c) JTP product forms of f(q^35,q^63), f(q^21,q^77), f(q^7,q^91), phi OK to q^1500")

# (d) real values at Q = q^{1/7}
mp.mp.dps = 40
def fR(a, b):
    return mp.nsum(lambda n: a ** (n * (n + 1) / 2) * b ** (n * (n - 1) / 2), [-mp.inf, mp.inf])
def phiR(q): return fR(q, q)
for q in [mp.mpf('0.1'), mp.mpf('0.5'), mp.mpf('0.9'), mp.exp(-mp.pi / mp.sqrt(7))]:
    Q = q ** (mp.mpf(1) / 7)
    d = phiR(q ** 7)
    u = 2 * Q * fR(q ** 5, q ** 9) / d
    v = 2 * Q ** 4 * fR(q ** 3, q ** 11) / d
    w = 2 * Q ** 9 * fR(q, q ** 13) / d
    err = phiR(Q) / d - (1 + u + v + w)
    assert abs(err) < mp.mpf(10) ** -30
    assert 2 > u > v > w > 0
    print(f"(d) q={mp.nstr(q,8)}: u={mp.nstr(u,12)} v={mp.nstr(v,12)} w={mp.nstr(w,12)} p=uvw={mp.nstr(u*v*w,12)} err={mp.nstr(err,3)}")
