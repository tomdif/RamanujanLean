"""Numerics for the page-206 evaluation (Rebak 2023, Theorem 4.1) and Entry 1.1(ii)-(v).
phi(e^{-7 pi sqrt7}) = 7^{-3/4} phi(e^{-pi sqrt7}) {1 + A + B + C},
A=(cos(pi/7)/(2cos^2(2pi/7)))^{2/7}, B=(cos(2pi/7)/(2cos^2(3pi/7)))^{2/7}, C=(cos(3pi/7)/(2cos^2(pi/7)))^{2/7}."""
import mpmath as mp
mp.mp.dps = 60
pi = mp.pi
def fR(a, b):
    return mp.nsum(lambda n: a ** (n * (n + 1) / 2) * b ** (n * (n - 1) / 2), [-mp.inf, mp.inf])
def phiR(q): return fR(q, q)
c = lambda k: mp.cos(k * pi / 7)
A = (c(1) / (2 * c(2) ** 2)) ** (mp.mpf(2) / 7)
B = (c(2) / (2 * c(3) ** 2)) ** (mp.mpf(2) / 7)
C = (c(3) / (2 * c(1) ** 2)) ** (mp.mpf(2) / 7)
lhs = phiR(mp.exp(-7 * pi * mp.sqrt(7)))
rhs = 7 ** (mp.mpf(-3) / 4) * phiR(mp.exp(-pi * mp.sqrt(7))) * (1 + A + B + C)
print("(note: phi(e^{-7pi sqrt7}) = 1 + 2e^{-7pi sqrt7}+..., so the check below is only meaningful past 1e-25; the u,v,w check is the sharp one)")
print("Theorem 4.1: lhs =", mp.nstr(lhs, 50)); print("             rhs =", mp.nstr(rhs, 50))
assert abs(lhs - rhs) < mp.mpf(10) ** -50
# Ramanujan's printed 7^{+3/4} is wrong:
print("with 7^{+3/4}: ratio", mp.nstr(lhs / (7 ** (mp.mpf(3) / 4) * phiR(mp.exp(-pi * mp.sqrt(7))) * (1 + A + B + C)), 10))

# Entry 1.1 at q = e^{-pi/sqrt7}: u,v,w from eq.(11) equal B,A,C (u>v>w; Theorem 4.1 lists the terms in a different order)
q = mp.exp(-pi / mp.sqrt(7)); Q = q ** (mp.mpf(1) / 7); d = phiR(q ** 7)
u = 2 * Q * fR(q ** 5, q ** 9) / d; v = 2 * Q ** 4 * fR(q ** 3, q ** 11) / d; w = 2 * Q ** 9 * fR(q, q ** 13) / d
print("u-B, v-A, w-C:", mp.nstr(u - B, 5), mp.nstr(v - A, 5), mp.nstr(w - C, 5))
assert max(abs(u - B), abs(v - A), abs(w - C)) < mp.mpf(10) ** -50
p = u * v * w
print("p = uvw =", mp.nstr(p, 30), " phi^4(q)/phi^4(q^7) =", mp.nstr(phiR(q) ** 4 / d ** 4, 30))

# (ii)-(v) at generic q
def poch(a, qq, N=4000):
    return mp.fprod(1 + a * qq ** k for k in range(N))  # (-a;qq)_inf
for q in [mp.mpf('0.2'), mp.mpf('0.6')]:
    Q = q ** (mp.mpf(1) / 7); d = phiR(q ** 7)
    u = 2 * Q * fR(q ** 5, q ** 9) / d; v = 2 * Q ** 4 * fR(q ** 3, q ** 11) / d; w = 2 * Q ** 9 * fR(q, q ** 13) / d
    p = u * v * w
    pii = 8 * q ** 2 * poch(q, q ** 2) / poch(q ** 7, q ** 14) ** 7
    R = phiR(q) ** 4 / d ** 4
    iii = R ** 2 - (2 + 5 * p) * R + (1 - p) ** 3
    roots = mp.polyroots([1, 2 * (1 + 3 * p - R), p ** 2 * (p + 4), -p ** 4], maxsteps=200, extraprec=200)
    # identify alpha,beta,gamma from (iv): u^7 = alpha^2 p / beta etc.
    import itertools
    best = min(itertools.permutations(roots), key=lambda t: abs(u ** 7 - t[0] ** 2 * p / t[1]) + abs(v ** 7 - t[1] ** 2 * p / t[2]) + abs(w ** 7 - t[2] ** 2 * p / t[0]))
    a, b, g = best
    res = abs(u ** 7 - a ** 2 * p / b) + abs(v ** 7 - b ** 2 * p / g) + abs(w ** 7 - g ** 2 * p / a)
    print(f"q={q}: (ii) err {mp.nstr(p - pii, 3)}  (iii) {mp.nstr(iii, 3)}  (iv)/(v) residual {mp.nstr(res, 3)}")
    assert abs(p - pii) < 1e-40 and abs(iii) < 1e-40 and res < 1e-30
