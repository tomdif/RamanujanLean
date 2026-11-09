#!/usr/bin/env python3
"""Numerical check of Ramanujan's forty identities for the Rogers-Ramanujan functions.

Statements follow Berndt, Choi, Choi, Hahn, Yeap, Yee, Yesilyurt, Yi, Mem. AMS 188 (2007), no. 880, Sec. 3.
G(q) = sum q^{n^2}/(q;q)_n,  H(q) = sum q^{n^2+n}/(q;q)_n are computed from the SUM sides (not the products),
so the check is independent of the Rogers-Ramanujan identities.  Identities with q^{1/2} are checked after
q -> q^2; identities with square roots are checked after squaring (with a sign/leading-term check).
All arithmetic is exact (Fraction) on truncated power series.

Usage: nice -n 10 python3 scripts/forty/verify_forty.py [ORDER]
"""
import sys
from fractions import Fraction

N = int(sys.argv[1]) if len(sys.argv) > 1 else 150


def mul(a, b):
    c = [0] * N
    for i, x in enumerate(a):
        if x:
            for j in range(N - i):
                if b[j]:
                    c[i + j] += x * b[j]
    return c


def add(*xs):
    return [sum(t) for t in zip(*xs)]


def neg(a):
    return [-x for x in a]


def scal(k, a):
    return [k * x for x in a]


def mono(e, c=1):
    a = [0] * N
    if e < N:
        a[e] = c
    return a


ONE = mono(0)


def inv(a):
    assert a[0] != 0
    b = [0] * N
    b[0] = Fraction(1) / a[0]
    for n in range(1, N):
        s = sum(a[k] * b[n - k] for k in range(1, n + 1))
        b[n] = -s / a[0]
    return b


def div(a, b):
    return mul(a, inv(b))


def sub_q(a, k, sign=1):
    """a(sign * q^k)"""
    b = [0] * N
    for i, x in enumerate(a):
        if i * k < N:
            b[i * k] = x * (sign ** i)
    return b


def pw(a, n):
    r = ONE
    for _ in range(n):
        r = mul(r, a)
    return r


def sqrt1(a):
    """formal square root of a series with a[0] = 1"""
    assert a[0] == 1
    b = [Fraction(0)] * N
    b[0] = Fraction(1)
    for n in range(1, N):
        s = sum(b[k] * b[n - k] for k in range(1, n))
        b[n] = (a[n] - s) / 2
    return b


# sum sides
def qpoch_fin(n):
    r = ONE
    for k in range(1, n + 1):
        r = mul(r, add(ONE, mono(k, -1)))
    return r


def rr_sum(shift):
    s = [0] * N
    n = 0
    while n * n + shift * n < N:
        s = add(s, mul(mono(n * n + shift * n), inv(qpoch_fin(n))))
        n += 1
    return s


G1 = rr_sum(0)
H1 = rr_sum(1)


def G(k, sign=1):
    return sub_q(G1, k, sign)


def H(k, sign=1):
    return sub_q(H1, k, sign)


def P(r, m, sign=1):
    """(sign q^r; q^m)_inf, sign=+1 means (q^r;q^m), sign=-1 means (-q^r;q^m)"""
    res = ONE
    j = r
    while j < N:
        res = mul(res, add(ONE, mono(j, -sign)))
        j += m
    return res


def f_neg(k):  # f(-q^k) = (q^k;q^k)
    return P(k, k)


def chi(k, sign=1):  # chi(sign q^k) = (-sign q^k; q^{2k})
    return P(k, 2 * k, -sign)


def phi(k, sign=1):  # phi(sign q^k)
    a = [0] * N
    n = 0
    while k * n * n < N:
        a[k * n * n] += (1 if n == 0 else 2) * (sign ** n)
        n += 1
    return a


def psi(k, sign=1):  # psi(sign q^k) = sum q^{k n(n+1)/2}
    a = [0] * N
    n = 0
    while k * n * (n + 1) // 2 < N:
        a[k * n * (n + 1) // 2] += sign ** (n * (n + 1) // 2)
        n += 1
    return a


def eq(a, b, name):
    ok = all(Fraction(x) == Fraction(y) for x, y in zip(a, b))
    print(f"{name:10s} {'OK' if ok else 'FAIL'}")
    if not ok:
        bad = [i for i in range(N) if Fraction(a[i]) != Fraction(b[i])][:5]
        print("   first diffs at", bad, [(a[i], b[i]) for i in bad])
    return ok


results = {}

# 3.1
results['3.1'] = eq(add(mul(pw(G(1), 11), H(1)), neg(mul(mono(2), mul(G(1), pw(H(1), 11))))),
                    add(ONE, scal(11, mul(mono(1), mul(pw(G(1), 6), pw(H(1), 6))))), '3.1')
# 3.2
results['3.2'] = eq(add(mul(G(1), G(4)), mul(mono(1), mul(H(1), H(4)))), mul(chi(1), chi(1)), '3.2')
results['3.2b'] = eq(mul(chi(1), chi(1)), div(phi(1), f_neg(2)), '3.2(phi)')
# 3.3
results['3.3'] = eq(add(mul(G(1), G(4)), neg(mul(mono(1), mul(H(1), H(4))))), div(phi(5), f_neg(2)), '3.3')
# 3.4
results['3.4'] = eq(add(mul(G(11), H(1)), neg(mul(mono(2), mul(G(1), H(11))))), ONE, '3.4')
# 3.5
results['3.5'] = eq(add(mul(G(16), H(1)), neg(mul(mono(3), mul(G(1), H(16))))), chi(2), '3.5')
# 3.6
results['3.6'] = eq(add(mul(G(1), G(9)), mul(mono(2), mul(H(1), H(9)))),
                    div(mul(f_neg(3), f_neg(3)), mul(f_neg(1), f_neg(9))), '3.6')
# 3.7
results['3.7'] = eq(add(mul(G(2), G(3)), mul(mono(1), mul(H(2), H(3)))), div(chi(3, -1), chi(1, -1)), '3.7')
# 3.8
results['3.8'] = eq(add(mul(G(6), H(1)), neg(mul(mono(1), mul(G(1), H(6))))), div(chi(1, -1), chi(3, -1)), '3.8')
# 3.9
results['3.9'] = eq(add(mul(G(7), H(2)), neg(mul(mono(1), mul(G(2), H(7))))), div(chi(1, -1), chi(7, -1)), '3.9')
# 3.10
results['3.10'] = eq(add(mul(G(1), G(14)), mul(mono(3), mul(H(1), H(14)))), div(chi(7, -1), chi(1, -1)), '3.10')
# 3.11
results['3.11'] = eq(add(mul(G(8), H(3)), neg(mul(mono(1), mul(G(3), H(8))))),
                     div(mul(chi(1, -1), chi(4, -1)), mul(chi(3, -1), chi(12, -1))), '3.11')
# 3.12
results['3.12'] = eq(add(mul(G(1), G(24)), mul(mono(5), mul(H(1), H(24)))),
                     div(mul(chi(3, -1), chi(12, -1)), mul(chi(1, -1), chi(4, -1))), '3.12')
# 3.13
results['3.13'] = eq(add(mul(G(9), H(4)), neg(mul(mono(1), mul(G(4), H(9))))),
                     div(mul(chi(1, -1), chi(6, -1)), mul(chi(3, -1), chi(18, -1))), '3.13')
# 3.14
results['3.14'] = eq(add(mul(G(36), H(1)), neg(mul(mono(7), mul(G(1), H(36))))),
                     div(mul(chi(6, -1), chi(9, -1)), mul(chi(2, -1), chi(3, -1))), '3.14')
# 3.15 (q -> q^2): LHS1(q^2) = LHS2(q^2) = 1/(2q) [chi(q)chi(-q^3)chi(q^7)chi(-q^21) - chi(-q)chi(q^3)chi(-q^7)chi(q^21)]
L1 = add(mul(G(6), G(14)), mul(mono(4), mul(H(6), H(14))))
L2 = add(mul(G(42), H(2)), neg(mul(mono(8), mul(G(2), H(42)))))
results['3.15a'] = eq(L1, L2, '3.15(i)')
R = add(mul(mul(chi(1), chi(3, -1)), mul(chi(7), chi(21, -1))), neg(mul(mul(chi(1, -1), chi(3)), mul(chi(7, -1), chi(21)))))
results['3.15b'] = eq(scal(2, mul(mono(1), L1)), R, '3.15(ii)')
# 3.16: LHS1 = LHS2 = sqrt(chi(-q^13)/chi(-q) - q chi(-q)/chi(-q^13))  (one square root over both terms)
L1 = add(mul(G(2), G(13)), mul(mono(3), mul(H(2), H(13))))
L2 = add(mul(G(26), H(1)), neg(mul(mono(5), mul(G(1), H(26)))))
results['3.16a'] = eq(L1, L2, '3.16(i)')
x = div(chi(13, -1), chi(1, -1))
results['3.16b'] = eq(L1, sqrt1(add(x, neg(mul(mono(1), inv(x))))), '3.16(ii)')
# 3.17 (q -> q^2): 4q*LHS(q^2) = chi^2(q)chi^2(q^19) - chi^2(-q)chi^2(-q^19) - 4q^5/(chi^2(-q^2)chi^2(-q^38))
L = add(mul(G(2), G(38)), mul(mono(8), mul(H(2), H(38))))
R = add(mul(pw(chi(1), 2), pw(chi(19), 2)), neg(mul(pw(chi(1, -1), 2), pw(chi(19, -1), 2))),
        neg(scal(4, div(mono(5), mul(pw(chi(2, -1), 2), pw(chi(38, -1), 2))))))
results['3.17'] = eq(scal(4, mul(mono(1), L)), R, '3.17')
# 3.18: 2q LHS = chi(q)chi(q^31) - chi(-q)chi(-q^31) + 2q^4/(chi(-q^2)chi(-q^62))
L = add(mul(G(31), H(1)), neg(mul(mono(6), mul(G(1), H(31)))))
R = add(mul(chi(1), chi(31)), neg(mul(chi(1, -1), chi(31, -1))), scal(2, div(mono(4), mul(chi(2, -1), chi(62, -1)))))
results['3.18'] = eq(scal(2, mul(mono(1), L)), R, '3.18')
# 3.19
A = mul(add(mul(G(1), G(39)), mul(mono(8), mul(H(1), H(39)))), mul(f_neg(1), f_neg(39)))
B = mul(add(mul(G(13), H(3)), neg(mul(mono(2), mul(G(3), H(13))))), mul(f_neg(3), f_neg(13)))
results['3.19a'] = eq(A, B, '3.19(i)')
results['3.19b'] = eq(scal(2, mul(mono(1), A)), add(mul(phi(3, -1), phi(13, -1)), neg(mul(phi(1, -1), phi(39, -1)))), '3.19(ii)')
# 3.20
results['3.20'] = eq(add(mul(G(1), H(1, -1)), mul(G(1, -1), H(1))), scal(2, inv(pw(chi(2, -1), 2))), '3.20')
results['3.20b'] = eq(scal(2, inv(pw(chi(2, -1), 2))), scal(2, div(psi(2), f_neg(2))), '3.20(psi)')
# 3.21
results['3.21'] = eq(add(mul(G(1), H(1, -1)), neg(mul(G(1, -1), H(1)))), scal(2, div(mul(mono(1), psi(10)), f_neg(2))), '3.21')
# 3.22
results['3.22'] = eq(add(mul(G(1, -1), G(4, -1)), mul(mono(1), mul(H(1, -1), H(4, -1)))), chi(2), '3.22')
# 3.23
results['3.23'] = eq(add(mul(G(2, -1), G(3, -1)), mul(mono(1), mul(H(2, -1), H(3, -1)))),
                     div(mul(chi(1), chi(6)), mul(chi(2), chi(3))), '3.23')
# 3.24
results['3.24'] = eq(add(mul(G(6, -1), H(1, -1)), neg(mul(mono(1), mul(H(6, -1), G(1, -1))))),
                     div(mul(chi(2), chi(3)), mul(chi(1), chi(6))), '3.24')
# 3.25
results['3.25'] = eq(add(mul(G(1, -1), G(9)), neg(mul(mono(2), mul(H(1, -1), H(9))))),
                     div(mul(chi(1, -1), chi(9)), chi(6, -1)), '3.25')
# 3.26
R = add(div(mul(chi(2), chi(22)), mul(chi(2, -1), chi(22, -1))),
        neg(scal(2, div(mono(3), mul(mul(chi(2, -1), chi(4, -1)), mul(chi(22, -1), chi(44, -1)))))))
results['3.26'] = eq(add(mul(G(11), H(1, -1)), mul(mono(2), mul(G(1, -1), H(11)))), R, '3.26')
# 3.27
U = add(mul(G(1), G(44)), mul(mono(9), mul(H(1), H(44))))
V = add(mul(G(4), G(11)), mul(mono(3), mul(H(4), H(11))))
results['3.27a'] = eq(add(mul(U, U), mul(mono(1), mul(V, V))), mul(pw(chi(1), 3), pw(chi(11), 3)), '3.27(i)')
results['3.27b'] = eq(add(mul(U, V), mono(1)), mul(pw(chi(1), 2), pw(chi(11), 2)), '3.27(ii)')
# 3.28
U = add(mul(G(17), H(2)), neg(mul(mono(3), mul(G(2), H(17)))))
V = add(mul(G(1), G(34)), mul(mono(7), mul(H(1), H(34))))
results['3.28a'] = eq(mul(U, chi(17, -1)), mul(V, chi(1, -1)), '3.28(i)')
c = div(pw(chi(17, -1), 3), pw(chi(1, -1), 3))
lhs = add(mul(pw(U, 4), pw(V, 4)), neg(mul(mono(1), mul(pw(U, 2), pw(V, 2)))))
rhs = mul(c, pw(add(ONE, mul(mono(2), inv(c))), 2))
results['3.28b'] = eq(lhs, rhs, '3.28(ii)')
# 3.29
A = add(mul(G(2), G(23)), mul(mono(5), mul(H(2), H(23))))
B = add(mul(G(46), H(1)), neg(mul(mono(9), mul(G(1), H(46)))))
x = mul(chi(1, -1), chi(23, -1))
results['3.29'] = eq(mul(A, B), add(x, mono(1), scal(2, div(mono(2), x))), '3.29')
# 3.30
A = add(mul(G(19), H(4)), neg(mul(mono(3), mul(G(4), H(19)))))
B = add(mul(G(76), H(1, -1)), mul(mono(15), mul(G(1, -1), H(76))))
results['3.30'] = eq(mul(A, chi(38, -1)), mul(B, chi(2, -1)), '3.30')
# 3.31
A = add(mul(G(2), G(33)), mul(mono(7), mul(H(2), H(33))))
B = add(mul(G(66), H(1)), neg(mul(mono(13), mul(H(66), G(1)))))
results['3.31'] = eq(mul(A, chi(11, -1)), mul(B, chi(3, -1)), '3.31')
# 3.32
A = add(mul(G(3), G(22)), mul(mono(5), mul(H(3), H(22))))
B = add(mul(G(11), H(6)), neg(mul(mono(1), mul(G(6), H(11)))))
results['3.32'] = eq(mul(A, chi(1, -1)), mul(B, chi(33, -1)), '3.32')
# 3.33
A = add(mul(G(1), G(54)), mul(mono(11), mul(H(1), H(54))))
B = add(mul(G(27), H(2)), neg(mul(mono(5), mul(G(2), H(27)))))
results['3.33'] = eq(mul(A, mul(chi(1, -1), chi(9, -1))), mul(B, mul(chi(3, -1), chi(27, -1))), '3.33')
# 3.34
A = add(mul(G(1), G(19, -1)), neg(mul(mono(4), mul(H(1), H(19, -1)))))
B = add(mul(G(1, -1), G(19)), neg(mul(mono(4), mul(H(1, -1), H(19)))))
results['3.34'] = eq(mul(A, B), add(mul(G(2), G(38)), mul(mono(8), mul(H(2), H(38)))), '3.34')
# 3.35: (AB - x - 2q^2 - 2q^4/x)^2 = q^2 (4x + 9q^2 + 8q^4/x),  x = chi(-q)chi(-q^47); sign: D = +2q + ...
A = add(mul(G(1), G(94)), mul(mono(19), mul(H(1), H(94))))
B = add(mul(G(47), H(2)), neg(mul(mono(9), mul(G(2), H(47)))))
x = mul(chi(1, -1), chi(47, -1))
D = add(mul(A, B), neg(x), mono(2, -2), neg(scal(2, div(mono(4), x))))
results['3.35'] = eq(mul(D, D), mul(mono(2), add(scal(4, x), mono(2, 9), scal(8, div(mono(4), x)))), '3.35(sq)')
print('3.35 sign: D leading coeffs', D[:3], '(expect 0, 2, ...)')
print("all ok:", all(results.values()), f"(order {N})")
