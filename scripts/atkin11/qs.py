"""Minimal truncated q-series toolkit (python-flint fmpz_poly / fmpq_poly), for Atkin 11^k checks.
A series is (poly, val): value = q^val * poly(q), truncated to absolute order < N (global PREC)."""
from flint import fmpz_poly, fmpq_poly, fmpz, fmpq
from fractions import Fraction

class S:
    """Laurent series q^v * P(q), known modulo q^N (absolute)."""
    __slots__ = ("p", "v", "N")
    def __init__(self, p, v, N):
        self.p = p if isinstance(p, fmpq_poly) else fmpq_poly(p)
        self.v, self.N = v, N
        self._trunc()
    def _trunc(self):
        L = self.N - self.v
        if L <= 0: self.p = fmpq_poly([]); return
        if self.p.degree() >= L:
            c = self.p.coeffs()[:L]; self.p = fmpq_poly(c)
    def coeff(self, n):
        k = n - self.v
        if n >= self.N: raise ValueError("beyond precision")
        if k < 0 or k > self.p.degree(): return fmpq(0)
        return self.p[k]
    def __add__(s, o):
        if not isinstance(o, S): o = const(o, s.N)
        v = min(s.v, o.v); N = min(s.N, o.N)
        p = s.p * fmpq_poly([0]*(s.v-v)+[1]) + o.p * fmpq_poly([0]*(o.v-v)+[1])
        return S(p, v, N)
    __radd__ = __add__
    def __neg__(s): return S(-s.p, s.v, s.N)
    def __sub__(s, o): return s + (-o)
    def __rsub__(s, o): return (-s) + o
    def __mul__(s, o):
        if not isinstance(o, S):
            return S(s.p * fmpq(o) if not isinstance(o, fmpq) else s.p*o, s.v, s.N)
        v = s.v + o.v
        # relative precision
        N = min(s.N + o.v, o.N + s.v)
        L = N - v
        if L <= 0: return S(fmpq_poly([]), v, N)
        a = fmpq_poly(s.p.coeffs()[:L]); b = fmpq_poly(o.p.coeffs()[:L])
        return S(a*b, v, N)
    __rmul__ = __mul__
    def inv(s):
        # normalize leading coeff
        c = s.p.coeffs()
        k = 0
        while k < len(c) and c[k] == 0: k += 1
        p = fmpq_poly(c[k:]); v = s.v + k
        L = s.N - v  # relative precision
        ip = _inv(p, L)
        return S(ip, -v, -v + L)
    def __pow__(s, e):
        if e < 0: return s.inv() ** (-e)
        r = const(1, s.N + max(0, (e-1)*s.v) if s.v > 0 else s.N); b = s
        r = None
        while e:
            if e & 1: r = b if r is None else r * b
            e >>= 1
            if e: b = b * b
        return r if r is not None else const(1, s.N)
    def subs(s, m):
        """q -> q^m"""
        c = s.p.coeffs(); nc = [0]*((len(c)-1)*m+1) if c else []
        for i, x in enumerate(c): nc[i*m] = x
        return S(fmpq_poly(nc), s.v*m, s.N*m)
    def U(s, m):
        """U_m: sum a(mk) q^k"""
        lo = -((-s.v)//m)  # ceil(v/m)
        hi = (s.N - 1)//m  # last k with mk < N
        c = [s.coeff(m*k) for k in range(lo, hi+1)]
        return S(fmpq_poly(c), lo, hi+1)
    def lead(s):
        c = s.p.coeffs(); k = 0
        while k < len(c) and c[k] == 0: k += 1
        return (s.v + k, c[k]) if k < len(c) else (None, 0)
    def is_zero(s):
        return all(x == 0 for x in s.p.coeffs())
    def coeffs_range(s, a, b):
        return [s.coeff(n) for n in range(a, b)]
    def __repr__(s):
        terms = []
        for i, x in enumerate(s.p.coeffs()[:8]):
            if x != 0: terms.append(f"{x}q^{s.v+i}")
        return " + ".join(terms) + f" + O(q^{s.N})"

def _inv(p, L):
    """Newton inversion of power series p (p[0]!=0) mod q^L"""
    c = p.coeffs()
    g = fmpq_poly([1/fmpq(c[0])]); k = 1
    while k < L:
        k = min(2*k, L)
        pk = fmpq_poly(c[:k])
        e = fmpq_poly(((pk*g).coeffs()+[0]*k)[:k])
        g = fmpq_poly((g*(2 - e)).coeffs()[:k])
    return g

def const(c, N):
    return S(fmpq_poly([c]), 0, N)

def euler(m, N):
    """prod_{n>=1} (1 - q^{mn}) mod q^N via pentagonal theorem"""
    c = [0]*N
    k = 0
    while True:
        done = True
        for kk in ([k] if k == 0 else [k, -k]):
            e = m * kk*(3*kk-1)//2
            if e < N:
                c[e] += (-1)**(kk % 2); done = False
        if done and k > 0: break
        k += 1
    return S(fmpq_poly(c), 0, N)

def etaq(exps, shift, N):
    """q^shift * prod_d (q^d;q^d)^{r_d}, exps = {d: r_d}"""
    r = const(1, N + max(0, -shift) + 10)
    NN = N - shift if shift < 0 else N
    NN = max(NN, N) + abs(shift)
    for d, e in exps.items():
        r = r * (euler(d, NN) ** e)
    out = S(r.p, r.v + shift, r.N + shift)
    out.N = min(out.N, N); out._trunc()
    return out

def val_p(x, p):
    x = fmpq(x)
    if x == 0: return 10**9
    n, d = int(x.p), int(x.q)
    v = 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v
