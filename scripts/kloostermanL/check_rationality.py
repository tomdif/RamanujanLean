"""Numerical check of Kloosterman L-function rationality (small p, r <= 4).
Checks (i) K_r = -(alpha^r+beta^r), alpha+beta=-K_1, alpha*beta=p, via the recurrence
K_r = -K_1 K_{r-1} - p K_{r-2} (K_0 := -2); (ii) A_n = sum over monic f of degree n of
lam(f) = [f(0)!=0] psi(-a*c_{X^{n-1}} - b*c_{X^1}/c_{X^0}) is 1, K_1, p, 0, 0; (iii) Weil |K_1|<=2 sqrt p."""
import cmath, itertools, math

def polymulmod(u, v, m, p):
    # polynomials as lists low->high; m monic
    res = [0]*(len(u)+len(v)-1)
    for i, x in enumerate(u):
        for j, y in enumerate(v):
            res[i+j] = (res[i+j] + x*y) % p
    d = len(m)-1
    for k in range(len(res)-1, d-1, -1):
        c = res[k]
        if c:
            for t in range(d+1):
                res[k-d+t] = (res[k-d+t] - c*m[t]) % p
    return (res + [0]*d)[:d]

def is_irred(m, p):
    d = len(m)-1
    # brute: no factor of degree <= d//2
    for e in range(1, d//2+1):
        for cs in itertools.product(range(p), repeat=e):
            g = list(cs)+[1]
            # remainder of m mod g
            r = m[:]
            for k in range(len(r)-1, e-1, -1):
                c = r[k]
                if c:
                    for t in range(e+1):
                        r[k-e+t] = (r[k-e+t]-c*g[t]) % p
            if all(x == 0 for x in r[:e]):
                return False
    return True

def field(p, r):
    if r == 1:
        return [1, 0][::-1] if False else None
    for cs in itertools.product(range(p), repeat=r):
        m = list(cs)+[1]
        if is_irred(m, p):
            return m

def K(p, r, a, b):
    psi = lambda t: cmath.exp(2j*math.pi*t/p)
    if r == 1:
        return sum(psi((a*x + b*pow(x, -1, p)) % p) for x in range(1, p))
    m = field(p, r)
    elems = [list(cs) for cs in itertools.product(range(p), repeat=r)]
    one = [1]+[0]*(r-1)
    def mul(u, v): return polymulmod(u, v, m, p)
    def power(u, e):
        res = one[:]
        while e:
            if e & 1: res = mul(res, u)
            u = mul(u, u); e >>= 1
        return res
    q = p**r
    def tr(u):  # sum of Frobenius conjugates, lands in F_p (constant coefficient)
        s = [0]*r; v = u[:]
        for _ in range(r):
            s = [(x+y) % p for x, y in zip(s, v)]; v = power(v, p)
        assert all(x == 0 for x in s[1:])
        return s[0]
    tot = 0
    for u in elems:
        if any(u):
            inv = power(u, q-2)
            tot += psi((a*tr(u) + b*tr(inv)) % p)
    return tot

def A(p, n, a, b):
    psi = lambda t: cmath.exp(2j*math.pi*t/p)
    if n == 0: return 1
    s = 0
    for cs in itertools.product(range(p), repeat=n):  # cs[i] = coeff of X^i
        if cs[0] == 0: continue
        c1 = cs[1] if n >= 2 else 1   # coeff of X^1 (for n=1, X^1 is the leading coeff 1)
        s += psi((-a*cs[n-1] - b*c1*pow(cs[0], -1, p)) % p)
    return s

worst = 0
for p in [2, 3, 5, 7]:
    rmax = 4 if p <= 5 else 3
    for a in range(1, p):
        for b in range(1, p):
            Ks = [None]+[K(p, r, a, b) for r in range(1, rmax+1)]
            prev2, prev1 = -2, Ks[1]
            for r in range(2, rmax+1):
                pred = -Ks[1]*prev1 - p*prev2
                worst = max(worst, abs(pred-Ks[r]))
                prev2, prev1 = prev1, Ks[r]
            assert abs(Ks[1]) <= 2*math.sqrt(p)+1e-9
            for n, expect in [(0, 1), (1, Ks[1]), (2, p), (3, 0), (4, 0)]:
                if n <= 4 and p**n <= 3000:
                    assert abs(A(p, n, a, b)-expect) < 1e-6, (p, a, b, n)
    print(f"p={p}: r<= {rmax} recurrence + A_n checks OK")
print("max recurrence error", worst)
