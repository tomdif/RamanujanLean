# Numerical check for the Artin-Schreier Stepanov bound.
# For q = p^r: N_c = #{x in F_q^x : Tr(x + b/x) = c}; check N_c <= q/p + 3p*p^t (t = r - r//2),
# check Y(x)*x^e = Z(x) on S_c, and |K_r| <= 3p^2 p^t + 1.
import itertools, cmath, sys

def irreducible(p, r):
    # find monic irreducible of degree r by brute force (small sizes)
    for tail in itertools.product(range(p), repeat=r):
        f = list(tail) + [1]  # coefficients low->high
        if f[0] == 0: continue
        # check no roots in subfields: test x^(p^r) = x and gcd conditions via order check
        ok = True
        # brute: f irreducible iff x^{p^k} != x mod f for k<r with k|r ... simple check via polynomial gcd
        def mulmod(a, b):
            res = [0]*(2*r)
            for i, ai in enumerate(a):
                if ai:
                    for j, bj in enumerate(b):
                        res[i+j] = (res[i+j] + ai*bj) % p
            for d in range(2*r-1, r-1, -1):
                c = res[d]
                if c:
                    for k in range(r+1):
                        res[d-r+k] = (res[d-r+k] - c*f[k]) % p
            return res[:r]
        def powmod(a, n):
            out = [1]+[0]*(r-1)
            while n:
                if n & 1: out = mulmod(out, a)
                a = mulmod(a, a); n >>= 1
            return out
        x = [0,1]+[0]*(r-2) if r >= 2 else [0]
        if r == 1: return f, mulmod
        def divides(g, h):  # does monic g divide h (low->high lists)?
            h = h[:]; dg = len(g)-1
            for d in range(len(h)-1, dg-1, -1):
                c = h[d]
                if c:
                    for k in range(dg+1): h[d-dg+k] = (h[d-dg+k] - c*g[k]) % p
            return not any(h[:dg])
        good = True
        for dg in range(1, r//2+1):
            for tl in itertools.product(range(p), repeat=dg):
                if divides(list(tl)+[1], f): good = False; break
            if not good: break
        if good:
            return f, mulmod
    raise Exception

def run(p, r):
    q = p**r
    f, mulmod = irreducible(p, r)
    elems = list(itertools.product(range(p), repeat=r))
    elems = [list(e) for e in elems]
    def powe(a, n):
        out = [1]+[0]*(r-1)
        while n:
            if n & 1: out = mulmod(out, a)
            a = mulmod(a, a); n >>= 1
        return out
    def add(a, b): return [(u+v) % p for u, v in zip(a, b)]
    def sc(c, a): return [(c*u) % p for u in a]
    s = r // 2; t = r - s; e = p**(s-1)
    worst = 0.0; worstK = 0.0
    for b in range(1, p):
        N = [0]*p
        K = 0
        for xv in elems:
            if not any(xv): continue
            xi = powe(xv, q-2)
            z = add(xv, sc(b, xi))
            tr = [0]*r
            for i in range(r): tr = add(tr, powe(z, p**i))
            assert all(v == 0 for v in tr[1:])
            c = tr[0]; N[c] += 1
            K += cmath.exp(2j*cmath.pi*c/p)
            # identity Y(x) x^e = Z(x)
            Y = [0]*r
            for i in range(s, r):
                Y = add(Y, add(powe(xv, q+p**i), sc(b, powe(xv, q-p**i))))
            lhs = mulmod(Y, powe(xv, e))
            Z = sc(c, powe(xv, e+1))
            for i in range(s):
                Z = add(Z, sc(p-1, add(powe(xv, e+1+p**i), sc(b, powe(xv, e+1-p**i)))))
            assert lhs == Z, (p, r, b, xv)
        B = q//p + 3*p*p**t
        assert max(N) <= B
        assert abs(K) <= 3*p*p*p**t + 1
        worst = max(worst, max(abs(n - (q-1)/p) for n in N)/q**0.5)
        worstK = max(worstK, abs(K)/q**0.5)
    print(f"p={p} r={r} q={q}: max|N_c-(q-1)/p|/sqrt q = {worst:.3f}, max|K|/sqrt q = {worstK:.3f}, bound B-q/p = {3*p*p**t}")

for p, rs in [(2, range(2, 12)), (3, range(2, 8)), (5, range(2, 5)), (7, range(2, 4))]:
    for r in rs: run(p, r)
