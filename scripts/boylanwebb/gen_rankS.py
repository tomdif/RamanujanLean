#!/usr/bin/env python3
"""Propose the finite data for `RankSPacked` at a prime with `s` vanishing low coefficients.

Shape: `dim S_{p-1} = s + 2`, `D = U(Φ ·)` kills `a₁, …, a_s` (`s p < δ`), the odd orbit has a
second-order recurrence, and the error observation is an `s`-vector moved by an `s × s` matrix
`Θ`. This covers `p = 53, 59` (`s = 2`); `p = 37, …, 47` (`s = 1`) are the `Rank2` files.

Everything printed is re-checked in Lean: lanes by one `decide +kernel` evaluation of
`RankSPacked.ok`, the identities in `ZMod p` by `decide`. Python only proposes.
Usage: python3 scripts/boylanwebb/gen_rankS.py 53
"""
import sys
import numpy as np
import sympy
from sympy.polys.matrices import DomainMatrix


def sigma(k, N, M):
    s = [0] * (N + 1)
    for d in range(1, N + 1):
        dk = pow(d, k, M)
        for m in range(d, N + 1, d):
            s[m] = (s[m] + dk) % M
    return s


def mul(a, b, M, N):
    r = np.convolve(np.array(a[:N + 1], dtype=np.int64), np.array(b[:N + 1], dtype=np.int64))[:N + 1]
    return [int(x) % M for x in r]


def inv(a, M, N):
    a = np.array(a[:N + 1], dtype=np.int64)
    r = np.zeros(N + 1, dtype=np.int64)
    r[0] = 1
    for n in range(1, N + 1):
        r[n] = (-int(np.dot(a[1:n + 1], r[n - 1::-1][:n]) % M)) % M
    return [int(x) for x in r]


def gf(p, A):
    return DomainMatrix.from_Matrix(sympy.Matrix(A)).convert_to(sympy.GF(p))


def to_int(p, DM):
    return [[int(x) % p for x in row] for row in DM.to_Matrix().tolist()]


def nullspace(p, A):
    """Basis of {v : A v = 0} over F_p, as lists."""
    ns = gf(p, A).nullspace()
    return [[int(x) % p for x in row] for row in ns.to_Matrix().tolist()]


def solve(p, A, b):
    """Some x with A x = b over F_p."""
    n = len(A[0])
    aug = sympy.Matrix(A).row_join(sympy.Matrix(b))
    R, piv = aug.applyfunc(lambda t: t % p).rref(iszerofunc=lambda t: t % p == 0,
                                                 normalize_last=False,
                                                 simplify=lambda t: t % p)
    # fall back to a modular solve
    Mx = gf(p, A)
    rhs = gf(p, [[v] for v in b])
    x = Mx.lu_solve(rhs) if Mx.shape[0] == Mx.shape[1] and Mx.rank() == n else None
    if x is not None:
        return [int(t) % p for t in x.to_Matrix()]
    # general: brute over nullspace offsets via rref of augmented system
    import itertools
    for cand in itertools.product(range(p), repeat=n):
        if all(sum(A[r][c] * cand[c] for c in range(n)) % p == b[r] % p for r in range(len(A))):
            return list(cand)
    raise ValueError


def run(p):
    M = p * p
    delta = (p * p - 1) // 24
    s = max(t for t in range(1, p) if t * p < delta)
    d = s + 2
    N = (d + 1) * p * p + 10
    s3 = sigma(3, N, M)
    s5 = sigma(5, N, M)
    E4 = [1] + [240 * s3[n] % M for n in range(1, N + 1)]
    E6 = [1] + [(-504 * s5[n]) % M for n in range(1, N + 1)]
    q = [0] * (N + 1)
    for k in range(-600, 601):
        e = k * (3 * k - 1) // 2
        if 0 <= e <= N:
            q[e] = (q[e] + (-1) ** (k % 2)) % M
    qinv = inv(q, M, N)
    P24 = [1] + [0] * N
    base = q[:]
    e = 24
    while e:
        if e & 1:
            P24 = mul(P24, base, M, N)
        base = mul(base, base, M, N)
        e >>= 1
    Dz = [0] + P24[:N]
    ql2 = [0] * (N + 1)
    for i in range(0, N // (p * p) + 1):
        ql2[i * p * p] = q[i]
    Phi = [0] * delta + mul(ql2, qinv, M, N)[:N + 1 - delta]
    w = p - 1
    ex, basis = [], []
    for j in range(1, d + 1):
        r = w - 12 * j
        for b in (0, 1):
            if r - 6 * b >= 0 and (r - 6 * b) % 4 == 0:
                a = (r - 6 * b) // 4
                break
        f = [1] + [0] * N
        for _ in range(j):
            f = mul(f, Dz, M, N)
        for _ in range(a):
            f = mul(f, E4, M, N)
        for _ in range(b):
            f = mul(f, E6, M, N)
        ex.append((j, a, b))
        basis.append(f)
    sp = sigma(p - 2, N, p)
    Einv = [1] + [(2 * p * sp[n]) % M for n in range(1, N + 1)]
    U = lambda F: [F[p * n] for n in range(len(F) // p)]
    Dop = lambda F: U(mul(Phi, F, M, N))
    R = range(d)
    B = [[basis[i][k + 1] % p for i in R] for k in R]       # B[k][i]
    Binv = to_int(p, gf(p, B).inv())

    def coords(F):
        v = [F[k + 1] % p for k in R]
        return [sum(Binv[i][k] * v[k] for k in R) % p for i in R]

    Um = [[0] * d for _ in R]
    Dm = [[0] * d for _ in R]
    for i in R:
        cu = coords(U(basis[i]))
        cd = coords(Dop(basis[i]))
        for j in R:
            Um[j][i] = cu[j]
            Dm[j][i] = cd[j]
    seed = coords(Dop([1] + [0] * N))
    # sanity: D-images and the seed have a_1..a_s = 0
    for i in R:
        F = Dop(basis[i])
        assert all(F[t] % p == 0 for t in range(1, s + 1))
    Uinv = to_int(p, gf(p, Um).inv())
    # omega^a = B_a U^{-1} (row), w^a = omega^a B^{-1}; then omega^a U = B_a, lam = identity
    om = [[sum(B[a][j] * Uinv[j][i] for j in R) % p for i in R] for a in range(s)]
    wv = [[sum(om[a][i] * Binv[i][k] for i in R) % p for k in R] for a in range(s)]
    lam = [[1 if a == t else 0 for t in range(s)] for a in range(s)]
    obsf = lambda a, F, m: sum(wv[a][k] * F[k + 1] for k in R) % m
    z = [[0] * d for _ in range(s)]
    for i, f in enumerate(basis):
        Y = U(Dop(mul(f, Einv, M, N)))
        for a in range(s):
            o = obsf(a, Y, M)
            assert o % p == 0
            z[a][i] = o // p
    L2 = U(Dop([1] + [0] * N))
    zL2 = []
    for a in range(s):
        o = obsf(a, L2, M)
        assert o % p == 0
        zL2.append(o // p)
    # theta: on ker Dm, z^a = sum_b theta_ab omega^b
    ker = nullspace(p, Dm)
    assert len(ker) == s, len(ker)
    Ok = [[sum(om[b][i] * kv[i] for i in R) % p for b in range(s)] for kv in ker]  # rows: kernel vecs
    th = []
    for a in range(s):
        rhs = [sum(z[a][i] * kv[i] for i in R) % p for kv in ker]
        th.append(solve(p, Ok, rhs))
    mu = []
    for a in range(s):
        rhs = [(z[a][i] - sum(th[a][b] * om[b][i] for b in range(s))) % p for i in R]
        # rhs_i = sum_j mu_j Dm[j][i]
        mu.append(solve(p, [[Dm[j][i] for j in R] for i in R], rhs))
    thinv = to_int(p, gf(p, th).inv())
    X = [[sum(Dm[r][t] * Um[t][c] for t in R) % p for c in R] for r in R]
    mv = lambda Mx, v: [sum(Mx[r][c] * v[c] for c in R) % p for r in R]
    o0 = seed
    o1 = mv(X, o0)
    o2 = mv(X, o1)
    k0 = k1 = None
    for a in range(p):
        for b in range(p):
            if all((o2[i] - b * o1[i] - a * o0[i]) % p == 0 for i in R):
                k0, k1 = a, b
    assert k0 is not None and k0 != 0
    lin = lambda k, v: sum(B[k][i] * v[i] for i in R) % p
    det0 = (lin(s, o0) * lin(s + 1, o1) - lin(s, o1) * lin(s + 1, o0)) % p
    Uo1 = mv(Um, o1)
    Uo0 = mv(Um, o0)
    init = [(sum(Uo1[i] * z[a][i] for i in R) - k1 * sum(Uo0[i] * z[a][i] for i in R) - k0 * zL2[a]) % p
            for a in range(s)]
    c = pow(-24 % p, -1, p)
    return dict(p=p, s=s, N=d * p * p + 1, c=c, ex=ex, B=B, Binv=Binv, Um=Um, Dm=Dm, seed=seed, w=wv,
                lam=lam, z=z, zL2=zL2, theta=th, thinv=thinv, mu=mu, k0=k0, k1=k1, det0=det0, init=init)


def mat(Mx):
    return "![" + ", ".join("![" + ", ".join(str(x) for x in row) + "]" for row in Mx) + "]"


def vec(v):
    return "![" + ", ".join(str(x) for x in v) + "]"


def emit(r):
    p, s, N = r["p"], r["s"], r["N"]
    lv = (N - 1).bit_length()
    dd = 7
    ex = ", ".join(f"({j}, {a}, {b})" for (j, a, b) in r["ex"])
    out = []
    w = out.append
    w("import RamanujanTau.FiniteArithmetic.RankSPacked\n")
    w(f"/-! # Boylan–Webb's threshold at {p}: `b_{p}(m) = 2m − 1` for every `m`\n\n"
      f"Generated by `scripts/boylanwebb/gen_rankS.py {p}`. The tables are proposals: the kernel\n"
      "checks every lane in one evaluation of `RankSPacked.ok`, and `decide` checks the\n"
      "identities in `ZMod p`. -/\n")
    w("set_option autoImplicit false\n")
    w(f"namespace RamanujanTau.FiniteArithmetic.RankSAt{p}\nopen RankSPacked\n\n")
    w(f"instance : Fact (Nat.Prime {p}) := ⟨by norm_num⟩\n\n")
    w(f"def P : Params {s} := ⟨{p}, {N}, {lv}, {r['c']}, {p}^2 * (2^18 / {p}^2), {dd}, 1, 14, 12, 18, 33, ![{ex}]⟩\n\n")
    w(f"def T : Table {s} := ⟨{mat(r['B'])},\n  {mat(r['Um'])},\n  {mat(r['Dm'])},\n  "
      f"{vec(r['seed'])}, {mat(r['w'])}, {mat(r['z'])}, {vec(r['zL2'])}⟩\n\n")
    w(f"def X : Extra {s} := ⟨{mat(r['Binv'])}, {mat(r['lam'])}, {mat(r['theta'])}, {mat(r['thinv'])},\n"
      f"  {mat(r['mu'])}, {r['k0']}, {r['k1']}⟩\n\n")
    w("set_option maxRecDepth 100000 in\n")
    w("/-- The single kernel evaluation of all lanes. -/\n")
    w("theorem ok_eq : ok P T = true := by decide +kernel\n\n")
    w("theorem sizes : Sizes P := ⟨" + ", ".join(["by decide"] * 21) + "⟩\n\n")
    w(f"theorem identities : Identities {p} T X := ⟨" + ", ".join(["by decide"] * 9) + "⟩\n\n")
    w(f"/-- **`b_{p}(m) = 2m − 1` for every `m ≥ 1`** (Boylan–Webb's literal invariant). -/\n")
    w(f"theorem bEll_{p} (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll {p} m = 2 * m - 1 :=\n")
    w(f"  @bEll_of_ok {s} P T X (inferInstanceAs (Fact (Nat.Prime {p}))) sizes identities ok_eq m hm\n\n")
    w(f"end RamanujanTau.FiniteArithmetic.RankSAt{p}\n")
    return "".join(out)


if __name__ == "__main__":
    for p in map(int, sys.argv[1:]):
        r = run(p)
        print(f"-- {p}: s={r['s']} theta={r['theta']} init={r['init']} det0={r['det0']} k0={r['k0']} "
              f"k1={r['k1']} zL2={r['zL2']}", file=sys.stderr)
        if "--emit" in sys.argv or True:
            open(f"RamanujanTau/FiniteArithmetic/RankSAt{p}.lean", "w").write(emit(r))
