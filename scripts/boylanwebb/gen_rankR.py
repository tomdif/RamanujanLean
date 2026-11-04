#!/usr/bin/env python3
"""Propose the finite data for `RankRPacked`: `s` killed low coefficients, odd recurrence of order `r`.

Shape: `dim S_{p-1} = s + r`, `D = U(Φ ·)` kills `a₁, …, a_s` (`s p < δ`), the odd orbit has a
recurrence of order `r`, and the error observation is an `s`-vector moved by an `s × s` matrix
`Θ`. Used for `p = 61, 67, 71` (`s = 2`, `r = 3`).

Everything printed is re-checked in Lean: lanes by one `decide +kernel` evaluation of
`RankRPacked.ok`, the identities in `ZMod p` by `decide`. Python only proposes.
Usage: python3 scripts/boylanwebb/gen_rankR.py 61
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


def _fftconv(x, y):
    n = len(x) + len(y) - 1
    m = 1 << (n - 1).bit_length()
    r = np.fft.irfft(np.fft.rfft(x, m) * np.fft.rfft(y, m), m)[:n]
    return np.rint(r).astype(np.int64)


def mul(a, b, M, N):
    """Exact product mod M (< 2^28) truncated at degree N: split into 7-bit limbs, FFT each pair."""
    x = np.array(a[:N + 1], dtype=np.int64) % M
    y = np.array(b[:N + 1], dtype=np.int64) % M
    if len(x) < 2000 or len(y) < 2000:
        r = np.convolve(x, y)[:N + 1]
        return [int(t) % M for t in r]
    B = 1 << 7
    x0, x1 = x % B, x // B
    y0, y1 = y % B, y // B
    c00 = _fftconv(x0, y0) % M
    c11 = _fftconv(x1, y1) % M
    c01 = (_fftconv(x0, y1) + _fftconv(x1, y0)) % M
    r = (c00 + (c01 * B) % M + (c11 * (B * B % M)) % M) % M
    return [int(t) for t in r[:N + 1]]


def inv(a, M, N):
    """Power-series inverse mod M (a[0] = 1) by Newton iteration with exact FFT products."""
    r = [1]
    k = 1
    while k < N + 1:
        k = min(2 * k, N + 1)
        ar = mul(a[:k], r, M, k - 1)
        t = [(-x) % M for x in ar]
        t[0] = (t[0] + 2) % M
        r = mul(r, t, M, k - 1)
    return r[:N + 1]


def gf(p, A):
    return DomainMatrix.from_Matrix(sympy.Matrix(A)).convert_to(sympy.GF(p))


def to_int(p, DM):
    return [[int(x) % p for x in row] for row in DM.to_Matrix().tolist()]


def nullspace(p, A):
    """Basis of {v : A v = 0} over F_p, as lists."""
    ns = gf(p, A).nullspace()
    return [[int(x) % p for x in row] for row in ns.to_Matrix().tolist()]


def solve(p, A, b):
    """Some x with A x = b over F_p (Gaussian elimination)."""
    m, n = len(A), len(A[0])
    M = [[A[i][j] % p for j in range(n)] + [b[i] % p] for i in range(m)]
    piv, row = [], 0
    for c in range(n):
        r0 = next((i for i in range(row, m) if M[i][c]), None)
        if r0 is None:
            continue
        M[row], M[r0] = M[r0], M[row]
        iv = pow(M[row][c], -1, p)
        M[row] = [v * iv % p for v in M[row]]
        for i in range(m):
            if i != row and M[i][c]:
                f = M[i][c]
                M[i] = [(vi - f * vr) % p for vi, vr in zip(M[i], M[row])]
        piv.append(c)
        row += 1
    if any(M[i][n] for i in range(row, m)):
        raise ValueError("no solution")
    x = [0] * n
    for i, c in enumerate(piv):
        x[c] = M[i][n]
    return x


def run(p):
    M = p * p
    delta = (p * p - 1) // 24
    s = max(t for t in range(1, p) if t * p < delta)
    d = (p - 1) // 12 if (p - 1) % 12 != 2 else (p - 1) // 12 - 1
    r = d - s
    N = (d + 1) * p * p + 10
    s3 = sigma(3, N, M)
    s5 = sigma(5, N, M)
    E4 = [1] + [240 * s3[n] % M for n in range(1, N + 1)]
    E6 = [1] + [(-504 * s5[n]) % M for n in range(1, N + 1)]
    q = [0] * (N + 1)
    import math
    kmax = math.isqrt(2 * N // 3 + 1) + 2
    for k in range(-kmax, kmax + 1):
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
    r = d - s
    X = [[sum(Dm[a][t] * Um[t][b] for t in R) % p for b in R] for a in R]
    mv = lambda Mx, v: [sum(Mx[a][b] * v[b] for b in R) % p for a in R]
    orb = [seed]
    for _ in range(r):
        orb.append(mv(X, orb[-1]))
    A = [[orb[j][i] for j in range(r)] for i in R]
    kk = solve(p, A, orb[r])
    assert all((orb[r][i] - sum(kk[j] * orb[j][i] for j in range(r))) % p == 0 for i in R)
    lin = lambda k, v: sum(B[k][i] * v[i] for i in R) % p
    W = [[lin(s + i, orb[j]) for j in range(r)] for i in range(r)]
    det0 = int(sympy.Matrix(W).det()) % p
    comp = [[(1 if t == j + 1 else 0) if j + 1 < r else kk[t] for j in range(r)] for t in range(r)]
    detc = int(sympy.Matrix(comp).det()) % p
    assert det0 != 0 and detc != 0, (det0, detc)
    def zev(j, a):
        if j == 0:
            return zL2[a]
        Uo = mv(Um, orb[j - 1])
        return sum(Uo[i] * z[a][i] for i in R) % p
    init = [(zev(r, a) - sum(kk[j] * zev(j, a) for j in range(r))) % p for a in range(s)]
    assert any(init)
    c = pow(-24 % p, -1, p)
    _extra = dict(Phi=Phi, L2=L2)
    return dict(_extra=_extra, p=p, s=s, r=r, N=d * p * p + 1, c=c, ex=ex, B=B, Binv=Binv, Um=Um, Dm=Dm, seed=seed,
                w=wv, lam=lam, z=z, zL2=zL2, theta=th, thinv=thinv, mu=mu, k=kk, det0=det0, detc=detc,
                init=init)


def mat(Mx):
    return "![" + ", ".join("![" + ", ".join(str(x) for x in row) + "]" for row in Mx) + "]"


def vec(v):
    return "![" + ", ".join(str(x) for x in v) + "]"


def emit(r):
    p, s, N, rr = r["p"], r["s"], r["N"], r["r"]
    lv = (N - 1).bit_length()
    dd = next(t for t in range(4, 20) if (2 ** t + 1) * (3 * (2 ** t + 1) - 1) // 2 >= N)
    ex = ", ".join(f"({j}, {a}, {b})" for (j, a, b) in r["ex"])
    out = []
    w = out.append
    w("import RamanujanTau.FiniteArithmetic.RankRPacked\n")
    w(f"/-! # Boylan–Webb's threshold at {p}: `b_{p}(m) = 2m − 1` for every `m`\n\n"
      f"Generated by `scripts/boylanwebb/gen_rankR.py {p}`. The tables are proposals: the kernel\n"
      "checks every lane in one evaluation of `RankRPacked.ok`, and `decide` checks the\n"
      "identities in `ZMod p`. -/\n")
    w("set_option autoImplicit false\n")
    w(f"namespace RamanujanTau.FiniteArithmetic.RankRAt{p}\nopen RankRPacked\n\n")
    w(f"instance : Fact (Nat.Prime {p}) := ⟨by norm_num⟩\n\n")
    w(f"def P : Params {s} {rr} := ⟨{p}, {N}, {lv}, {r['c']}, {p}^2 * (2^18 / {p}^2), {dd}, 1, {lv}, {(p * p).bit_length()}, 18, 33, ![{ex}]⟩\n\n")
    w(f"def T : Table {s} {rr} := ⟨{mat(r['B'])},\n  {mat(r['Um'])},\n  {mat(r['Dm'])},\n  "
      f"{vec(r['seed'])}, {mat(r['w'])}, {mat(r['z'])}, {vec(r['zL2'])}⟩\n\n")
    w(f"def X : Extra {s} {rr} := ⟨{mat(r['Binv'])}, {mat(r['lam'])}, {mat(r['theta'])}, {mat(r['thinv'])},\n"
      f"  {mat(r['mu'])}, {vec(r['k'])}⟩\n\n")
    w("set_option maxRecDepth 100000 in\n")
    w("/-- The single kernel evaluation of all lanes. -/\n")
    w("theorem ok_eq : ok P T = true := by decide +kernel\n\n")
    w("theorem sizes : Sizes P := ⟨" + ", ".join(["by decide"] * 22) + "⟩\n\n")
    w("set_option maxHeartbeats 0 in\n")
    w(f"theorem identities : Identities {p} T X := ⟨" + ", ".join(["by decide +kernel"] * 9) + "⟩\n\n")
    w(f"/-- **`b_{p}(m) = 2m − 1` for every `m ≥ 1`** (Boylan–Webb's literal invariant). -/\n")
    w(f"theorem bEll_{p} (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll {p} m = 2 * m - 1 :=\n")
    w(f"  @bEll_of_ok {s} {rr} P T X (inferInstanceAs (Fact (Nat.Prime {p}))) sizes identities ok_eq m hm\n\n")
    w(f"end RamanujanTau.FiniteArithmetic.RankRAt{p}\n")
    return "".join(out)


if __name__ == "__main__":
    for p in map(int, sys.argv[1:]):
        r = run(p)
        print(f"-- {p}: s={r['s']} r={r['r']} theta={r['theta']} init={r['init']} det0={r['det0']} "
              f"detC={r['detc']} k={r['k']} zL2={r['zL2']}", file=sys.stderr)
        if "--emit" in sys.argv or True:
            import os
            open(os.path.join(os.environ.get("GEN_OUT", "RamanujanTau/FiniteArithmetic"), f"RankRAt{p}.lean"), "w").write(emit(r))
