#!/usr/bin/env python3
"""Propose the finite data for `Rank2Packed` at a rank-two prime (37, 41, 43, 47).

Everything printed here is re-checked in Lean: lanes by one `decide +kernel` evaluation of
`Rank2Packed.ok`, and the identities in `ZMod p` by `decide`. Python only proposes.
Usage: python3 scripts/boylanwebb/gen_rank2.py 37
"""
import sys
import itertools
import numpy as np


def sigma(k, N):
    s = [0] * (N + 1)
    for d in range(1, N + 1):
        dk = pow(d, k)
        for m in range(d, N + 1, d):
            s[m] += dk
    return s


def mul(a, b, M, N):
    r = np.convolve(np.array(a[:N + 1], dtype=object), np.array(b[:N + 1], dtype=object))[:N + 1]
    return [int(x) % M for x in r]


def inv(a, M, N):
    r = [0] * (N + 1)
    r[0] = 1
    for n in range(1, N + 1):
        s = 0
        for k in range(1, n + 1):
            if a[k]:
                s += a[k] * r[n - k]
        r[n] = (-s) % M
    return r


def solve_mod(A, b, p):
    """Some solution x of A x = b over F_p (A: list of rows)."""
    n = len(A[0])
    for x in itertools.product(range(p), repeat=n):
        if all(sum(A[r][c] * x[c] for c in range(n)) % p == b[r] % p for r in range(len(A))):
            return list(x)
    raise ValueError("no solution")


def matinv(B, p):
    import sympy
    return [[int(v) % p for v in row] for row in sympy.Matrix(B).inv_mod(p).tolist()]


def run(p):
    M = p * p
    N = 4 * p * p + 10
    s3 = sigma(3, N)
    s5 = sigma(5, N)
    E4 = [1] + [240 * s3[n] % M for n in range(1, N + 1)]
    E6 = [1] + [(-504 * s5[n]) % M for n in range(1, N + 1)]
    q = [0] * (N + 1)
    for k in range(-300, 301):
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
    delta = (p * p - 1) // 24
    ql2 = [0] * (N + 1)
    for i in range(0, N // (p * p) + 1):
        ql2[i * p * p] = q[i]
    Phi = [0] * delta + mul(ql2, qinv, M, N)[:N + 1 - delta]
    w = p - 1
    ex = []
    basis = []
    for j in (1, 2, 3):
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
    sp = sigma(p - 2, N)
    Einv = [1] + [(2 * p * sp[n]) % M for n in range(1, N + 1)]
    U = lambda F: [F[p * n] for n in range(len(F) // p)]
    Dop = lambda F: U(mul(Phi, F, M, N))
    B = [[basis[i][k + 1] % p for i in range(3)] for k in range(3)]   # B[k][i]
    Binv = matinv(B, p)

    def coords(F):
        v = [F[k + 1] % p for k in range(3)]
        return [sum(Binv[i][k] * v[k] for k in range(3)) % p for i in range(3)]

    Um = [[0] * 3 for _ in range(3)]
    Dm = [[0] * 3 for _ in range(3)]
    for i in range(3):
        cu = coords(U(basis[i]))
        cd = coords(Dop(basis[i]))
        for j in range(3):
            Um[j][i] = cu[j]
            Dm[j][i] = cd[j]
    seed = coords(Dop([1] + [0] * N))
    # obs: weights on (a1,a2,a3) killing U of the image of D
    UD = [[sum(Um[r][t] * Dm[t][c] for t in range(3)) % p for c in range(3)] for r in range(3)]
    wv = None
    for cand in itertools.product(range(p), repeat=3):
        if cand[0] != 1:
            continue
        om = [sum(cand[k] * B[k][i] for k in range(3)) % p for i in range(3)]
        if all(sum(om[r] * UD[r][c] for r in range(3)) % p == 0 for c in range(3)):
            wv = list(cand)
            break
    om = [sum(wv[k] * B[k][i] for k in range(3)) % p for i in range(3)]
    omU = [sum(om[j] * Um[j][i] for j in range(3)) % p for i in range(3)]
    # lam: omU = lam * B[0]
    lam = None
    for t in range(p):
        if all((omU[i] - t * B[0][i]) % p == 0 for i in range(3)):
            lam = t
    assert lam is not None
    obsf = lambda F, m: sum(wv[k] * F[k + 1] for k in range(3)) % m
    z = []
    for f in basis:
        Y = U(Dop(mul(f, Einv, M, N)))
        o = obsf(Y, M)
        assert o % p == 0
        z.append(o // p)
    L2 = U(Dop([1] + [0] * N))
    oL2 = obsf(L2, M)
    assert oL2 % p == 0
    zL2 = oL2 // p
    # theta, mu: z - theta*om in the row space of Dm
    ker = [v for v in itertools.product(range(p), repeat=3)
           if any(v) and all(sum(Dm[j][i] * v[i] for i in range(3)) % p == 0 for j in range(3))]
    kv = ker[0]
    oK = sum(om[i] * kv[i] for i in range(3)) % p
    th = sum(kv[i] * z[i] for i in range(3)) * pow(oK, -1, p) % p
    rhs = [(z[i] - th * om[i]) % p for i in range(3)]
    mu = solve_mod([[Dm[j][i] for j in range(3)] for i in range(3)], rhs, p)
    # odd coordinates and the recurrence
    X = [[sum(Dm[r][t] * Um[t][c] for t in range(3)) % p for c in range(3)] for r in range(3)]
    mv = lambda Mx, v: [sum(Mx[r][c] * v[c] for c in range(3)) % p for r in range(3)]
    o0 = seed
    o1 = mv(X, o0)
    o2 = mv(X, o1)
    k0, k1 = None, None
    for a, b in itertools.product(range(p), repeat=2):
        if all((o2[i] - b * o1[i] - a * o0[i]) % p == 0 for i in range(3)):
            k0, k1 = a, b
    lin = lambda k, v: sum(B[k][i] * v[i] for i in range(3)) % p
    det0 = (lin(1, o0) * lin(2, o1) - lin(1, o1) * lin(2, o0)) % p
    Uo1 = mv(Um, o1)
    Uo0 = mv(Um, o0)
    init = (sum(Uo1[i] * z[i] for i in range(3)) - k1 * sum(Uo0[i] * z[i] for i in range(3)) - k0 * zL2) % p
    c = pow(-24 % p, -1, p)
    return dict(p=p, N=3 * p * p + 1, c=c, ex=ex, B=B, Binv=Binv, Um=Um, Dm=Dm, seed=seed, w=wv, lam=lam, z=z,
                zL2=zL2, theta=th, mu=mu, k0=k0, k1=k1, det0=det0, init=init, delta=delta)


def mat(Mx):
    return "![" + ", ".join("![" + ", ".join(str(x) for x in row) + "]" for row in Mx) + "]"


def vec(v):
    return "![" + ", ".join(str(x) for x in v) + "]"


def emit(r):
    p = r["p"]
    N = r["N"]
    d = 6 if N <= 6305 else 7
    ex = ", ".join(f"({j}, {a}, {b})" for (j, a, b) in r["ex"])
    out = []
    w = out.append
    w("import RamanujanTau.FiniteArithmetic.Rank2Packed\n")
    w(f"/-! # Boylan–Webb's threshold at {p}: `b_{p}(m) = 2m − 1` for every `m`\n\n"
      f"Generated by `scripts/boylanwebb/gen_rank2.py {p}`. The tables are proposals: the kernel\n"
      "checks every lane in one evaluation of `Rank2Packed.ok`, and `decide` checks the\n"
      "identities in `ZMod p`. -/\n")
    w("set_option autoImplicit false\n")
    w(f"namespace RamanujanTau.FiniteArithmetic.Rank2At{p}\nopen Rank2Packed\n\n")
    w(f"instance : Fact (Nat.Prime {p}) := ⟨by norm_num⟩\n\n")
    w(f"def P : Params := ⟨{p}, {N}, {r['c']}, {p}^2 * (2^18 / {p}^2), {d}, 1, 13, 12, 18, 33, ![{ex}]⟩\n\n")
    w(f"def T : Table := ⟨{mat(r['B'])},\n  {mat(r['Um'])},\n  {mat(r['Dm'])},\n  "
      f"{vec(r['seed'])}, {vec(r['w'])}, {vec(r['z'])}, {r['zL2']}⟩\n\n")
    w(f"def X : Extra := ⟨{mat(r['Binv'])}, {r['lam']}, {r['theta']}, {vec(r['mu'])}, {r['k0']}, {r['k1']}⟩\n\n")
    w("set_option maxRecDepth 100000 in\n")
    w("/-- The single kernel evaluation of all lanes. -/\n")
    w("theorem ok_eq : ok P T = true := by decide +kernel\n\n")
    w("theorem sizes : Sizes P := ⟨" + ", ".join(["by decide"] * 19) + "⟩\n\n")
    w(f"theorem identities : Identities {p} T X := ⟨" + ", ".join(["by decide"] * 9) + "⟩\n\n")
    w(f"/-- **`b_{p}(m) = 2m − 1` for every `m ≥ 1`** (Boylan–Webb's literal invariant). -/\n")
    w(f"theorem bEll_{p} (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll {p} m = 2 * m - 1 :=\n")
    w(f"  @bEll_of_ok P T X (inferInstanceAs (Fact (Nat.Prime {p}))) sizes identities ok_eq m hm\n\n")
    w(f"end RamanujanTau.FiniteArithmetic.Rank2At{p}\n")
    return "".join(out)


if __name__ == "__main__":
    for p in map(int, sys.argv[1:]):
        r = run(p)
        print(f"-- {p}: theta={r['theta']} init={r['init']} det0={r['det0']} k0={r['k0']}", file=sys.stderr)
        open(f"RamanujanTau/FiniteArithmetic/Rank2At{p}.lean", "w").write(emit(r))
