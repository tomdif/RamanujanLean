#!/usr/bin/env python3
"""Generate the Lean ECS definitions and the theta-identity theorem (in L = C((t))) for Cao-style proofs of
Ramanujan's forty identities.  See RamanujanTau/Forty/Lattice.lean (qf_two, θθ_lattice) and Tools.lean.

Usage:  python3 scripts/forty/gen.py <entry>      (prints Lean to stdout)
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from ecs import typeI, typeII, find_ecs, c2  # noqa: E402


def coset_formula(b, r, I):
    """i = ((al*m + be*n - lo) % k) + lo characterises the coset of (m,n)."""
    b11, b12, b21, b22 = b
    det = b11 * b22 - b12 * b21
    k = abs(det)
    lo = I[0]
    def idx(m, n):
        hits = []
        for i in I:
            x, y = m - r[0] * i, n - r[1] * i
            if (b22 * x - b12 * y) % det == 0 and (b11 * y - b21 * x) % det == 0:
                hits.append(i)
        assert len(hits) == 1
        return hits[0]
    for al in range(k):
        for be in range(k):
            if all((al * m + be * n - idx(m, n)) % k == 0 for m in range(-k, k) for n in range(-k, k)):
                return al, be, det
    raise ValueError("no linear coset formula")


def lean_int(x):
    return f"({x})" if x < 0 else str(x)


def ecs_def(name, b, r, I, doc=""):
    b11, b12, b21, b22 = b
    al, be, det = coset_formula(b, r, I)
    k = abs(det)
    lo = I[0]
    i_expr = f"(({al} * m + {be} * n - {lean_int(lo)}) % {k} + {lean_int(lo)})"
    # u = (b22 (m - r1 i) - b12 (n - r2 i)) / det ;  v = (b11 (n - r2 i) - b21 (m - r1 i)) / det
    x = f"(m - {lean_int(r[0])} * {i_expr})"
    y = f"(n - {lean_int(r[1])} * {i_expr})"
    u_expr = f"(({lean_int(b22)} * {x} - {lean_int(b12)} * {y}) / {lean_int(det)})"
    v_expr = f"(({lean_int(b11)} * {y} - {lean_int(b21)} * {x}) / {lean_int(det)})"
    Iset = "{" + ", ".join(lean_int(i) for i in I) + "}"
    return f"""/-- {doc}`B = ({b11} {b12}; {b21} {b22})`, shifts `i ({r[0]}, {r[1]})`, `i ∈ {Iset}`. -/
def {name} : ECS where
  b11 := {lean_int(b11)}
  b12 := {lean_int(b12)}
  b21 := {lean_int(b21)}
  b22 := {lean_int(b22)}
  r1 := {lean_int(r[0])}
  r2 := {lean_int(r[1])}
  I := {Iset}
  det_ne := by norm_num
  cover := fun m n => ⟨{i_expr}, by simp only [mem_insert, mem_singleton]; omega,
    {u_expr}, {v_expr}, by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega
"""


def theta_nf(M, f, c, hname):
    """simp-lemma instance turning θ_M(f,c) into its canonical form; None if already canonical."""
    k = f // M
    e0 = f - M * k
    if e0 == 0 and c == 1:
        return f"θz' {hname} {lean_int(k)} (e := {lean_int(f)}) (by norm_num)", None
    if e0 > M - e0:
        g = M - e0
        E = -(M * c2(k + 1)) - e0 * k + M * k
        if c == 1:
            C = (-1) ** (k % 2)
            return (f"θ_nfr1 {hname} {g} {lean_int(k)} {lean_int(E)} {lean_int(C)} (e := {lean_int(f)}) (by norm_num) "
                    f"(by norm_num [c2]) (by norm_num)"), (g, E, C)
        else:
            C = 1
            return (f"θ_nfrm {hname} {g} {lean_int(k)} {lean_int(E)} {lean_int(C)} (e := {lean_int(f)}) (by norm_num) "
                    f"(by norm_num [c2]) (by norm_num)"), (g, E, C)
    if k == 0:
        return None, (e0, 0, 1)
    E = -(M * c2(k + 1)) - e0 * k + M * k
    C = ((-1) ** (k % 2)) * (c ** (k % 2))
    cc = "one_ne_zero" if c == 1 else "(by norm_num : (-1 : ℂ) ≠ 0)"
    return (f"θ_sh {hname} {lean_int(e0)} {lean_int(k)} {cc} {lean_int(E)} {lean_int(C)} (e := {lean_int(f)}) "
            f"(by norm_num) (by norm_num [c2]) (by norm_num)"), (e0, E, C)


def canon_terms(terms):
    """terms: list of (E, C, (M1,f1,c1), (M2,f2,c2)) -> dict (E, (M1,g1,c1), (M2,g2,c2)) -> coefficient"""
    out = {}
    for (E, C, t1, t2) in terms:
        tot_E, tot_C = E, C
        gs = []
        zero = False
        for (M, f, c) in (t1, t2):
            k = f // M
            e0 = f - M * k
            if e0 == 0 and c == 1:
                zero = True
                break
            Es = -(M * c2(k + 1)) - e0 * k + M * k
            Cs = ((-1) ** (k % 2)) * (c ** (k % 2))
            g = e0 if e0 <= M - e0 else M - e0
            tot_E += Es
            tot_C *= Cs
            gs.append((M, g, c))
        if zero:
            continue
        key = (tot_E, gs[0], gs[1])
        out[key] = out.get(key, 0) + tot_C
    return {k: v for k, v in out.items() if v}


def lean_side(cterms, hn):
    parts = []
    for (E, t1, t2), co in sorted(cterms.items()):
        th = f"(θ {hn[t1[0]]} {lean_int(t1[1])} {lean_int(t1[2])} * θ {hn[t2[0]]} {lean_int(t2[1])} {lean_int(t2[2])})"
        body = th if E == 0 else f"(mono {lean_int(E)} 1 * {th})"
        parts.append((co, body))
    s = ""
    for idx, (co, body) in enumerate(parts):
        a = abs(co)
        piece = body if a == 1 else f"{a} * {body}"
        if idx == 0:
            s = piece if co > 0 else f"-({piece})"
        else:
            s += (" + " if co > 0 else " - ") + piece
    return s if s else "0"


def gen_typeII(tag, form, spec1, spec2):
    A, Bq, C, d, e, de1, de2 = form
    out = []
    names = []
    sides = []
    hn = {}
    lemmas = set()
    for side, (b, r, lo) in zip("ab", (spec1, spec2)):
        det = b[0] * b[3] - b[1] * b[2]
        I = list(range(lo, lo + abs(det)))
        rr, II, terms, ok = typeII(A, Bq, C, d, e, de1, de2, b, r, None, [lo])
        assert ok, (tag, side)
        nm = f"B{tag.replace('.', '_')}{side}"
        names.append((nm, b, I))
        out.append(ecs_def(nm, b, r, I, f"Entry {tag}, side {side}: "))
        M1 = 2 * (A * b[0] ** 2 + 2 * Bq * b[0] * b[2] + C * b[2] ** 2)
        M2 = 2 * (A * b[1] ** 2 + 2 * Bq * b[1] * b[3] + C * b[3] ** 2)
        for M in (M1, M2):
            hn[M] = f"hm{M}"
        tl = []
        for (i, E, Cc, t1, t2) in terms:
            tl.append((E, Cc, t1, t2))
            for (M, f, c) in (t1, t2):
                lem, _ = theta_nf(M, f, c, f"hm{M}")
                if lem:
                    lemmas.add(lem)
        sides.append(((M1, M2), canon_terms(tl), len(I)))
    hdefs = "".join(f"private lemma hm{M} : 1 ≤ {M} := by norm_num\n" for M in sorted(hn))
    (M1a, M2a), ca, na = sides[0]
    (M1b, M2b), cb, nb = sides[1]
    lhs = lean_side(ca, hn)
    rhs = lean_side(cb, hn)
    Ba, Bb = names[0][0], names[1][0]
    nm_a = names[0]; nm_b = names[1]
    expand = lambda n: ", ".join(["sum_insert (by decide)"] * (n - 1) + ["sum_singleton"])
    proof = f"""theorem L{tag.replace('.', '_')} : {lhs} = {rhs} := by
  have h := qf_two {lean_int(A)} {lean_int(Bq)} {lean_int(C)} {lean_int(d)} {lean_int(e)} {lean_int(de1)} {lean_int(de2)} {Ba} {Bb}
    hm{M1a} hm{M2a} hm{M1b} hm{M2b} (by norm_num [{Ba}]) (by norm_num [{Ba}]) (by norm_num [{Ba}])
    (by norm_num [{Bb}]) (by norm_num [{Bb}]) (by norm_num [{Bb}])
  simp only [{Ba}, {Bb}] at h
  rw [{expand(na)}] at h
  rw [{expand(nb)}] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [{', '.join(sorted(lemmas)) if lemmas else 'mul_one'}] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
"""
    global LAST
    LAST = (ca, cb, hn)
    return hdefs + "\n" + "\n".join(out) + "\n" + proof


SPECS = {
    # tag: (form (A,Bq,C,d,e,δ1,δ2), (B, r, lo) side a, side b)
}




def auto(tag):
    """search both ECSs for an entry (see ecs.py jobs) and generate the Lean theta identity"""
    import ecs
    import io
    import contextlib
    jobs = {
        "3.4": ((3, 1, 4, 1, 4, 1, 0), [(6, 66), (10, 110)]),
        "3.6": ((2, 1, 5, 1, 2, 1, 0), [(10, 90), (18, 18)]),
        "3.9": ((3, 1, 5, 1, 4, 1, 0), [(20, 70), (6, 84)]),
        "3.10": ((3, 1, 5, 3, 1, 0, 1), [(10, 140), (12, 42)]),
        "3.19": ((5, 1, 8, 1, 8, 1, 0), [(10, 390), (30, 130)]),
        "3.28": ((5, 1, 7, 1, 7, 1, 0), [(20, 170), (10, 340)]),
        "3.5": ((4, 2, 5, 2, -3, 1, 1), [(10, 160), (8, 32)]),
        "3.11": ((4, 2, 7, 2, 7, 1, 0), [(30, 80), (8, 48)]),
        "3.12": ((5, 1, 5, 1, 5, 1, 0), [(10, 240), (16, 24)]),
    }
    form, tg = jobs[tag]
    specs = []
    for t in tg:
        best = None
        for tt in (t, (t[1], t[0])):
            with contextlib.redirect_stdout(io.StringIO()):
                best = ecs.search_II(tag, *form, tt)
            if best:
                break
        (sc, b, out) = best
        r, I = out[0], out[1]
        specs.append((b, r, I[0]))
    return gen_typeII(tag, form, specs[0], specs[1])





def poly(cterms, half, Xname="PowerSeries.X"):
    """PowerSeries polynomial in J's: halve moduli/exponents if half; coefficients divided by 2."""
    parts = []
    js = []
    for (E, t1, t2), co in sorted(cterms.items()):
        assert co % 2 == 0
        c = co // 2
        if half:
            assert E % 2 == 0 and all(x % 2 == 0 for x in (t1[0], t1[1], t2[0], t2[1]))
            E2, a1, m1, a2, m2 = E // 2, t1[1] // 2, t1[0] // 2, t2[1] // 2, t2[0] // 2
        else:
            E2, a1, m1, a2, m2 = E, t1[1], t1[0], t2[1], t2[0]
        js += [(a1, m1), (a2, m2)]
        body = f"(J {a1} {m1} * J {a2} {m2})"
        if E2:
            body = f"({Xname} ^ {E2} * {body})"
        parts.append((c, body))
    out = ""
    for idx, (c, body) in enumerate(parts):
        piece = body if abs(c) == 1 else f"{abs(c)} * {body}"
        if idx == 0:
            out = piece if c > 0 else f"-{piece}"
        else:
            out += (" + " if c > 0 else " - ") + piece
    return out, js


def gen_P(tag):
    ca, cb, hn = LAST
    name = tag.replace('.', '_')
    lq, jl = poly(ca, True)
    rq, jr = poly(cb, True)
    lt, _ = poly(ca, False)
    rt, _ = poly(cb, False)
    thetas = sorted(set((t[0], t[1]) for d in (ca, cb) for k in d for t in (k[1], k[2])))
    rws = ", ".join(f"θu' {hn[M]} {g} (e' := {g}) (by norm_num) (by norm_num) (by norm_num)" for (M, g) in thetas)
    sj = ", ".join(f"S_J 2 {a} {m} (by norm_num) (by norm_num)" for (a, m) in sorted(set(jl + jr)))
    return f"""
/-- the product form of `L{name}` in `ℤ⟦q⟧`. -/
theorem P{name} : {lq} = {rq} := by
  apply S_inj 2
  have h := L{name}
  rw [{rws}] at h
  have h' : ι (2 * ({lt})) = ι (2 * ({rt})) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, {sj},
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2
"""


if __name__ == "__main__" and len(sys.argv) == 5:
    import ast
    tag = sys.argv[1]
    form = ast.literal_eval(sys.argv[2])
    s1 = ast.literal_eval(sys.argv[3])
    s2 = ast.literal_eval(sys.argv[4])
    print(gen_typeII(tag, form, s1, s2))
    print(gen_P(tag))

if __name__ == "__main__" and len(sys.argv) == 3 and sys.argv[1] == "auto":
    print(auto(sys.argv[2]))
    print(gen_P(sys.argv[2]))


def gen_typeI(tag, N1, e1, w1, N2, e2, w2, b, lo):
    """Type I: θ_{N1}(e1,w1) θ_{N2}(e2,w2) split by one ECS with shifts i(1,0), i ∈ [lo, lo+|det|)."""
    det = b[0] * b[3] - b[1] * b[2]
    I = list(range(lo, lo + abs(det)))
    r, II, terms, ok = typeI(N1, e1, w1, N2, e2, w2, b, (1, 0), I)
    assert ok
    nm = f"B{tag.replace('.', '_')}"
    M1 = N1 * b[0] ** 2 + N2 * b[2] ** 2
    M2 = N1 * b[1] ** 2 + N2 * b[3] ** 2
    hn = {M: f"hm{M}" for M in (N1, N2, M1, M2)}
    lemmas = set()
    tl = []
    for (i, E, C, t1, t2) in terms:
        tl.append((E, C, t1, t2))
        for (M, f, c) in (t1, t2):
            lem, _ = theta_nf(M, f, c, f"hm{M}")
            if lem:
                lemmas.add(lem)
    cb = canon_terms(tl)
    rhs = lean_side(cb, hn)
    hdefs = "".join(f"private lemma hm{M} : 1 ≤ {M} := by norm_num\n" for M in sorted(hn))
    wl = lambda w: "1" if w == 1 else "(-1)"
    wne = lambda w: "one_ne_zero" if w == 1 else "(by norm_num : (-1 : ℂ) ≠ 0)"
    expand = ", ".join(["sum_insert (by decide)"] * (len(I) - 1) + ["sum_singleton"])
    proof = f"""theorem L{tag.replace('.', '_')} : θ hm{N1} {lean_int(e1)} {wl(w1)} * θ hm{N2} {lean_int(e2)} {wl(w2)} = {rhs} := by
  have h := θθ_lattice hm{N1} hm{N2} hm{M1} hm{M2} {lean_int(e1)} {lean_int(e2)} {wne(w1)} {wne(w2)} {nm} rfl rfl
    (by norm_num [{nm}]) (by norm_num [{nm}]) (by norm_num [{nm}])
  simp only [{nm}] at h
  rw [{expand}] at h
  norm_num [c2] at h
  simp only [{', '.join(sorted(lemmas)) if lemmas else 'mul_one'}] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
"""
    return hdefs + "\n" + ecs_def(nm, b, (1, 0), I, f"Entry {tag}: ") + "\n" + proof


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[1] == "typeI":
    import ast
    args = ast.literal_eval(sys.argv[3])
    print(gen_typeI(sys.argv[2], *args))
