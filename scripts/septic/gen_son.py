"""Generate Lean isometry identities P_U(a,b,c,d) = P_U'(a,b,c,d) for RamanujanTau/Septic/SonProof*.lean.

For an integer matrix M (n x n) with M^T M = 49 I and a subspace U of F_7^n with
rowspace(M mod 7) <= U <= ker(M mod 7), the map g = M/7 is an isometry of R^n carrying the lattice
L_U = {k in Z^n : k mod 7 in U} onto L_U' (U' = image).  Hence
    sum_{k in L_U} q^{|k|^2} = sum_{k in L_U'} q^{|k|^2},
and splitting both sides by k mod 7 gives P_U(T) = P_U'(T) with P_U = sum_{u in U} prod_i T_{u_i}.
In Lean: L_U is parametrised by z in Z^n via k = B_U z (B_U the pivot basis); the isometry becomes an
integer unimodular V with |B_U' V z|^2 = |B_U z|^2 (checked by `ring`)."""
import itertools
from collections import Counter
from fractions import Fraction as Fr
import sympy as sp

a, b, c, d = sp.symbols('a b c d')
TT = {0: a, 1: b, 2: c, 3: d}
cl = lambda r: min(r % 7, (-r) % 7)

def span(vecs, n):
    S = {(0,) * n}
    for v in vecs:
        v = tuple(x % 7 for x in v)
        if v in S: continue
        S = {tuple((x + k * y) % 7 for x, y in zip(s, v)) for s in S for k in range(7)}
    return S

def poly_of(S):
    return sp.expand(sum(sp.Mul(*[TT[cl(x)] for x in v]) for v in S))

def pivot_data(S, n):
    dim = {7 ** k: k for k in range(n + 1)}[len(S)]
    for P in itertools.combinations(range(n), dim):
        if len({tuple(v[i] for i in P) for v in S}) == len(S): break
    lut = {tuple(v[i] for i in P): v for v in S}
    forms = []
    for i in range(n):
        co = []
        for j in range(dim):
            e = [0] * dim; e[j] = 1
            co.append(lut[tuple(e)][i])
        forms.append(co)
    return list(P), forms

def basis_matrix(P, forms, n):
    """B with k = B z: k_{P_l} = z_{P_l}; k_i = sum_l forms[i][l] z_{P_l} + 7 z_i (i not pivot)."""
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        if i in P: B[i][i] = 1
        else:
            B[i][i] = 7
            for l, p in enumerate(P): B[i][p] = forms[i][l]
    return sp.Matrix(B)

def image_space(M, Ubasis, n):
    imgs = []
    for u in Ubasis:
        z = [sum(M[i][j] * u[j] for j in range(n)) for i in range(n)]
        assert all(x % 7 == 0 for x in z)
        imgs.append([x // 7 for x in z])
    for j in range(n): imgs.append([M[i][j] for i in range(n)])
    return span(imgs, n)

def comp(var, i, n):
    if n == 1: return var
    if i == 0: return var + ".1" * (n - 1)
    return var + ".1" * (n - 1 - i) + ".2"

def tup(xs):
    s = xs[0]
    for x in xs[1:]: s = f"({s}, {x})"
    return s

def typ(base, n):
    s = base
    for _ in range(n - 1): s = f"({s} × {base})" if False else f"{s} × {base}"
    # left-nested: ((A × A) × A) ...
    s = base
    for k in range(1, n): s = (f"({s})" if k > 1 else s) + f" × {base}"
    return s

def lin(coefs, xs):
    t = [f"({co}) * {x}" for co, x in zip(coefs, xs) if co != 0]
    return " + ".join(t) if t else "0"

def lean_poly(P):
    terms = []
    for mon, co in sp.Poly(P, a, b, c, d).terms():
        fac = []
        for v, e in zip(("T 0", "T 1", "T 2", "T 3"), mon):
            if e == 1: fac.append(v)
            elif e > 1: fac.append(f"{v} ^ {e}")
        terms.append(f"({co}) * " + " * ".join(fac))
    return "\n      + ".join(terms)

def side(nm, S, n, Zn, L):
    """emit defs/lemmas for one side; returns (P, forms, B, Idx type)."""
    P, forms = pivot_data(S, n)
    dd = len(P)
    B = basis_matrix(P, forms, n)
    zs = [comp("z", i, n) for i in range(n)]
    ms = [comp("m", i, n) for i in range(n)]
    Idx = typ("Fin 7", dd)
    sv = [f"(({comp('s', l, dd)} : ℕ) : ℤ)" for l in range(dd)]
    L.append(f"/-! #### side `{nm}`: pivots {P}, |U| = 7^{dd} -/")
    for i in range(n):
        L.append(f"def {nm}k{i} (z : {Zn}) : ℤ := {lin([B[i, j] for j in range(n)], zs)}")
    W = f"{nm}k0 z ^ 2"
    for i in range(1, n): W = f"{W} + {nm}k{i} z ^ 2"
    L.append(f"def {nm}W (z : {Zn}) : ℤ := {W}")
    for i in range(n):
        if i in P:
            L.append(f"def {nm}r{i} (s : {Idx}) : ℤ := {sv[P.index(i)]}")
        else:
            L.append(f"def {nm}r{i} (s : {Idx}) : ℤ := ({lin(forms[i], sv)}) % 7")
    G = f"(7 * {ms[0]} + {nm}r0 s) ^ 2"
    for i in range(1, n): G = f"({G} + (7 * {ms[i]} + {nm}r{i} s) ^ 2)" if False else f"{G} + (7 * {ms[i]} + {nm}r{i} s) ^ 2"
    L.append(f"def {nm}G (s : {Idx}) (m : {Zn}) : ℤ := {G}")
    # E : Zn ≃ Idx × Zn
    sdef = tup([f"⟨({comp('z', p, n)} % 7).toNat, by omega⟩" for p in P])
    L.append(f"def {nm}s (z : {Zn}) : {Idx} := {sdef}")
    for i in range(n):
        if i in P:
            L.append(f"def {nm}m{i} (z : {Zn}) : ℤ := {zs[i]} / 7")
        else:
            L.append(f"def {nm}m{i} (z : {Zn}) : ℤ := ({nm}k{i} z - {nm}r{i} ({nm}s z)) / 7")
    # inverse: z_p = 7 m_p + s_p ; z_i = (7 m_i + r_i(s) - sum_l f_il (7 m_p + s_p)) / 7
    inv = []
    for i in range(n):
        if i in P:
            l = P.index(i)
            inv.append(f"7 * {comp('q.2', i, n)} + (({comp('q.1', l, dd)} : ℕ) : ℤ)")
        else:
            zp = [f"(7 * {comp('q.2', p, n)} + (({comp('q.1', l, dd)} : ℕ) : ℤ))" for l, p in enumerate(P)]
            inv.append(f"(7 * {comp('q.2', i, n)} + {nm}r{i} q.1 - ({lin(forms[i], zp)})) / 7")
    kdefs = ", ".join(f"{nm}k{i}" for i in range(n))
    rdefs = ", ".join(f"{nm}r{i}" for i in range(n))
    mdefs = ", ".join(f"{nm}m{i}" for i in range(n))
    zpat = tup([f"z{i}" for i in range(n)])
    zpat_an = "⟨" * 0
    def anon(names):
        s = names[0]
        for x in names[1:]: s = f"⟨{s}, {x}⟩"
        return s
    spat = anon([f"⟨s{l}, hs{l}⟩" for l in range(dd)])
    mpat = anon([f"m{i}" for i in range(n)])
    zp = anon([f"z{i}" for i in range(n)])
    L.append(f"""
def {nm}E : {Zn} ≃ ({Idx}) × {Zn} where
  toFun z := ({nm}s z, {tup([f'{nm}m{i} z' for i in range(n)])})
  invFun q := {tup(inv)}
  left_inv z := by
    obtain {zp} := z
    simp only [{nm}s, {mdefs}, {kdefs}, {rdefs}, toNat_emod7]
    ext <;> simp only <;> omega
  right_inv q := by
    obtain ⟨{spat}, {mpat}⟩ := q
    simp only [{nm}s, {mdefs}, {kdefs}, {rdefs}]
    ext <;> simp only <;> omega
""")
    for i in range(n):
        L.append(f"lemma {nm}co{i} (z : {Zn}) : 7 * {nm}m{i} z + {nm}r{i} ({nm}s z) = {nm}k{i} z := by\n"
                 f"  obtain {zp} := z\n  simp only [{nm}s, {nm}m{i}, {kdefs}, {rdefs}, toNat_emod7]\n  omega")
    cos = ", ".join(f"{nm}co{i}" for i in range(n))
    L.append(f"""
lemma {nm}G_E (z : {Zn}) : {nm}G ({nm}E z).1 ({nm}E z).2 = {nm}W z := by
  simp only [{nm}G, {nm}E, Equiv.coe_fn_mk]
  rw [{cos}]
  rfl
""")
    # Good and cnt
    g = "(good_T _)"
    gp = g
    for i in range(1, n): gp = f"(good_prod _ _ {gp} (good_T _))"
    L.append(f"lemma good_{nm}G (s : {Idx}) : Good ({nm}G s) :=\n  {gp[1:-1]}")
    rws = []
    acc = g
    for i in range(1, n):
        rws.append(f"cnt_mul _ _ {acc} (good_T _)")
        acc = f"(good_prod _ _ {acc} (good_T _))"
    prodT = " * ".join(f"T ({nm}r{i} s)" for i in range(n))
    L.append(f"""
lemma cnt_{nm}G (s : {Idx}) : cnt ({nm}G s) = {prodT} := by
  simp only [T]
  rw [{(','+chr(10)+'    ').join(rws)}]
  rfl
""")
    PU = poly_of(S)
    L.append(f"noncomputable def {nm}poly : PowerSeries ℤ :=\n      {lean_poly(PU)}")
    fins = "Fin.sum_univ_seven"
    L.append(f"""
lemma {nm}sum : ∑ s : {Idx}, cnt ({nm}G s) = {nm}poly := by
  simp only [cnt_{nm}G, Fintype.sum_prod_type, {fins}, {rdefs}]
  norm_num [T4, T5, T6, {nm}poly]
  ring

lemma {nm}cnt : cnt {nm}W = {nm}poly := by
  rw [cnt_congr {nm}E (g := fun p : ({Idx}) × {Zn} => {nm}G p.1 p.2) {nm}G_E,
    cnt_fin_prod {nm}G good_{nm}G, {nm}sum]
""")
    return P, forms, B, PU

def gen_iso(tag, M, Ubasis, n=6):
    """returns (lean text, P_U - P_U')."""
    M = [list(r) for r in M]
    Mm = sp.Matrix(M)
    assert Mm.T * Mm == 49 * sp.eye(n)
    S = span(Ubasis, n)
    S2 = image_space(M, Ubasis, n)
    assert len(S) == len(S2)
    Zn = typ("ℤ", n)
    L = [f"/-! ### Isometry identity `{tag}` -/"]
    _, _, B1, P1 = side(f"{tag}a", S, n, Zn, L)
    _, _, B2, P2 = side(f"{tag}b", S2, n, Zn, L)
    V = B2.inv() * (Mm / 7) * B1
    Vi = B1.inv() * (Mm.T / 7) * B2
    assert all(x.is_integer for x in V) and all(x.is_integer for x in Vi)
    assert V * Vi == sp.eye(n)
    zs = [comp("z", i, n) for i in range(n)]
    def anon(names):
        s = names[0]
        for x in names[1:]: s = f"⟨{s}, {x}⟩"
        return s
    zp = anon([f"z{i}" for i in range(n)])
    Vt = tup([f"{lin([V[i, j] for j in range(n)], zs)}" for i in range(n)])
    Vit = tup([f"{lin([Vi[i, j] for j in range(n)], zs)}" for i in range(n)])
    L.append(f"""
/-- the isometry `M/7 : L_U → L_U'` in pivot coordinates (unimodular). -/
def {tag}V : {Zn} ≃ {Zn} where
  toFun z := {Vt}
  invFun z := {Vit}
  left_inv z := by
    obtain {zp} := z
    ext <;> simp only <;> ring
  right_inv z := by
    obtain {zp} := z
    ext <;> simp only <;> ring

lemma {tag}W_V (z : {Zn}) : {tag}bW ({tag}V z) = {tag}aW z := by
  obtain {zp} := z
  simp only [{tag}V, Equiv.coe_fn_mk, {tag}aW, {tag}bW, {', '.join(f'{tag}ak{i}' for i in range(n))}, {', '.join(f'{tag}bk{i}' for i in range(n))}]
  ring

/-- **isometry identity `{tag}`**: `P_U = P_U'`. -/
theorem {tag}_identity : {tag}apoly = {tag}bpoly := by
  rw [← {tag}acnt, ← {tag}bcnt]
  exact cnt_congr {tag}V {tag}W_V
""")
    return "\n".join(L), sp.expand(P1 - P2), P1, P2
