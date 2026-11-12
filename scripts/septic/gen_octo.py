"""Generate RamanujanTau/Septic/Octo{1,2}.lean: 8-dimensional lattice identities
   phi(q^7)^8 = sum_{v in W} prod_i T_{v_i}   (W a Lagrangian of F_7^8 with L_W = M Z^8, M^T M = 7 I)
The matrices M (columns) were found by random search (orthogonal norm-7 vectors of Z^8); see docs/SEPTIC_PAGE206.md."""
import itertools, sys
from collections import Counter
import sympy as sp
MATS = {
 1: [(1, 0, 1, 1, 0, 0, 2, 0), (0, 0, -1, 1, 1, 0, 0, 2), (0, 2, -1, -1, 0, 0, 1, 0), (2, -1, -1, -1, 0, 0, 0, 0),
     (0, 0, 1, -1, 0, -2, 0, 1), (1, 1, 1, 0, -1, 1, -1, 1), (0, 0, 1, -1, 2, 1, 0, 0), (1, 1, 0, 1, 1, -1, -1, -1)],
 2: [(-1, -1, -2, 0, 0, 1, 0, 0), (0, -1, 0, 0, 0, -1, -1, 2), (0, 0, 0, 1, -1, 0, 2, 1), (-1, 0, 0, -2, 0, -1, 1, 0),
     (-1, 1, 0, 0, -2, 0, -1, 0), (2, 0, -1, -1, -1, 0, 0, 0), (0, 0, 1, -1, 0, 2, 0, 1), (0, -2, 1, 0, -1, 0, 0, -1)],
}
p = 7
def analyse(cols):
    n = 8
    M = [[cols[j][i] for j in range(n)] for i in range(n)]  # M[i][j], k = M n
    for i in range(n):
        for j in range(n):
            assert sum(M[k][i] * M[k][j] for k in range(n)) == (7 if i == j else 0)
    # W = column span mod 7; find pivot coordinates P (4 of them) with W -> F_7^P bijective
    span = {tuple([0] * n)}
    for col in cols:
        span = {tuple((x + k * y) % p for x, y in zip(s, col)) for s in span for k in range(p)}
    assert len(span) == p ** 4
    for P in itertools.combinations(range(n), 4):
        if len({tuple(v[i] for i in P) for v in span}) == p ** 4:
            break
    # express each coordinate as a linear form in the pivots
    lut = {tuple(v[i] for i in P): v for v in span}
    forms = []
    for i in range(n):
        coef = []
        for j in range(4):
            e = [0] * 4; e[j] = 1
            coef.append(lut[tuple(e)][i])
        forms.append(coef)
    for key, v in lut.items():
        for i in range(n):
            assert sum(c * s for c, s in zip(forms[i], key)) % p == v[i]
    cls = lambda r: min(r % 7, (-r) % 7)
    cnt = Counter(tuple(sorted(cls(x) for x in v)) for v in span)
    return M, P, forms, cnt
a, b, c, d = sp.symbols('a b c d')
TT = {0: a, 1: b, 2: c, 3: d}
def poly_of(cnt):
    return sp.expand(sum(m * sp.Mul(*[TT[i] for i in k]) for k, m in cnt.items()))
def lean_poly(P):
    terms = []
    for mon, co in sp.Poly(P, a, b, c, d).terms():
        fac = []
        for v, e in zip(("T 0", "T 1", "T 2", "T 3"), mon):
            if e == 1: fac.append(v)
            elif e > 1: fac.append(f"{v} ^ {e}")
        terms.append(f"{co} * " + " * ".join(fac))
    return "\n      + ".join(terms)
def proj(i):  # component i of Z8 = ((((((ℤ×ℤ)×ℤ)×ℤ)×ℤ)×ℤ)×ℤ)×ℤ
    return "n" + ".1" * (7 - i) + (".2" if i > 0 else ".1" if False else "")
def comp(var, i):
    if i == 0: return var + ".1" * 7
    return var + ".1" * (7 - i) + ".2"
def gen(idx):
    M, P, forms, cnt = analyse(MATS[idx])
    nm = f"O{idx}"
    sidx = ["s.1.1.1", "s.1.1.2", "s.1.2", "s.2"]
    def r_expr(i, svars):
        f = forms[i]
        if i in P and f == [1 if j == P.index(i) else 0 for j in range(4)]:
            return f"(({svars[P.index(i)]} : ℕ) : ℤ)"
        lin = " + ".join(f"{f[j]} * (({svars[j]} : ℕ) : ℤ)" for j in range(4) if f[j] != 0) or "0"
        return f"(({lin}) % 7)"
    L = []
    L.append(f"/-- residue of coordinate `i` on `W_{idx}` in terms of the pivot residues. -/")
    for i in range(8):
        L.append(f"def {nm}r{i} (s : Idx4) : ℤ := {r_expr(i, sidx)}")
    # weight
    w = [f"(7 * {comp('m', i)} + {nm}r{i} st) ^ 2" for i in range(8)]
    expr = w[0]
    for i in range(1, 8): expr = f"({expr} + {w[i]})"
    L.append(f"def {nm}G (st : Idx4) (m : Z8) : ℤ := {expr}")
    # M n
    for i in range(8):
        lin = " + ".join(f"({M[i][j]}) * {comp('n', j)}" for j in range(8) if M[i][j] != 0)
        L.append(f"def {nm}k{i} (n : Z8) : ℤ := {lin}")
    # equivalence
    piv = [f"⟨({nm}k{P[j]} n % 7).toNat, by omega⟩" for j in range(4)]
    L.append(f"def {nm}s (n : Z8) : Idx4 := ((({piv[0]}, {piv[1]}), {piv[2]}), {piv[3]})")
    ms = [f"({nm}k{i} n - {nm}r{i} ({nm}s n)) / 7" for i in range(8)]
    mexpr = ms[0]
    for i in range(1, 8): mexpr = f"({mexpr}, {ms[i]})"
    kq = [f"(7 * {comp('q.2', i)} + {nm}r{i} q.1)" for i in range(8)]
    ns = []
    for j in range(8):
        lin = " + ".join(f"({M[i][j]}) * {kq[i]}" for i in range(8) if M[i][j] != 0)
        ns.append(f"({lin}) / 7")
    nexpr = ns[0]
    for j in range(1, 8): nexpr = f"({nexpr}, {ns[j]})"
    L.append(f"""def {nm}equiv : Z8 ≃ Idx4 × Z8 where
  toFun n := ({nm}s n, {mexpr})
  invFun q := {nexpr}""")
    L.append(f"""  left_inv n := by
    obtain ⟨⟨⟨⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := n
    simp only [{nm}s, {', '.join(f'{nm}k{i}' for i in range(8))}, {', '.join(f'{nm}r{i}' for i in range(8))}, toNat_emod7]
    ext <;> simp only <;> omega
  right_inv q := by
    obtain ⟨⟨⟨⟨⟨s0, h0⟩, ⟨s1, h1⟩⟩, ⟨s2, h2⟩⟩, ⟨s3, h3⟩⟩, ⟨⟨⟨⟨⟨⟨⟨m0, m1⟩, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩, m7⟩⟩ := q
    simp only [{nm}s, {', '.join(f'{nm}k{i}' for i in range(8))}, {', '.join(f'{nm}r{i}' for i in range(8))}, toNat_emod7]
    ext <;> simp only <;> omega""")
    L.append(f"""
lemma {nm}G_equiv (n : Z8) : {nm}G ({nm}equiv n).1 ({nm}equiv n).2 = W8 n := by
  obtain ⟨⟨⟨⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := n""")
    for i in range(8):
        L.append(f"  have h{i} : 7 * (({nm}equiv (((((((n0, n1), n2), n3), n4), n5), n6), n7)).2{'.1' * (7 - i) if i == 0 else ''}{'' if i == 0 else '.1' * (7 - i) + '.2'}) + {nm}r{i} ({nm}equiv (((((((n0, n1), n2), n3), n4), n5), n6), n7)).1 = {nm}k{i} (((((((n0, n1), n2), n3), n4), n5), n6), n7) := by\n    simp only [{nm}equiv, {nm}s, Equiv.coe_fn_mk, {', '.join(f'{nm}k{j}' for j in range(8))}, {', '.join(f'{nm}r{j}' for j in range(8))}, toNat_emod7]; omega")
    L.append(f"  simp only [{nm}G, W8] at *")
    L.append(f"  rw [h0, h1, h2, h3, h4, h5, h6, h7]")
    L.append(f"  simp only [{', '.join(f'{nm}k{j}' for j in range(8))}]")
    L.append(f"  ring")
    L.append(f"""
lemma good_{nm}G (st : Idx4) : Good ({nm}G st) :=
  good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _
    (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)

lemma cnt_{nm}G (st : Idx4) :
    cnt ({nm}G st) = T ({nm}r0 st) * T ({nm}r1 st) * T ({nm}r2 st) * T ({nm}r3 st)
      * T ({nm}r4 st) * T ({nm}r5 st) * T ({nm}r6 st) * T ({nm}r7 st) := by
  simp only [T]
  rw [cnt_mul _ _ (good_T _) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _))
      (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _))
      (good_T _)) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _)
      (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _
      (good_T _) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)]
  rfl

/-- the polynomial `P_{{W_{idx}}}(a,b,c,d)` (multiplicities of the class patterns on `W_{idx}`). -/
noncomputable def {nm}poly : PowerSeries ℤ :=
      {lean_poly(poly_of(cnt))}

/-- **8-dimensional lattice identity {idx}**: `φ(q⁷)⁸ = P_{{W_{idx}}}(a, b, c, d)`. -/
theorem octo{idx}_identity : ramF 7 7 ^ 8 = {nm}poly := by
  have e1 : cnt W8 = cnt (fun p : Idx4 × Z8 => {nm}G p.1 p.2) := cnt_congr {nm}equiv {nm}G_equiv
  have e2 : cnt (fun p : Idx4 × Z8 => {nm}G p.1 p.2) = ∑ st, cnt ({nm}G st) := cnt_fin_prod {nm}G good_{nm}G
  rw [Phi8_cnt, e1, e2]
  simp only [cnt_{nm}G, Fintype.sum_prod_type, Fin.sum_univ_seven, {', '.join(f'{nm}r{j}' for j in range(8))}]
  norm_num [T4, T5, T6, {nm}poly]
  ring
""")
    return "\n".join(L), poly_of(cnt)
HEADER = '''/-
# 8-dimensional lattice identities `φ(q⁷)⁸ = P_W(a, b, c, d)` — GENERATED by scripts/septic/gen_octo.py

For a Lagrangian `W ⊂ F₇⁸` (w.r.t. `Σ xᵢ²`) the lattice `L_W = {k ∈ ℤ⁸ : k mod 7 ∈ W}` satisfies
`L_W/√7` unimodular of rank 8, i.e. `≅ I₈` or `E₈`. For the two `W` below we exhibit `M ∈ M₈(ℤ)` with
`MᵀM = 7I` and `Mℤ⁸ = L_W`, so `Σ_{k∈L_W} q^{|k|²} = Σ_{n∈ℤ⁸} q^{7|n|²} = φ(q⁷)⁸`. Splitting `L_W` by `k mod 7`
gives `P_W(a,b,c,d) = Σ_{v∈W} Π T_{vᵢ}`. Same method as `Quaternion.lean`, with 7⁴ = 2401 cosets.
-/
import RamanujanTau.Septic.Quaternion

set_option autoImplicit false
set_option maxHeartbeats 0

namespace RamanujanTau.Septic

open PowerSeries Finset

abbrev Z8 := ((((((ℤ × ℤ) × ℤ) × ℤ) × ℤ) × ℤ) × ℤ) × ℤ
abbrev Idx4 := ((Fin 7 × Fin 7) × Fin 7) × Fin 7

def W8 (n : Z8) : ℤ :=
  ((((((7 * n.1.1.1.1.1.1.1 ^ 2 + 7 * n.1.1.1.1.1.1.2 ^ 2) + 7 * n.1.1.1.1.1.2 ^ 2) + 7 * n.1.1.1.1.2 ^ 2)
    + 7 * n.1.1.1.2 ^ 2) + 7 * n.1.1.2 ^ 2) + 7 * n.1.2 ^ 2) + 7 * n.2 ^ 2

lemma Phi8_cnt : ramF 7 7 ^ 8 = cnt W8 := by
  have g := good_seven_sq
  rw [ramF77_eq, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_one,
    cnt_mul _ _ g g, cnt_mul _ _ (good_prod _ _ g g) g,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ g g) g) g,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ g g) g) g) g,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ g g) g) g) g) g,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ g g) g) g) g) g) g,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ g g)
      g) g) g) g) g) g]
  rfl

'''
if __name__ == "__main__":
    which = [int(x) for x in sys.argv[1:]] or [1, 2]
    Q4 = a**4 + 24*a*b*c*d + 8*(b**3*c + c**3*d + d**3*b)
    for idx in which:
        body, P = gen(idx)
        D = sp.factor(P - sp.expand(Q4**2))
        print(f"W_{idx}: P_W - Q4^2 =", D)
        out = f"RamanujanTau/Septic/Octo{idx}.lean"
        hdr = HEADER if idx == 1 else HEADER.replace("import RamanujanTau.Septic.Quaternion", "import RamanujanTau.Septic.Octo1").split("abbrev Z8")[0] + "\n"
        open(out, "w").write(hdr + body + "\nend RamanujanTau.Septic\n")
        print("wrote", out)
