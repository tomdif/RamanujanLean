import RamanujanTau.Igusa.Core
import RamanujanTau.Igusa.Serre

/-!
# Igusa's theorem over a field of characteristic `p`, and supersingular points

`F` is a field of characteristic `p ≥ 5`, `AF = Ā ⊗ F` (`Ā = ModP.hasseBar`).
Isobaric polynomials are read in two affine charts of the weighted projective line:
* `chartT P = P(t, 1) ∈ F[t]` (covers all points with `x₁ ≠ 0`, i.e. all `j ≠ 1728` and `j = ∞`),
* `chartS P = P(1, s) ∈ F[s]` (we only use its behaviour at `s = 0`, the point `(1,0)`, `j = 1728`).
On isobaric polynomials both charts are injective on monomials.

From Ramanujan's equations (`RamanujanODE`, the only hypothesis) the Serre derivation gives
`∂Ā = B̄`, `∂B̄ = −X₀Ā` (`Serre.lean`); in the `t`-chart this is the system
`b = −4(1−t³) a' + t² a`, `−t a = −4(1−t³) b' − t² b`, and `Core.not_sq_dvd` gives

* `igusa_chartT`: `Ā(t,1)` has no double root `t₀` with `t₀³ ≠ 1`;
* `chartT_ne_of_cube_eq_one`: `Ā(t₀,1) ≠ 0` when `t₀³ = 1` (these are the cusp: `x₀³ = x₁²`);
* `igusa_chartS`: `s² ∤ Ā(1,s)`, so `eA ≤ 1` (`eA_le_one`) — the point `(1,0)` is at most a simple zero.

Monomial complement: `dA` is the largest `X₀`-exponent of `Ā` and `eA = (p−1−4dA)/6` the matching
`X₁`-exponent (`X₀^{dA} X₁^{eA}` is the leading monomial for lex with `X₀ > X₁`). For a weight `k`,
`S p hp5 k` is the set of weight-`k` monomials *not divisible* by `X₀^{dA} X₁^{eA}`.

* **`exists_ss_nonvanishing`** (`F` algebraically closed): a nonzero `β ∈ F[X₀,X₁]` supported on
  `S p hp5 k` does not vanish at some supersingular point: `∃ x, Ā(x) = 0, x₀³ ≠ x₁², β(x) ≠ 0`.
* **`exists_ss`**: supersingular points exist.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Igusa
open MvPolynomial ModP

variable {F : Type*} [Field F]

/-! ### Charts -/

/-- `P(t, 1)`. -/
noncomputable def chartT : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval (![Polynomial.X, 1] : Fin 2 → Polynomial F)

/-- `P(1, s)`. -/
noncomputable def chartS : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval (![1, Polynomial.X] : Fin 2 → Polynomial F)

@[simp] lemma chartT_X0 : chartT (X 0 : MvPolynomial (Fin 2) F) = Polynomial.X := by simp [chartT]
@[simp] lemma chartT_X1 : chartT (X 1 : MvPolynomial (Fin 2) F) = 1 := by simp [chartT]
@[simp] lemma chartS_X0 : chartS (X 0 : MvPolynomial (Fin 2) F) = 1 := by simp [chartS]
@[simp] lemma chartS_X1 : chartS (X 1 : MvPolynomial (Fin 2) F) = Polynomial.X := by simp [chartS]

lemma chartT_pderiv0 (P : MvPolynomial (Fin 2) F) :
    chartT (pderiv 0 P) = Polynomial.derivative (chartT P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [chartT]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz]
    simp only [chartT] at hp ⊢
    fin_cases i
    · simp [hp, pderiv_X]; ring
    · simp [hp, pderiv_X]

lemma chartS_pderiv1 (P : MvPolynomial (Fin 2) F) :
    chartS (pderiv 1 P) = Polynomial.derivative (chartS P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [chartS]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz]
    simp only [chartS] at hp ⊢
    fin_cases i
    · simp [hp, pderiv_X]
    · simp [hp, pderiv_X]; ring

lemma eval_chartT (P : MvPolynomial (Fin 2) F) (t : F) :
    (chartT P).eval t = eval ![t, 1] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [chartT]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [chartT] at hp ⊢
    fin_cases i <;> simp [hp]

lemma eval_chartS (P : MvPolynomial (Fin 2) F) (s : F) :
    (chartS P).eval s = eval ![1, s] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [chartS]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [chartS] at hp ⊢
    fin_cases i <;> simp [hp]

lemma chartT_eq_sum (P : MvPolynomial (Fin 2) F) :
    chartT P = ∑ s ∈ P.support, Polynomial.C (P.coeff s) * Polynomial.X ^ (s 0) := by
  conv_lhs => rw [P.as_sum]
  rw [chartT, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp [Polynomial.algebraMap_eq]

lemma chartS_eq_sum (P : MvPolynomial (Fin 2) F) :
    chartS P = ∑ s ∈ P.support, Polynomial.C (P.coeff s) * Polynomial.X ^ (s 1) := by
  conv_lhs => rw [P.as_sum]
  rw [chartS, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp [Polynomial.algebraMap_eq]

lemma weight_eq {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : Iso P k) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ P.support) : 4 * s 0 + 6 * s 1 = k := by
  have := hP (mem_support_iff.mp hs); rwa [weight_wt] at this

lemma eq_of_weight {s s' : Fin 2 →₀ ℕ} (h : 4 * s 0 + 6 * s 1 = 4 * s' 0 + 6 * s' 1)
    (h0 : s 0 = s' 0) : s = s' := by
  ext i; fin_cases i
  · exact h0
  · simp; omega

/-- On an isobaric polynomial the `t`-chart reads off coefficients. -/
lemma coeff_chartT {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : Iso P k) {s : Fin 2 →₀ ℕ}
    (hs : 4 * s 0 + 6 * s 1 = k) : (chartT P).coeff (s 0) = P.coeff s := by
  rw [chartT_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · simp
  · intro s' hs' hne
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    exact hne (eq_of_weight (by rw [weight_eq hP hs', hs]) h.symm)
  · intro hs'; rw [notMem_support_iff.mp hs']; simp

lemma coeff_chartT_eq_zero (P : MvPolynomial (Fin 2) F) {j : ℕ} (hj : ∀ s ∈ P.support, s 0 ≠ j) :
    (chartT P).coeff j = 0 := by
  rw [chartT_eq_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm (hj s hs))]

lemma natDegree_chartT_le (P : MvPolynomial (Fin 2) F) {N : ℕ} (h : ∀ s ∈ P.support, s 0 ≤ N) :
    (chartT P).natDegree ≤ N := by
  rw [chartT_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (h s hs)

lemma natDegree_chartS_le (P : MvPolynomial (Fin 2) F) {N : ℕ} (h : ∀ s ∈ P.support, s 1 ≤ N) :
    (chartS P).natDegree ≤ N := by
  rw [chartS_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (h s hs)

/-- Euler in the `t`-chart: `P(t,1)` determines `∂P(t,1)`. -/
lemma chartT_serreD {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : Iso P k) :
    chartT (serreD P) = -4 * (1 - Polynomial.X ^ 3) * Polynomial.derivative (chartT P)
      - (k : Polynomial F) * Polynomial.X ^ 2 * chartT P := by
  have he := congrArg chartT (euler hP)
  simp only [map_add, map_mul, map_ofNat, map_natCast, chartT_X0, chartT_X1, chartT_pderiv0] at he
  simp only [serreD, map_sub, map_neg, map_mul, map_ofNat, map_pow, chartT_X0, chartT_X1,
    chartT_pderiv0]
  linear_combination (-(Polynomial.X : Polynomial F) ^ 2) * he

lemma chartS_serreD {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : Iso P k) :
    chartS (serreD P) = -6 * (1 - Polynomial.X ^ 2) * Polynomial.derivative (chartS P)
      - (k : Polynomial F) * Polynomial.X * chartS P := by
  have he := congrArg chartS (euler hP)
  simp only [map_add, map_mul, map_ofNat, map_natCast, chartS_X0, chartS_X1, chartS_pderiv1] at he
  simp only [serreD, map_sub, map_neg, map_mul, map_ofNat, map_pow, chartS_X0, chartS_X1,
    chartS_pderiv1]
  linear_combination (-(Polynomial.X : Polynomial F)) * he

/-- Isobaric scaling `P(u⁴x₀, u⁶x₁) = u^k P(x₀, x₁)`. -/
lemma eval_scale {P : MvPolynomial (Fin 2) F} {k : ℕ} (hP : Iso P k) (u x₀ x₁ : F) :
    eval ![u ^ 4 * x₀, u ^ 6 * x₁] P = u ^ k * eval ![x₀, x₁] P := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two, ← weight_eq hP hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-! ### The Hasse polynomial over `F` -/

section Hasse
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]

/-- `Ā ⊗ F`. -/
noncomputable def AF (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p) :
    MvPolynomial (Fin 2) F :=
  MvPolynomial.map (ZMod.castHom (dvd_refl p) F) (hasseBar p hp5)

/-- `B̄ ⊗ F = ∂(Ā ⊗ F)`. -/
noncomputable def BF (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p) :
    MvPolynomial (Fin 2) F :=
  MvPolynomial.map (ZMod.castHom (dvd_refl p) F) (hasseB p hp5)

variable (hp5 : 5 ≤ p)
include hp5

lemma iso_AF : Iso (AF F p hp5) (p - 1) := iso_map _ (iso_hasseBar hp5)
lemma iso_BF : Iso (BF F p hp5) (p + 1) := iso_map _ (iso_hasseB hp5)

lemma BF_eq : BF F p hp5 = serreD (AF F p hp5) := by
  rw [BF, AF, hasseB, map_serreD]

lemma serreD_BF (hR : RamanujanODE) : serreD (BF F p hp5) = -(X 0 * AF F p hp5) := by
  rw [BF, ← map_serreD, serreD_hasseB hR hp5, AF]; simp

lemma eval_one_AF : eval ![1, 1] (AF F p hp5) = 1 := by
  have h := constantCoeff_ev (ZMod p) (hasseBar p hp5)
  rw [ev_hasseBar, map_one] at h
  rw [AF, eval_map]
  have h2 := MvPolynomial.eval₂_comp_left (ZMod.castHom (dvd_refl p) F) (RingHom.id _) one2
    (hasseBar p hp5)
  have e : (⇑(ZMod.castHom (dvd_refl p) F) ∘ one2) = ![1, 1] := by
    ext i; fin_cases i <;> simp [one2]
  rw [e, RingHom.comp_id] at h2
  rw [← h2]
  have := congrArg (ZMod.castHom (dvd_refl p) F) h
  rw [map_one] at this
  exact this.symm

lemma support_AF : (AF F p hp5).support = (hasseBar p hp5).support := by
  rw [AF]; exact support_map_of_injective _ (ZMod.castHom (dvd_refl p) F).injective

lemma coeff_AF (s : Fin 2 →₀ ℕ) : (AF F p hp5).coeff s ≠ 0 ↔ (hasseBar p hp5).coeff s ≠ 0 := by
  rw [← mem_support_iff, ← mem_support_iff, support_AF]

lemma four_ne_zero' : (4 : F) ≠ 0 := by
  have := natCast_ne_zero_of_lt (F := F) (p := p) (n := 4) (by norm_num) (by omega)
  exact_mod_cast this

lemma six_ne_zero' : (6 : F) ≠ 0 := by
  have h2 := natCast_ne_zero_of_lt (F := F) (p := p) (n := 2) (by norm_num) (by omega)
  have h3 := natCast_ne_zero_of_lt (F := F) (p := p) (n := 3) (by norm_num) (by omega)
  rw [show (6 : F) = ((2 : ℕ) : F) * ((3 : ℕ) : F) by push_cast; norm_num]
  exact mul_ne_zero h2 h3
  
lemma natCast_PF (k : ℕ) (hk : k = p - 1 ∨ k = p + 1) :
    (k : Polynomial F) = if k = p - 1 then -1 else 1 := by
  have hp1 : 1 ≤ p := by omega
  have hcp : ((p : ℕ) : Polynomial F) = 0 := by
    rw [← map_natCast (Polynomial.C (R := F)), CharP.cast_eq_zero, map_zero]
  rcases hk with rfl | rfl
  · rw [if_pos rfl, Nat.cast_sub hp1, hcp]; simp
  · rw [if_neg (by omega), Nat.cast_add, hcp]; simp

/-- The `t`-chart system for `a = Ā(t,1)`, `b = B̄(t,1)`. -/
lemma chartT_system (hR : RamanujanODE) :
    chartT (BF F p hp5) = (-4 * (1 - Polynomial.X ^ 3)) * Polynomial.derivative (chartT (AF F p hp5))
        + Polynomial.X ^ 2 * chartT (AF F p hp5) ∧
    -(Polynomial.X * chartT (AF F p hp5)) =
      (-4 * (1 - Polynomial.X ^ 3)) * Polynomial.derivative (chartT (BF F p hp5))
        + (-Polynomial.X ^ 2) * chartT (BF F p hp5) := by
  constructor
  · rw [BF_eq hp5, chartT_serreD (iso_AF hp5), natCast_PF hp5 _ (Or.inl rfl), if_pos rfl]; ring
  · have h := chartT_serreD (F := F) (iso_BF hp5)
    rw [serreD_BF hp5 hR, natCast_PF hp5 _ (Or.inr rfl), if_neg (by omega)] at h
    simp only [map_neg, map_mul, chartT_X0] at h
    rw [h]; ring

lemma chartS_system (hR : RamanujanODE) :
    chartS (BF F p hp5) = (-6 * (1 - Polynomial.X ^ 2)) * Polynomial.derivative (chartS (AF F p hp5))
        + Polynomial.X * chartS (AF F p hp5) ∧
    -(1 * chartS (AF F p hp5)) =
      (-6 * (1 - Polynomial.X ^ 2)) * Polynomial.derivative (chartS (BF F p hp5))
        + (-Polynomial.X) * chartS (BF F p hp5) := by
  constructor
  · rw [BF_eq hp5, chartS_serreD (iso_AF hp5), natCast_PF hp5 _ (Or.inl rfl), if_pos rfl]; ring
  · have h := chartS_serreD (F := F) (iso_BF hp5)
    rw [serreD_BF hp5 hR, natCast_PF hp5 _ (Or.inr rfl), if_neg (by omega)] at h
    simp only [map_neg, map_mul, chartS_X0] at h
    rw [h]; ring

lemma chartT_AF_ne_zero : chartT (AF F p hp5) ≠ 0 := by
  intro h
  have := eval_chartT (AF F p hp5) 1
  rw [h, Polynomial.eval_zero, eval_one_AF hp5] at this
  exact zero_ne_one this

lemma chartS_AF_ne_zero : chartS (AF F p hp5) ≠ 0 := by
  intro h
  have := eval_chartS (AF F p hp5) 1
  rw [h, Polynomial.eval_zero, eval_one_AF hp5] at this
  exact zero_ne_one this

lemma natDegree_chartT_AF_lt : (chartT (AF F p hp5)).natDegree < p := by
  have := natDegree_chartT_le (AF F p hp5) (N := p - 1) fun s hs => by
    have := weight_eq (iso_AF (F := F) hp5) hs; omega
  omega

lemma natDegree_chartS_AF_lt : (chartS (AF F p hp5)).natDegree < p := by
  have := natDegree_chartS_le (AF F p hp5) (N := p - 1) fun s hs => by
    have := weight_eq (iso_AF (F := F) hp5) hs; omega
  omega

/-- **Igusa (finite part).** `Ā(t,1)` has no double root `t₀` with `t₀³ ≠ 1`. -/
theorem igusa_chartT (hR : RamanujanODE) {t₀ : F} (ht : t₀ ^ 3 ≠ 1) :
    ¬ (Polynomial.X - Polynomial.C t₀) ^ 2 ∣ chartT (AF F p hp5) := by
  obtain ⟨h1, h2⟩ := chartT_system (F := F) hp5 hR
  refine not_sq_dvd (p := p) (chartT_AF_ne_zero hp5) (natDegree_chartT_AF_lt hp5) ?_ h1 h2
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_ofNat, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_ne_zero (neg_ne_zero.mpr (four_ne_zero' (F := F) hp5)) (sub_ne_zero.mpr (Ne.symm ht))

/-- **Igusa at `(1,0)`.** `s² ∤ Ā(1,s)`. -/
theorem igusa_chartS (hR : RamanujanODE) : ¬ Polynomial.X ^ 2 ∣ chartS (AF F p hp5) := by
  obtain ⟨h1, h2⟩ := chartS_system (F := F) hp5 hR
  have := not_sq_dvd (p := p) (t₀ := 0) (chartS_AF_ne_zero hp5) (natDegree_chartS_AF_lt hp5) ?_ h1 h2
  · simpa using this
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_ofNat, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  simpa using six_ne_zero' (F := F) hp5

/-- `Ā` does not vanish on the cusp `x₀³ = x₁²` (in the chart: `t₀³ = 1`). -/
theorem chartT_ne_of_cube_eq_one {t₀ : F} (ht : t₀ ^ 3 = 1) : eval ![t₀, 1] (AF F p hp5) ≠ 0 := by
  have h := eval_scale (iso_AF hp5) t₀ 1 1
  have e4 : t₀ ^ 4 * 1 = t₀ := by rw [mul_one, pow_succ, ht, one_mul]
  have e6 : t₀ ^ 6 * 1 = 1 := by rw [mul_one, show 6 = 3 * 2 by rfl, pow_mul, ht, one_pow]
  rw [e4, e6, eval_one_AF hp5, mul_one] at h
  rw [h]
  refine pow_ne_zero _ ?_
  rintro rfl; simp at ht

/-! ### The leading monomial -/

omit [CharP F p] in
lemma hasseBar_ne_zero : hasseBar p hp5 ≠ 0 := by
  intro h; have := ev_hasseBar hp5; rw [h, map_zero] at this; exact zero_ne_one this

omit hp5 in
/-- Largest `X₀`-exponent in `Ā`. -/
noncomputable def dA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : ℕ := (hasseBar p hp5).support.sup fun s => s 0

omit hp5 in
/-- The matching `X₁`-exponent. -/
noncomputable def eA (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : ℕ := (p - 1 - 4 * dA p hp5) / 6

omit [CharP F p] in
lemma weight_hasseBar {s : Fin 2 →₀ ℕ} (hs : s ∈ (hasseBar p hp5).support) : 4 * s 0 + 6 * s 1 = p - 1 := by
  have := iso_hasseBar hp5 (mem_support_iff.mp hs); rwa [weight_wt] at this

omit [CharP F p] in
lemma exists_lead : ∃ s₀ ∈ (hasseBar p hp5).support, s₀ 0 = dA p hp5 ∧ s₀ 1 = eA p hp5 := by
  have hne : (hasseBar p hp5).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]; exact hasseBar_ne_zero hp5
  obtain ⟨s₀, hs₀, h⟩ := Finset.exists_mem_eq_sup _ hne fun s => s 0
  refine ⟨s₀, hs₀, h.symm, ?_⟩
  have := weight_hasseBar hp5 hs₀
  simp only [eA, dA, h]; omega

omit [CharP F p] in
lemma le_dA {s : Fin 2 →₀ ℕ} (hs : s ∈ (hasseBar p hp5).support) : s 0 ≤ dA p hp5 :=
  Finset.le_sup (f := fun s => s 0) hs

omit [CharP F p] in
lemma eA_le {s : Fin 2 →₀ ℕ} (hs : s ∈ (hasseBar p hp5).support) : eA p hp5 ≤ s 1 := by
  obtain ⟨s₀, hs₀, h0, h1⟩ := exists_lead hp5
  have w := weight_hasseBar hp5 hs
  have w0 := weight_hasseBar hp5 hs₀
  have := le_dA hp5 hs
  omega

omit [CharP F p] in
lemma dA_eA : 4 * dA p hp5 + 6 * eA p hp5 = p - 1 := by
  obtain ⟨s₀, hs₀, h0, h1⟩ := exists_lead hp5
  rw [← h0, ← h1]; exact weight_hasseBar hp5 hs₀

/-- **Igusa at `(1,0)`, monomial form:** `X₁² ∤ Ā`, i.e. `eA ≤ 1`. -/
theorem eA_le_one (F : Type*) [Field F] [CharP F p] (hR : RamanujanODE) : eA p hp5 ≤ 1 := by
  by_contra hcon
  push Not at hcon
  apply igusa_chartS (F := F) hp5 hR
  rw [chartS_eq_sum]
  refine Finset.dvd_sum fun s hs => ?_
  rw [support_AF] at hs
  exact dvd_mul_of_dvd_right (pow_dvd_pow _ (le_trans hcon (eA_le hp5 hs))) _

lemma natDegree_chartT_AF : (chartT (AF F p hp5)).natDegree = dA p hp5 := by
  obtain ⟨s₀, hs₀, h0, h1⟩ := exists_lead hp5
  apply le_antisymm
  · exact natDegree_chartT_le _ fun s hs => le_dA hp5 (by rwa [support_AF] at hs)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [← h0, coeff_chartT (iso_AF hp5) (weight_hasseBar hp5 hs₀)]
    exact (coeff_AF hp5 s₀).mpr (mem_support_iff.mp hs₀)

/-! ### The monomial complement and supersingular points -/

omit [CharP F p] hp5 in
/-- Weight-`k` monomials not divisible by the leading monomial `X₀^{dA} X₁^{eA}` of `Ā`. -/
def S (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (k : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {s | 4 * s 0 + 6 * s 1 = k ∧ ¬ (dA p hp5 ≤ s 0 ∧ eA p hp5 ≤ s 1)}

/-- The roots of `Ā(t,1)` are simple and avoid the cusp. -/
lemma roots_nodup (hR : RamanujanODE) : (chartT (AF F p hp5)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro t
  rw [Polynomial.count_roots]
  by_contra h
  push Not at h
  have hdvd : (Polynomial.X - Polynomial.C t) ^ 2 ∣ chartT (AF F p hp5) :=
    (Polynomial.le_rootMultiplicity_iff (chartT_AF_ne_zero hp5)).mp h
  have hroot : (chartT (AF F p hp5)).IsRoot t := by
    rw [← Polynomial.dvd_iff_isRoot]
    exact (dvd_pow_self _ two_ne_zero).trans hdvd
  have ht : t ^ 3 ≠ 1 := by
    intro ht
    apply chartT_ne_of_cube_eq_one hp5 ht
    rw [← eval_chartT]; exact hroot
  exact igusa_chartT hp5 hR ht hdvd

/-- **Supersingular detection over an algebraically closed field.** -/
theorem exists_ss_nonvanishing [IsAlgClosed F] (hR : RamanujanODE) {k : ℕ}
    {β : MvPolynomial (Fin 2) F} (hβ : β ≠ 0) (hS : (β.support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 k) :
    ∃ x : Fin 2 → F, eval x (AF F p hp5) = 0 ∧ x 0 ^ 3 - x 1 ^ 2 ≠ 0 ∧ eval x β ≠ 0 := by
  have hβiso : Iso β k := fun s hs => by
    rw [weight_wt]; exact (hS (mem_support_iff.mpr hs)).1
  by_cases hinf : 1 ≤ eA p hp5 ∧ ∃ s ∈ β.support, s 1 = 0
  · -- the point `(1, 0)`
    obtain ⟨he, s, hs, hs1⟩ := hinf
    refine ⟨![1, 0], ?_, by simp, ?_⟩
    · rw [eval_eq']
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [support_AF] at ht
      have := eA_le hp5 ht
      rw [Fin.prod_univ_two]
      simp [zero_pow (by omega : t 1 ≠ 0)]
    · rw [eval_eq', Finset.sum_eq_single s]
      · rw [Fin.prod_univ_two]; simp [hs1, mem_support_iff.mp hs]
      · intro t ht hne
        have ht1 : t 1 ≠ 0 := by
          intro ht1
          exact hne (eq_of_weight (by rw [weight_eq hβiso ht, weight_eq hβiso hs])
            (by have := weight_eq hβiso ht; have := weight_eq hβiso hs; omega))
        rw [Fin.prod_univ_two]; simp [zero_pow ht1]
      · intro h; exact absurd hs h
  · -- a finite point `(t₀, 1)`
    have hlow : ∀ s ∈ β.support, s 0 < dA p hp5 := by
      intro s hs
      have hSs := (hS hs).2
      have h1 := eA_le_one hp5 F hR
      by_contra hcon
      push Not at hcon
      apply hSs ⟨hcon, ?_⟩
      by_cases he : 1 ≤ eA p hp5
      · have : s 1 ≠ 0 := fun h0 => hinf ⟨he, s, hs, h0⟩
        omega
      · omega
    set a := chartT (AF F p hp5)
    set b := chartT β
    have hb0 : b ≠ 0 := by
      obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr ((not_congr support_eq_empty).mpr hβ)
      intro h
      have := coeff_chartT hβiso (weight_eq hβiso hs)
      rw [← show b = chartT β from rfl, h, Polynomial.coeff_zero] at this
      exact mem_support_iff.mp hs this.symm
    have hbdeg : b.natDegree < dA p hp5 ∨ dA p hp5 = 0 := by
      rcases Nat.eq_zero_or_pos (dA p hp5) with h | h
      · exact Or.inr h
      · left
        have : b.natDegree ≤ dA p hp5 - 1 := natDegree_chartT_le β fun s hs => by
          have := hlow s hs; omega
        omega
    have hex : ∃ t, a.IsRoot t ∧ ¬ b.IsRoot t := by
      by_contra hcon
      push Not at hcon
      have hle : a.roots ≤ b.roots := by
        rw [Multiset.le_iff_subset (roots_nodup hp5 hR)]
        intro t ht
        rw [Polynomial.mem_roots hb0]
        exact hcon t ((Polynomial.mem_roots (chartT_AF_ne_zero hp5)).mp ht)
      have h1 := Multiset.card_le_card hle
      rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_chartT_AF hp5] at h1
      have h2 := Polynomial.card_roots' b
      rcases hbdeg with h | h
      · omega
      · -- `dA = 0`: then `β` has no monomials at all
        obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr ((not_congr support_eq_empty).mpr hβ)
        have := hlow s hs; omega
    obtain ⟨t, hta, htb⟩ := hex
    have ht3 : t ^ 3 ≠ 1 := by
      intro ht
      apply chartT_ne_of_cube_eq_one hp5 ht
      rw [← eval_chartT]; exact hta
    refine ⟨![t, 1], ?_, ?_, ?_⟩
    · rw [← eval_chartT]; exact hta
    · simpa [sub_eq_zero] using ht3
    · rw [← eval_chartT]; exact htb

/-- **Supersingular points exist** over an algebraically closed field of characteristic `p`. -/
theorem exists_ss [IsAlgClosed F] (hR : RamanujanODE) :
    ∃ x : Fin 2 → F, eval x (AF F p hp5) = 0 ∧ x 0 ^ 3 - x 1 ^ 2 ≠ 0 := by
  have hS : ((1 : MvPolynomial (Fin 2) F).support : Set (Fin 2 →₀ ℕ)) ⊆ S p hp5 0 := by
    intro s hs
    rw [Finset.mem_coe, support_one, Finset.mem_singleton] at hs
    subst hs
    refine ⟨by simp, fun ⟨h0, h1⟩ => ?_⟩
    have := dA_eA hp5
    simp at h0 h1
    omega
  obtain ⟨x, h1, h2, -⟩ := exists_ss_nonvanishing hp5 hR one_ne_zero hS
  exact ⟨x, h1, h2⟩

end Hasse

end Igusa
