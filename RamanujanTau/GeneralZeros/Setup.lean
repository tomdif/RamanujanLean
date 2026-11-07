/-
# Setup for the zeros of `L(f,s)`, `f ∈ S_k(SL₂(ℤ))` an arbitrary nonzero cusp form

* `weight_ge`, `weight_even`: `f ≠ 0 ⇒ k ≥ 12`, `k` even.
* `exists_sigma_normalized`: with `n₀` the first index where `a_f(n₀) ≠ 0`,
  `G(s) = n₀^s a_f(n₀)^{−1} L(f,s)` satisfies `|G(s) − 1| ≤ ρ` on a whole half-plane
  `Re s ≥ σ₁` (the half-plane version of `HafnerGeneral.exists_normalized`).
* `Lam_ne_zero_right`, `Lam_ne_zero_left`: `Λ(f,s) ≠ 0` for `Re s ≥ σ₁` and `Re s ≤ k − σ₁`.
* `order_reflect`: `ord_{k−u} Λ = ord_u Λ` (functional equation `Λ(k−s) = i^k Λ(s)`).
* `order_Lam_eq_fL`: `ord_u Λ = ord_u L` off the poles of `Γ`.
* `fL_growth`: `‖L(f,s)‖ ≤ B (1+‖s‖)²` on `Re s ≥ (k−1)/2`.
-/
import RamanujanTau.HafnerGeneral.Main
import RamanujanTau.ZeroCountRvM.RvM

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

variable {k : ℕ}

lemma weight_ge (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : 12 ≤ k := by
  by_contra h; push Not at h; exact hf (eq_zero_of_lt_twelve f h)

lemma weight_even (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : Even k := by
  rcases Nat.even_or_odd k with h | h
  · exact h
  · exact absurd (HardyZerosGeneral.eq_zero_of_odd f h) hf

/-- The normalized function `G(s) = n₀^s / a₀ · L(f,s)`. -/
noncomputable def Gn (f : CuspForm 𝒮ℒ (k : ℤ)) (n₀ : ℕ) (s : ℂ) : ℂ :=
  (n₀ : ℂ) ^ s / coef f n₀ * fL f s

lemma Gn_entire (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    Differentiable ℂ (Gn f n₀) := by
  have hn : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (show n₀ ≠ 0 by omega)
  exact ((differentiable_id.const_cpow (Or.inl hn)).div_const _).mul (fL_entire f hk)

lemma norm_Gn (f : CuspForm 𝒮ℒ (k : ℤ)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (s : ℂ) :
    ‖Gn f n₀ s‖ = (n₀ : ℝ) ^ s.re / ‖coef f n₀‖ * ‖fL f s‖ := by
  rw [Gn, norm_mul, norm_div, norm_natCast_cpow_of_pos (by omega)]

lemma fL_eq_of_Gn (f : CuspForm 𝒮ℒ (k : ℤ)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (ha : coef f n₀ ≠ 0)
    (s : ℂ) : fL f s = coef f n₀ * Gn f n₀ s / (n₀ : ℂ) ^ s := by
  have hc : (n₀ : ℂ) ^ s ≠ 0 := by
    have := norm_natCast_cpow_pos_of_pos (n := n₀) (by omega) s
    exact norm_pos_iff.mp this
  rw [Gn]; field_simp

/-- **Half-plane normalisation.** -/
theorem exists_sigma_normalized (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {n₀ : ℕ}
    (ha₀ : coef f n₀ ≠ 0) (hmin : ∀ n < n₀, coef f n = 0) {σa : ℝ}
    (hσa : ((k : ℝ) + 1) / 2 < σa) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ σ₁ : ℝ, σa ≤ σ₁ ∧ ∀ s : ℂ, σ₁ ≤ s.re → ‖Gn f n₀ s - 1‖ ≤ ρ := by
  have hn₀1 : 1 ≤ n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exact absurd (h ▸ coef_zero f) ha₀
    · exact h
  set a₀ := coef f n₀ with ha₀def
  have ha₀n : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  have hσa0 : 0 < σa := lt_of_le_of_lt (by positivity) hσa
  have hsum : LSeriesSummable (coef f) (σa : ℂ) := LSeriesSummable_coef f hk (by simpa using hσa)
  set S : ℝ := ∑' n, ‖LSeries.term (coef f) σa n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  set B : ℝ := (n₀ : ℝ) ^ σa / ‖a₀‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set q : ℝ := (n₀ : ℝ) / ((n₀ : ℝ) + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ρ / (B * S + 1) by positivity) hq1
  refine ⟨σa + K, by linarith [Nat.cast_nonneg (α := ℝ) K], fun s hs => ?_⟩
  set σ := s.re with hσdef
  have hσa' : σa + K ≤ σ := hs
  have hsums : LSeriesSummable (coef f) s :=
    LSeriesSummable_coef f hk (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have hpos : (0 : ℝ) < n₀ := by exact_mod_cast hn₀1
  have hcp0 : (n₀ : ℂ) ^ s ≠ 0 := by
    have := norm_natCast_cpow_pos_of_pos (n := n₀) (by omega) s
    exact norm_pos_iff.mp this
  rw [Gn, fL_eq_LSeries f hk (by linarith [Nat.cast_nonneg (α := ℝ) K]), LSeries,
    hsums.tsum_eq_add_tsum_ite n₀]
  have hterm : LSeries.term (coef f) s n₀ = a₀ / (n₀ : ℂ) ^ s := by
    rw [LSeries.term_def, if_neg (by omega)]
  rw [hterm]
  set R := ∑' n, (if n = n₀ then 0 else LSeries.term (coef f) s n) with hR
  have hsimp : (n₀ : ℂ) ^ s / a₀ * (a₀ / (n₀ : ℂ) ^ s + R) - 1 = (n₀ : ℂ) ^ s / a₀ * R := by
    field_simp; ring
  rw [← ha₀def, hsimp, hR, ← tsum_mul_left]
  have hpt : ∀ n : ℕ, ‖(n₀ : ℂ) ^ s / a₀ * (if n = n₀ then 0 else LSeries.term (coef f) s n)‖ ≤
      q ^ K * B * ‖LSeries.term (coef f) σa n‖ := by
    intro n
    have hrhs : 0 ≤ q ^ K * B * ‖LSeries.term (coef f) σa n‖ := by positivity
    split_ifs with hn
    · simpa using hrhs
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have : LSeries.term (coef f) s n = 0 := by
        rw [LSeries.term_def]; split_ifs <;> simp [hmin n hlt]
      rw [this, mul_zero, norm_zero]; exact hrhs
    · have hn0 : n ≠ 0 := by omega
      have hnR : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hgt
      have hnpos : (0 : ℝ) < n := by linarith
      rw [norm_mul, norm_div, norm_natCast_cpow_of_pos (by omega), LSeries.norm_term_eq,
        LSeries.norm_term_eq, if_neg hn0, if_neg hn0]
      have e7 : ((σa : ℂ)).re = σa := by simp
      rw [e7, ← hσdef]
      set c := ‖coef f n‖ with hc
      have hc0 : 0 ≤ c := norm_nonneg _
      have h1 : (n₀ : ℝ) ^ σ = (n₀ : ℝ) ^ σa * (n₀ : ℝ) ^ (σ - σa) := by
        rw [← Real.rpow_add hpos]; ring_nf
      have h2 : (n : ℝ) ^ σ = (n : ℝ) ^ σa * (n : ℝ) ^ (σ - σa) := by
        rw [← Real.rpow_add hnpos]; ring_nf
      have hr1 : (n₀ : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have hr0 : 0 ≤ (n₀ : ℝ) / n := by positivity
      have hqn : ((n₀ : ℝ) / n) ^ (σ - σa) ≤ q ^ K := by
        calc ((n₀ : ℝ) / n) ^ (σ - σa) ≤ ((n₀ : ℝ) / n) ^ ((K : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 (by positivity) (by linarith)
          _ = ((n₀ : ℝ) / n) ^ K := Real.rpow_natCast _ _
          _ ≤ q ^ K := by
              apply pow_le_pow_left₀ hr0
              rw [hq]; exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnR
      have hX : 0 ≤ (n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa) := by positivity
      have hnσ : 0 < (n : ℝ) ^ σa := Real.rpow_pos_of_pos hnpos _
      have hnK : 0 < (n : ℝ) ^ (σ - σa) := Real.rpow_pos_of_pos hnpos _
      have hdiv : ((n₀ : ℝ) / n) ^ (σ - σa) = (n₀ : ℝ) ^ (σ - σa) / (n : ℝ) ^ (σ - σa) :=
        Real.div_rpow hpos.le hnpos.le _
      calc (n₀ : ℝ) ^ σ / ‖a₀‖ * (c / (n : ℝ) ^ σ)
          = ((n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa)) * ((n₀ : ℝ) / n) ^ (σ - σa) := by
            rw [h1, h2, hdiv]; field_simp
        _ ≤ ((n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa)) * q ^ K :=
            mul_le_mul_of_nonneg_left hqn hX
        _ = q ^ K * B * (c / (n : ℝ) ^ σa) := by rw [hB]; ring
  have hsumR : Summable fun n => q ^ K * B * ‖LSeries.term (coef f) σa n‖ :=
    hsum.norm.mul_left _
  have hnorm : Summable fun n : ℕ =>
      ‖(n₀ : ℂ) ^ s / a₀ * (if n = n₀ then 0 else LSeries.term (coef f) s n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumR
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (Summable.tsum_le_tsum hpt hnorm hsumR).trans ?_
  rw [tsum_mul_left, ← hS]
  have h := hK.le
  rw [le_div_iff₀ (by positivity)] at h
  have : 0 ≤ q ^ K := by positivity
  nlinarith

/-- **The data of the normalisation**: `n₀` the first nonzero index, `σ₁ ≥ (k+1)/2 + 1` with
`|G − 1| ≤ 1/4` on `Re s ≥ σ₁`. -/
structure NormData (f : CuspForm 𝒮ℒ (k : ℤ)) where
  n₀ : ℕ
  hn₀ : 1 ≤ n₀
  ha₀ : coef f n₀ ≠ 0
  hmin : ∀ n < n₀, coef f n = 0
  σ₁ : ℝ
  hσ₁ : ((k : ℝ) + 1) / 2 + 1 ≤ σ₁
  hG : ∀ s : ℂ, σ₁ ≤ s.re → ‖Gn f n₀ s - 1‖ ≤ 1 / 4

lemma one_le_of_coef_ne_zero (f : CuspForm 𝒮ℒ (k : ℤ)) {n₀ : ℕ} (ha₀ : coef f n₀ ≠ 0) :
    1 ≤ n₀ := by
  rcases Nat.eq_zero_or_pos n₀ with h | h
  · exact absurd (h ▸ coef_zero f) ha₀
  · exact h

/-- A normalisation exists for any prescribed first index `n₀`. -/
theorem exists_normData (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {n₀ : ℕ}
    (ha₀ : coef f n₀ ≠ 0) (hmin : ∀ n < n₀, coef f n = 0) :
    ∃ D : NormData f, D.n₀ = n₀ := by
  obtain ⟨σ₁, hσ₁, hG⟩ := exists_sigma_normalized f hk ha₀ hmin
    (σa := ((k : ℝ) + 1) / 2 + 1) (by linarith) (ρ := 1 / 4) (by norm_num)
  exact ⟨⟨n₀, one_le_of_coef_ne_zero f ha₀, ha₀, hmin, σ₁, hσ₁, hG⟩, rfl⟩

/-- The first nonzero index exists for `f ≠ 0`. -/
theorem exists_first (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ n₀ : ℕ, coef f n₀ ≠ 0 ∧ ∀ n < n₀, coef f n = 0 := by
  classical
  have hex := HafnerGeneral.exists_coef_ne_zero f hf hk
  exact ⟨Nat.find hex, Nat.find_spec hex, fun n hn => by
    by_contra h; exact Nat.find_min hex hn h⟩

namespace NormData

variable {f : CuspForm 𝒮ℒ (k : ℤ)} (D : NormData f)

lemma Gn_re_ge {s : ℂ} (hs : D.σ₁ ≤ s.re) : 3 / 4 ≤ (Gn f D.n₀ s).re := by
  have h := D.hG s hs
  have := Complex.abs_re_le_norm (Gn f D.n₀ s - 1)
  rw [sub_re, one_re] at this
  linarith [(abs_le.mp this).1]

lemma Gn_ne_zero {s : ℂ} (hs : D.σ₁ ≤ s.re) : Gn f D.n₀ s ≠ 0 := by
  intro h; have := D.Gn_re_ge hs; rw [h] at this; simp at this; linarith

lemma fL_ne_zero {s : ℂ} (hs : D.σ₁ ≤ s.re) : fL f s ≠ 0 := by
  intro h; apply D.Gn_ne_zero hs; rw [Gn, h, mul_zero]

lemma σ₁_pos : 0 < D.σ₁ := by linarith [D.hσ₁, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma Lam_ne_zero_right {s : ℂ} (hs : D.σ₁ ≤ s.re) : heckeLambda f s ≠ 0 := by
  have hpos : 0 < s.re := lt_of_lt_of_le D.σ₁_pos hs
  rw [heckeLambda_eq_fL f (ne_neg_nat_of_re_pos hpos)]
  exact mul_ne_zero (mul_ne_zero (by rw [cpow_neg]; exact inv_ne_zero (two_pi_cpow_ne_zero _))
    (Gamma_ne_zero_of_re_pos hpos)) (D.fL_ne_zero hs)

lemma Lam_ne_zero_left (hk : 1 ≤ k) {s : ℂ} (hs : s.re ≤ k - D.σ₁) : heckeLambda f s ≠ 0 := by
  have h := heckeLambda_functional_equation f hk s
  intro h0
  rw [h0, mul_zero] at h
  exact D.Lam_ne_zero_right (s := (k : ℂ) - s) (by simp; linarith) h

end NormData

/-! ### Orders -/

lemma order_reflect (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (u : ℂ) :
    analyticOrderAt (heckeLambda f) ((k : ℂ) - u) = analyticOrderAt (heckeLambda f) u := by
  have hfe : (fun s => heckeLambda f ((k : ℂ) - s)) = fun s => I ^ k * heckeLambda f s :=
    funext (heckeLambda_functional_equation f hk)
  have hg : AnalyticAt ℂ (fun s : ℂ => (k : ℂ) - s) u := by fun_prop
  have hd : deriv (fun s : ℂ => (k : ℂ) - s) u ≠ 0 := by
    rw [deriv_const_sub, deriv_id'']; norm_num
  have h1 := analyticOrderAt_comp_of_deriv_ne_zero (f := heckeLambda f) hg hd
  have hcomp : (heckeLambda f ∘ fun s : ℂ => (k : ℂ) - s) = fun s => I ^ k * heckeLambda f s :=
    hfe
  rw [hcomp] at h1
  rw [← h1]
  have hIk : I ^ k ≠ 0 := pow_ne_zero _ I_ne_zero
  have han : AnalyticAt ℂ (heckeLambda f) u := (heckeLambda_entire f hk).analyticAt u
  have hc : AnalyticAt ℂ (fun _ : ℂ => I ^ k) u := analyticAt_const
  rw [show (fun s => I ^ k * heckeLambda f s) = (fun _ : ℂ => I ^ k) * heckeLambda f from rfl,
    analyticOrderAt_mul hc han,
    (analyticOrderAt_eq_zero.mpr (Or.inr hIk) : analyticOrderAt (fun _ : ℂ => I ^ k) u = 0),
    zero_add]

/-- The set where `Γ` is analytic and nonzero (used for the orders). -/
def goodSet : Set ℂ := {s | 0 < s.re} ∪ {s | s.im ≠ 0}

lemma isOpen_goodSet : IsOpen goodSet :=
  (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)

lemma ne_neg_nat_of_good {s : ℂ} (hs : s ∈ goodSet) : ∀ n : ℕ, s ≠ -n := by
  rcases hs with hs | hs
  · exact NormData.ne_neg_nat_of_re_pos hs
  · intro n h; apply hs; rw [h]; simp

lemma order_Lam_eq_fL (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {u : ℂ} (hu : u ∈ goodSet) :
    analyticOrderAt (heckeLambda f) u = analyticOrderAt (fL f) u := by
  have heq : heckeLambda f =ᶠ[𝓝 u] fun w => ((2 * π : ℂ) ^ (-w) * Gamma w) * fL f w := by
    filter_upwards [isOpen_goodSet.mem_nhds hu] with w hw
    exact heckeLambda_eq_fL f (ne_neg_nat_of_good hw)
  have hGam : AnalyticAt ℂ Gamma u := by
    have hd : DifferentiableOn ℂ Gamma goodSet := fun w hw =>
      (differentiableAt_Gamma w (ne_neg_nat_of_good hw)).differentiableWithinAt
    exact hd.analyticAt (isOpen_goodSet.mem_nhds hu)
  have hhan : AnalyticAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) u := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) u := by
      have : Differentiable ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) :=
        fun w => (ZeroCountRvM.hasDerivAt_two_pi_cpow_neg w).differentiableAt
      exact this.analyticAt u
    exact h1.mul hGam
  have h0 : analyticOrderAt (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (mul_ne_zero
      (by rw [cpow_neg]; exact inv_ne_zero (two_pi_cpow_ne_zero _))
      (Gamma_ne_zero (ne_neg_nat_of_good hu))))
  have hmul := analyticOrderAt_mul hhan ((fL_entire f hk).analyticAt u)
  rw [h0, zero_add] at hmul
  rw [analyticOrderAt_congr heq]
  exact hmul

lemma Lam_zero_iff_fL (f : CuspForm 𝒮ℒ (k : ℤ)) {u : ℂ} (hu : u ∈ goodSet) :
    heckeLambda f u = 0 ↔ fL f u = 0 := by
  rw [heckeLambda_eq_fL f (ne_neg_nat_of_good hu)]
  have h1 : (2 * π : ℂ) ^ (-u) ≠ 0 := by rw [cpow_neg]; exact inv_ne_zero (two_pi_cpow_ne_zero _)
  simp [h1, Gamma_ne_zero (ne_neg_nat_of_good hu)]

/-! ### Polynomial growth on `Re s ≥ (k−1)/2` -/

theorem fL_growth (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ((k : ℝ) - 1) / 2 ≤ s.re → ‖fL f s‖ ≤ B * (1 + ‖s‖) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk (ε := 1 / 2) (by norm_num) le_rfl
  obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk1 (σ := ((k : ℝ) + 1) / 2 + 1 / 2) (by linarith)
  refine ⟨2 * Real.exp 10 * C + D, by positivity, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
  rcases le_or_gt s.re (((k : ℝ) + 1) / 2 + 1 / 2) with h | h
  · have hl := fL_line f hk (ε := 1 / 2) (by norm_num) le_rfl hC (s := s) (by linarith) h
    set θ := ((k : ℝ) + 1) / 2 + 1 / 2 - s.re with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ2 : θ ≤ 2 := by rw [hθ]; linarith
    have hb : ‖s / 2‖ ^ θ ≤ (1 + ‖s‖) ^ 2 := by
      have hn : ‖s / 2‖ ≤ 1 + ‖s‖ := by
        rw [norm_div, Complex.norm_two]; linarith [norm_nonneg s]
      calc ‖s / 2‖ ^ θ ≤ (1 + ‖s‖) ^ θ := Real.rpow_le_rpow (norm_nonneg _) hn hθ0
        _ ≤ (1 + ‖s‖) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg s]) hθ2
        _ = (1 + ‖s‖) ^ 2 := by norm_cast
    have hK : 0 ≤ 2 * Real.exp 10 * C := by positivity
    calc ‖fL f s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hl
      _ ≤ 2 * Real.exp 10 * C * (1 + ‖s‖) ^ 2 := mul_le_mul_of_nonneg_left hb hK
      _ ≤ _ := by nlinarith
  · have := hD s h.le
    have h2 : 0 ≤ 2 * Real.exp 10 * C * (1 + ‖s‖) ^ 2 := by positivity
    nlinarith

end RamanujanTau.GeneralZeros
