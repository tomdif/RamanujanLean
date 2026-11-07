/-
# A Riesz-smoothed Perron formula with complex coefficients, and the contour shift past `w = 0`

* `perron_c`: for `a : ℕ → ℂ`, `a 0 = 0`, `∑ |aₙ| n^{-c} < ∞` (`c > 0`), `k ≥ 1`, `x > 0`:
  `2π ∑ aₙ φ_k(n/x) = ∫ x^{c+iy} P_k(c+iy) L(a, c+iy) dy`.
* `shift_identity`: for `F` entire with `‖F w‖ ≤ K (1+|Im w|)²` on `−δ ≤ Re w ≤ c`
  (`0 < δ < 1`, `c > 0`) and `X ≥ 1`:
  `∫_{(c)} X^w P₃(w) F(w) = 2π F(0) φ₃(1/X) + ∫_{(−δ)} X^w P₃(w) F(w) − F(0) ∫_{(−δ)} X^w P₃(w)`.
  The residue at the simple pole `w = 0` is removed by hand: `h(w) = X^w Q(w) dslope F 0 w`,
  `Q(w) = 6/((w+1)(w+2)(w+3))`, is holomorphic on `Re w > −1` and equals
  `X^w P₃(w) (F(w) − F(0))` off `0`; shift `h` with `Stirling.integral_line_eq_rpow`.
-/
import RamanujanTau.Stirling.RieszReal

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError

/-! ### Perron with complex coefficients -/

section Perron

variable (a : ℕ → ℂ) (ha0 : a 0 = 0)

/-- The integrand on the line, term by term. -/
noncomputable def ftermC (k : ℕ) (c x : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  a n * ((n : ℂ) ^ (-ln c y) * (x : ℂ) ^ ln c y * Pk k (ln c y))

include ha0 in
lemma integral_ftermC {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    ∫ y, ftermC a k c x n y = a n * (2 * π * phi k (n / x)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [ftermC, ha0]
  · have hinv := mellinInv_Pk hk hc (u := n / x) (by positivity)
    unfold mellinInv at hinv
    rw [Complex.real_smul] at hinv
    simp_rw [cpow_div_neg (Nat.cast_nonneg n) hx, ofReal_natCast] at hinv
    unfold ftermC
    rw [integral_const_mul]
    congr 1
    have h2π : (2 * π : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    rw [← hinv]
    push_cast
    field_simp
    congr 1; funext y; simp only [smul_eq_mul, ln]; ring_nf

include ha0 in
lemma norm_ftermC {k : ℕ} {c x : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    ‖ftermC a k c x n y‖ = ‖a n‖ * (n : ℝ) ^ (-c) * x ^ c * ‖Pk k (ln c y)‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [ftermC, ha0]
  · unfold ftermC
    rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_neg hn.ne',
      norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (ln c y).re = c := by simp [ln]
    rw [hre]; ring

include ha0 in
lemma integrable_ftermC {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    Integrable (ftermC a k c x n) := by
  have hP := integrable_Pk_line hk hc
  have hmeas : AEStronglyMeasurable (ftermC a k c x n) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : ftermC a k c x 0 = fun _ => 0 := by funext y; simp [ftermC, ha0]
      rw [this]; exact aestronglyMeasurable_const
    · refine Continuous.aestronglyMeasurable ?_
      unfold ftermC
      have hc1 := continuous_Pk_line k hc
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      refine continuous_const.mul ((Continuous.mul ?_ ?_).mul hc1)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl hx0)
  refine (hP.norm.const_mul (‖a n‖ * (n : ℝ) ^ (-c) * x ^ c)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [norm_ftermC a ha0 hx]

include ha0 in
/-- **Perron formula for Riesz means, complex coefficients.** -/
theorem perron_c {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c)) :
    (2 * π : ℂ) * ∑' n : ℕ, a n * phi k (n / x) =
      ∫ y : ℝ, (x : ℂ) ^ ln c y * Pk k (ln c y) * LSeries a (ln c y) := by
  have hint := integrable_ftermC a ha0 hk hc hx
  have hsumI : Summable fun n => ∫ y, ‖ftermC a k c x n y‖ := by
    simp_rw [norm_ftermC a ha0 hx, integral_const_mul]
    exact (hsum.mul_right (x ^ c)).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumI
  simp_rw [integral_ftermC a ha0 hk hc hx] at key
  rw [← tsum_mul_left]
  have e1 : ∀ n : ℕ, (2 * π : ℂ) * (a n * phi k (n / x)) =
      a n * (2 * π * phi k (n / x)) := fun n => by ring
  simp_rw [e1, key]
  congr 1
  funext y
  unfold ftermC LSeries
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [LSeries.term_def₀ ha0]
  ring

end Perron

/-! ### Bounds for `P₃` -/

lemma Pk3_eq (w : ℂ) : Pk 3 w = 6 / (w * (w + 1) * (w + 2) * (w + 3)) := by
  simp [Pk, prod_range_succ, Nat.factorial]

/-- General bound: if `b ≤ ‖w + j‖` for all `j`, then `‖P_k(w)‖ ≤ k!/b^{k+1}`. -/
lemma norm_Pk_le_of (k : ℕ) {w : ℂ} {b : ℝ} (hb : 0 < b) (h : ∀ j : ℕ, b ≤ ‖w + j‖) :
    ‖Pk k w‖ ≤ k.factorial / b ^ (k + 1) := by
  have hprod : b ^ (k + 1) ≤ ∏ j ∈ range (k + 1), ‖w + j‖ := by
    have : b ^ (k + 1) = ∏ _j ∈ range (k + 1), b := by rw [prod_const, card_range]
    rw [this]
    exact prod_le_prod (fun _ _ => hb.le) (fun j _ => h j)
  rw [Pk, norm_div, norm_prod, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod

/-- For `|Im w| ≥ 1`: `‖P₃(w)‖ ≤ 96/(1+|Im w|)⁴`. -/
lemma norm_Pk3_le_im {w : ℂ} (hw : 1 ≤ |w.im|) : ‖Pk 3 w‖ ≤ 96 / (1 + |w.im|) ^ 4 := by
  have hb : 0 < (1 + |w.im|) / 2 := by positivity
  have := norm_Pk_le_of 3 hb (w := w) fun j => by
    have h2 : |(w + j).im| ≤ ‖w + j‖ := Complex.abs_im_le_norm _
    simp only [add_im, natCast_im, add_zero] at h2
    linarith
  refine this.trans (le_of_eq ?_)
  rw [div_pow]; simp [Nat.factorial]; field_simp; norm_num

/-- On a line `Re w = σ` with `−1 < σ < 0`: `‖P₃(w)‖ ≤ 6(2/m)⁴/(1+|Im w|)⁴`, `m = min(−σ, 1+σ)`. -/
lemma norm_Pk3_le_left {σ : ℝ} (h0 : σ < 0) (h1 : -1 < σ) (y : ℝ) :
    ‖Pk 3 ((σ : ℂ) + y * I)‖ ≤ 6 * (2 / min (-σ) (1 + σ)) ^ 4 / (1 + |y|) ^ 4 := by
  set m := min (-σ) (1 + σ) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hm1 : m ≤ 1 := (min_le_right _ _).trans (by linarith)
  have hb : 0 < m * (1 + |y|) / 2 := by positivity
  have := norm_Pk_le_of 3 hb (w := (σ : ℂ) + y * I) fun j => by
    have h2 : |((σ : ℂ) + y * I + j).im| ≤ ‖(σ : ℂ) + y * I + j‖ := Complex.abs_im_le_norm _
    have h3 : |((σ : ℂ) + y * I + j).re| ≤ ‖(σ : ℂ) + y * I + j‖ := Complex.abs_re_le_norm _
    simp only [add_im, natCast_im, add_zero, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
      I_re, mul_zero, zero_add, add_re, natCast_re, mul_re, ofReal_im, sub_zero] at h2 h3
    have hre : m ≤ |σ + j| := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp only [Nat.cast_zero, add_zero]; rw [abs_of_neg h0]
        exact min_le_left _ _
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
        rw [abs_of_pos (by linarith)]
        exact (min_le_right _ _).trans (by linarith)
    have : m * |y| ≤ |y| := by have := abs_nonneg y; nlinarith
    nlinarith
  refine this.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, div_pow]; simp [Nat.factorial]; field_simp

lemma prod_ne_zero_left {σ : ℝ} (h0 : σ < 0) (h1 : -1 < σ) (y : ℝ) :
    ∏ j ∈ range (3 + 1), ((σ : ℂ) + y * I + j) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro j _ h
  have := congrArg Complex.re h
  simp at this
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp at this; linarith
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith

lemma continuous_Pk3_left {σ : ℝ} (h0 : σ < 0) (h1 : -1 < σ) :
    Continuous fun y : ℝ => Pk 3 ((σ : ℂ) + y * I) := by
  unfold Pk
  exact Continuous.div continuous_const (by fun_prop) (fun y => prod_ne_zero_left h0 h1 y)

/-- `‖X^w‖ = X^{Re w}`. -/
lemma norm_X_cpow {X : ℝ} (hX : 0 < X) (w : ℂ) : ‖(X : ℂ) ^ w‖ = X ^ w.re :=
  norm_cpow_eq_rpow_re_of_pos hX w

lemma integrable_of_le_div_sq' {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (h : ∀ y, ‖g y‖ ≤ C / (1 + |y|) ^ 2) : Integrable g :=
  integrable_of_le_div_sq hg h

/-- `∫ C/(1+|y|)² dy` is finite. -/
lemma integrable_div_sq (C : ℝ) : Integrable fun y : ℝ => C / (1 + |y|) ^ 2 := by
  have hi : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-(2:ℝ))) :=
    (integrable_one_add_norm (by simp)).const_mul C
  refine hi.congr (Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]; norm_cast

/-! ### The contour shift -/

/-- `h(w) = X^w Q(w) dslope F 0 w`, `Q(w) = 6/((w+1)(w+2)(w+3))`. -/
noncomputable def hfun (F : ℂ → ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  (X : ℂ) ^ w * (6 / ((w + 1) * (w + 2) * (w + 3))) * dslope F 0 w

lemma hfun_eq {F : ℂ → ℂ} {X : ℝ} {w : ℂ} (hw : w ≠ 0) :
    hfun F X w = (X : ℂ) ^ w * Pk 3 w * (F w - F 0) := by
  rw [hfun, dslope_of_ne _ hw, slope_def_module, Pk3_eq, sub_zero, smul_eq_mul]
  field_simp

lemma differentiableOn_hfun {F : ℂ → ℂ} (hF : Differentiable ℂ F) {X : ℝ} (hX : 0 < X)
    {a b : ℝ} (ha : -1 < a) :
    DifferentiableOn ℂ (hfun F X) {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hd : Differentiable ℂ (dslope F 0) := by
    have := (differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ)) Filter.univ_mem).2
      hF.differentiableOn
    exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  intro w hw
  have hre : -1 < w.re := lt_of_lt_of_le ha hw.1
  have hne : ∀ j : ℕ, 1 ≤ j → w + j ≠ 0 := by
    intro j hj h
    have := congrArg Complex.re h
    simp at this
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have h1 : w + 1 ≠ 0 := by simpa using hne 1 le_rfl
  have h2 : w + 2 ≠ 0 := by simpa using hne 2 (by norm_num)
  have h3 : w + 3 ≠ 0 := by simpa using hne 3 (by norm_num)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold hfun
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (hd w)
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl hX0)
  · refine DifferentiableAt.div (differentiableAt_const _) (by fun_prop) ?_
    exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- Bound for `h` on the strip `−δ ≤ Re w ≤ c`. -/
lemma hfun_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {X : ℝ} (hX : 1 ≤ X) {c δ : ℝ}
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) {K : ℝ}
    (hK : ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖F w‖ ≤ K * (1 + |w.im|) ^ 2) :
    ∃ C : ℝ, ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖hfun F X w‖ ≤ C * (1 + |w.im|) ^ (-(2 : ℝ)) := by
  have hX0 : 0 < X := by linarith
  -- compact part
  set R : Set ℂ := (Set.Icc (-δ) c) ×ℂ (Set.Icc (-1) 1) with hR
  have hRc : IsCompact R := (isCompact_Icc).reProdIm isCompact_Icc
  have hcont : ContinuousOn (hfun F X) R := by
    refine (differentiableOn_hfun hF hX0 (a := -δ) (b := c) (by linarith)).continuousOn.mono ?_
    intro w hw
    simp only [hR, Complex.mem_reProdIm, Set.mem_Icc] at hw
    exact ⟨hw.1.1, hw.1.2⟩
  obtain ⟨B, hB⟩ := hRc.exists_bound_of_continuousOn hcont
  have hK0 : 0 ≤ K := by
    have := hK 0 (by simp; linarith) (by simp; linarith)
    simp at this
    exact (norm_nonneg _).trans this
  refine ⟨192 * K * X ^ c + 4 * max B 0, fun w h1 h2 => ?_⟩
  have hv : (0 : ℝ) < 1 + |w.im| := by positivity
  have hrp : (1 + |w.im|) ^ (-(2 : ℝ)) = 1 / (1 + |w.im|) ^ 2 := by
    rw [Real.rpow_neg hv.le, one_div]; norm_cast
  rw [hrp]
  rcases le_or_gt 1 |w.im| with him | him
  · -- `|Im w| ≥ 1`
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at him; simp at him; linarith
    rw [hfun_eq hw0, norm_mul, norm_mul, norm_X_cpow hX0]
    have hXw : X ^ w.re ≤ X ^ c := Real.rpow_le_rpow_of_exponent_le hX h2
    have hP := norm_Pk3_le_im him
    have hFw := hK w h1 h2
    have hF0 : ‖F 0‖ ≤ K := by
      have := hK 0 (by simp; linarith) (by simp; linarith)
      simpa using this
    have hsub : ‖F w - F 0‖ ≤ 2 * K * (1 + |w.im|) ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have : K ≤ K * (1 + |w.im|) ^ 2 := by
        have : (1 : ℝ) ≤ (1 + |w.im|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg w.im])
        nlinarith
      linarith
    have hB0 : 0 ≤ 4 * max B 0 * (1 / (1 + |w.im|) ^ 2) := by positivity
    calc X ^ w.re * ‖Pk 3 w‖ * ‖F w - F 0‖
        ≤ X ^ c * (96 / (1 + |w.im|) ^ 4) * (2 * K * (1 + |w.im|) ^ 2) := by
          gcongr
      _ = 192 * K * X ^ c * (1 / (1 + |w.im|) ^ 2) := by
          field_simp; ring
      _ ≤ (192 * K * X ^ c + 4 * max B 0) * (1 / (1 + |w.im|) ^ 2) := by
          rw [add_mul]; linarith
  · -- compact part
    have hwR : w ∈ R := by
      simp only [hR, Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨h1, h2⟩, by linarith [neg_abs_le w.im, le_abs_self w.im], by
        linarith [le_abs_self w.im]⟩
    have hb := hB w hwR
    have hsq : (1 + |w.im|) ^ 2 ≤ 4 := by
      have := abs_nonneg w.im; nlinarith
    have : max B 0 ≤ 4 * max B 0 * (1 / (1 + |w.im|) ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      have := le_max_right B 0; nlinarith
    have h0 : 0 ≤ 192 * K * X ^ c * (1 / (1 + |w.im|) ^ 2) := by positivity
    calc ‖hfun F X w‖ ≤ max B 0 := hb.trans (le_max_left _ _)
      _ ≤ (192 * K * X ^ c + 4 * max B 0) * (1 / (1 + |w.im|) ^ 2) := by
          rw [add_mul]; linarith

/-- `X^w P₃(w)` is integrable on the line `Re w = σ`, `−1 < σ < 0`. -/
lemma integrable_XPk_left {X : ℝ} (hX : 0 < X) {σ : ℝ} (h0 : σ < 0) (h1 : -1 < σ) :
    Integrable fun y : ℝ => (X : ℂ) ^ ln σ y * Pk 3 (ln σ y) := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  refine integrable_of_le_div_sq ((Continuous.const_cpow (by fun_prop) (Or.inl hX0)).mul
    (continuous_Pk3_left h0 h1)) (C := X ^ σ * (6 * (2 / min (-σ) (1 + σ)) ^ 4)) fun y => ?_
  rw [norm_mul, norm_X_cpow hX]
  have hre : (ln σ y).re = σ := by simp [ln]
  rw [hre]
  have hP := norm_Pk3_le_left h0 h1 y
  have h1y : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 4 := pow_le_pow_right₀ h1y (by norm_num)
  calc X ^ σ * ‖Pk 3 (ln σ y)‖ ≤ X ^ σ * (6 * (2 / min (-σ) (1 + σ)) ^ 4 / (1 + |y|) ^ 4) := by
        gcongr
    _ ≤ X ^ σ * (6 * (2 / min (-σ) (1 + σ)) ^ 4 / (1 + |y|) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- `X^w P₃(w)` is integrable on the line `Re w = c > 0`. -/
lemma integrable_XPk_right {X : ℝ} (hX : 0 < X) {c : ℝ} (hc : 0 < c) :
    Integrable fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  refine integrable_of_le_div_sq ((Continuous.const_cpow (by fun_prop) (Or.inl hX0)).mul
    (continuous_Pk_line 3 hc)) (C := X ^ c * (Nat.factorial 3 * (2 / min c 1) ^ (3 + 1)))
    fun y => ?_
  rw [norm_mul, norm_X_cpow hX]
  have hre : (ln c y).re = c := by simp [ln]
  rw [hre]
  have hP := Pk_line_le 3 hc y
  have h1y : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ (3 + 1) := pow_le_pow_right₀ h1y (by norm_num)
  calc X ^ c * ‖Pk 3 (ln c y)‖
      ≤ X ^ c * (Nat.factorial 3 * (2 / min c 1) ^ (3 + 1) / (1 + |y|) ^ (3 + 1)) := by
        gcongr
    _ ≤ X ^ c * (Nat.factorial 3 * (2 / min c 1) ^ (3 + 1) / (1 + |y|) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- `∫_{(c)} X^w P₃(w) dy = 2π φ₃(1/X)`. -/
lemma integral_XPk_right {X : ℝ} (hX : 0 < X) {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, (X : ℂ) ^ ln c y * Pk 3 (ln c y) = 2 * π * phi 3 (1 / X) := by
  have hinv := mellinInv_Pk (k := 3) (by norm_num) hc (u := 1 / X) (by positivity)
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have e : ∀ y : ℝ, ((1 / X : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) = (X : ℂ) ^ ln c y := by
    intro y
    rw [cpow_div_neg zero_le_one hX, Complex.ofReal_one, one_cpow, one_mul]
  simp_rw [smul_eq_mul, e] at hinv
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have : ∫ y : ℝ, (X : ℂ) ^ ln c y * Pk 3 (ln c y) = (2 * π : ℂ) * (phi 3 (1 / X) : ℂ) := by
    rw [← hinv]; push_cast; field_simp
  rw [this]

/-- **The contour shift past the pole `w = 0`.** -/
theorem shift_identity {F : ℂ → ℂ} (hF : Differentiable ℂ F) {X : ℝ} (hX : 1 ≤ X) {c δ : ℝ}
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) {K : ℝ}
    (hK : ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖F w‖ ≤ K * (1 + |w.im|) ^ 2) :
    ∫ y : ℝ, (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) =
      2 * π * F 0 * phi 3 (1 / X) +
        ((∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y)) -
          F 0 * ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨C, hC⟩ := hfun_bound hF hX hc hδ0 hδ1 hK
  have hdiff := differentiableOn_hfun hF hX0 (a := -δ) (b := c) (by linarith)
  have hshift := RamanujanTau.Stirling.integral_line_eq_rpow (p := 2) (by norm_num)
    (by linarith : -δ ≤ c) hdiff hC
  have hih_c := RamanujanTau.Stirling.integrable_line_of_strip_rpow (p := 2) (by norm_num)
    hdiff.continuousOn hC (σ := c) (by linarith) le_rfl
  have hih_l := RamanujanTau.Stirling.integrable_line_of_strip_rpow (p := 2) (by norm_num)
    hdiff.continuousOn hC (σ := -δ) le_rfl (by linarith)
  have hne : ∀ σ y : ℝ, σ ≠ 0 → ln σ y ≠ 0 := by
    intro σ y hσ h
    have := congrArg Complex.re h
    simp [ln] at this
    exact hσ this
  -- on the right line
  have hR : ∀ y : ℝ, (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) =
      hfun F X (ln c y) + F 0 * ((X : ℂ) ^ ln c y * Pk 3 (ln c y)) := by
    intro y; rw [hfun_eq (hne c y hc.ne')]; ring
  -- on the left line
  have hL : ∀ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y) =
      hfun F X (ln (-δ) y) + F 0 * ((X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)) := by
    intro y; rw [hfun_eq (hne (-δ) y (by linarith))]; ring
  have hXr := integrable_XPk_right hX0 hc
  have hXl := integrable_XPk_left hX0 (σ := -δ) (by linarith) (by linarith)
  simp_rw [hR, hL]
  rw [integral_add hih_c (hXr.const_mul _), integral_add hih_l (hXl.const_mul _),
    integral_const_mul, integral_const_mul, integral_XPk_right hX0 hc]
  simp only [ln] at hshift ⊢
  rw [hshift]
  ring

end RamanujanTau.MeanSquare
