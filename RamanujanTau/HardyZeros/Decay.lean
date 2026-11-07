/-
# Exponential decay of `Λ(Δ, 6+it)` on the critical line

`Λ(6+it) = (2π)^{−6−it} Γ(6+it) L(Δ,6+it)`, with Stirling (`|Γ(6+it)| ≪ (1+|t|)^{11/2} e^{−π|t|/2}`)
and the convexity bound (`|L(Δ,6+it)| ≪ 1+|t|`).  Hence for every `b < π/2`

    ‖Λ(6+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹.
-/
import RamanujanTau.HeckeConvex.Convex
import RamanujanTau.Stirling.Absolute
import RamanujanTau.HeckeZeros.Zeros

set_option autoImplicit false

namespace RamanujanTau.HardyZeros

open Complex MeasureTheory Set
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex
open scoped Real

/-- `(1+x)^n ≤ K e^{cx}` for `x ≥ 0`. -/
lemma one_add_pow_le_exp {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ n ≤ K * Real.exp (c * x) := by
  set κ : ℝ := min 1 (c / (n + 1)) with hκ
  have hκpos : 0 < κ := lt_min one_pos (by positivity)
  refine ⟨(κ ^ n)⁻¹, by positivity, fun x hx => ?_⟩
  have h1 : κ * (1 + x) ≤ Real.exp (c / (n + 1) * x) := by
    have := Real.add_one_le_exp (c / (n + 1) * x)
    have h2 : κ * (1 + x) ≤ 1 + c / (n + 1) * x := by
      have a1 : κ ≤ 1 := min_le_left _ _
      have a2 : κ ≤ c / (n + 1) := min_le_right _ _
      nlinarith
    linarith
  have h3 : (κ * (1 + x)) ^ n ≤ Real.exp (c / (n + 1) * x) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  rw [← Real.exp_nat_mul, mul_pow] at h3
  have h4 : Real.exp (n * (c / (n + 1) * x)) ≤ Real.exp (c * x) := by
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) * (c / (n + 1)) ≤ c := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have h3' : (1 + x) ^ n ≤ Real.exp (n * (c / (n + 1) * x)) / κ ^ n := by
    rw [le_div_iff₀ (pow_pos hκpos n)]; linarith
  calc (1 + x) ^ n ≤ Real.exp (n * (c / (n + 1) * x)) / κ ^ n := h3'
    _ ≤ Real.exp (c * x) / κ ^ n := by gcongr
    _ = (κ ^ n)⁻¹ * Real.exp (c * x) := by ring

/-- The polynomial-times-Gaussian-free bound `‖Λ(6+it)‖ ≤ K (1+|t|)^7 e^{−π|t|/2}`. -/
lemma norm_heckeLambda_line_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖heckeLambda (6 + t * I)‖ ≤ K * (1 + |t|) ^ 7 * Real.exp (-(π * |t|) / 2) := by
  obtain ⟨C, hC0, hC⟩ := tauL_convexity (ε := 1 / 2) (by norm_num)
  set G : ℝ := ((4 + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π)
  have hG0 : 0 ≤ G := by positivity
  refine ⟨G * 2 ^ 6 * C, by positivity, fun t => ?_⟩
  have hs : ∀ n : ℕ, (6 + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp)
  rw [heckeLambda_eq_tauL hs, norm_mul, norm_mul]
  -- the exponential factor
  have h2π : ‖(2 * π : ℂ) ^ (-(6 + t * I))‖ ≤ 1 := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [neg_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
    norm_num
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [Real.pi_gt_three]))
  -- Stirling
  have hΓ := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := 6) (by norm_num) 4
    (by norm_num) t
  have e6 : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
  rw [e6] at hΓ
  set Tn := ‖(3 / 2 : ℂ) + t * I‖ with hTn
  have hT1 : 1 ≤ Tn := RamanujanTau.Stirling.one_le_norm_of_re (by simp; norm_num)
  have hTle : Tn ≤ 2 * (1 + |t|) := by
    refine (norm_add_le _ _).trans ?_
    have : ‖(t : ℂ) * I‖ = |t| := by simp
    rw [this]
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]
      norm_num
    rw [this]; linarith [abs_nonneg t]
  have hTpow : Tn ^ ((6 : ℝ) - 1 / 2) ≤ (2 * (1 + |t|)) ^ 6 := by
    calc Tn ^ ((6 : ℝ) - 1 / 2) ≤ Tn ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = Tn ^ 6 := Real.rpow_natCast _ _
      _ ≤ (2 * (1 + |t|)) ^ 6 := pow_le_pow_left₀ (by positivity) hTle 6
  have hΓ' : ‖Complex.Gamma (6 + t * I)‖ ≤ G * (2 * (1 + |t|)) ^ 6 *
      Real.exp (-(π * |t|) / 2) := by
    refine hΓ.trans ?_
    have := mul_le_mul_of_nonneg_left hTpow hG0
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  -- convexity
  have hL := hC t
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at hL
  calc ‖(2 * π : ℂ) ^ (-(6 + t * I))‖ * ‖Complex.Gamma (6 + t * I)‖ * ‖tauL (6 + t * I)‖
      ≤ 1 * (G * (2 * (1 + |t|)) ^ 6 * Real.exp (-(π * |t|) / 2)) * (C * (1 + |t|)) := by
        gcongr
    _ = G * 2 ^ 6 * C * (1 + |t|) ^ 7 * Real.exp (-(π * |t|) / 2) := by ring

/-- **Decay on the critical line**: for every `b < π/2`,
`‖Λ(6+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹`. -/
theorem heckeLambda_line_decay {b : ℝ} (hb : b < π / 2) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖heckeLambda (6 + t * I)‖ * (1 + |t|) * Real.exp (b * |t|) ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := norm_heckeLambda_line_le
  obtain ⟨K₁, hK₁0, hK₁⟩ := one_add_pow_le_exp (c := π / 2 - b) (by linarith) 10
  refine ⟨K * K₁, fun t => ?_⟩
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h1 := hK t
  have h2 := hK₁ |t| ht0
  have hexp : Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
      Real.exp ((π / 2 - b) * |t|) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  calc ‖heckeLambda (6 + t * I)‖ * (1 + |t|) * Real.exp (b * |t|) * (1 + t ^ 2)
      ≤ (K * (1 + |t|) ^ 7 * Real.exp (-(π * |t|) / 2)) * (1 + |t|) * Real.exp (b * |t|) *
          (1 + |t|) ^ 2 := by gcongr
    _ = K * (1 + |t|) ^ 10 * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by ring
    _ ≤ K * (K₁ * Real.exp ((π / 2 - b) * |t|)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by gcongr
    _ = K * K₁ * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
          Real.exp ((π / 2 - b) * |t|)) := by ring
    _ = K * K₁ := by rw [hexp, mul_one]

lemma continuous_heckeLambda_line : Continuous fun t : ℝ => heckeLambda (6 + t * I) :=
  heckeLambda_entire.continuous.comp (by fun_prop)

/-- Integrability of `‖Λ(6+it)‖ (1+|t|) e^{b|t|}` for `b < π/2`. -/
theorem integrable_heckeLambda_line {b : ℝ} (hb : b < π / 2) :
    Integrable fun t : ℝ => ‖heckeLambda (6 + t * I)‖ * (1 + |t|) * Real.exp (b * |t|) := by
  obtain ⟨C, hC⟩ := heckeLambda_line_decay hb
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_heckeLambda_line.norm.mul (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hC t

end RamanujanTau.HardyZeros
