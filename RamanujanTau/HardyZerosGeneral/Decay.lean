/-
# Exponential decay of `Λ(f, k/2+it)` on the critical line, for a level-one cusp form `f`

`Λ(f,k/2+it) = (2π)^{−k/2−it} Γ(k/2+it) L(f,k/2+it)`; Stirling
(`|Γ(k/2+it)| ≪ (1+|t|)^{k} e^{−π|t|/2}`, crude) and the convexity bound
(`|L(f,k/2+it)| ≪ 1+|t|`, `fL_convexity` with `ε = 1/2`) give, for every `b < π/2`,

    ‖Λ(f,k/2+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹.
-/
import RamanujanTau.HeckeConvexGeneral.Convex
import RamanujanTau.Stirling.Absolute
import RamanujanTau.HardyZeros.Decay

set_option autoImplicit false

namespace RamanujanTau.HardyZerosGeneral

open Complex MeasureTheory Set ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

variable {k : ℕ}

/-- The point `k/2 + it` of the critical line. -/
noncomputable def sc (k : ℕ) (t : ℝ) : ℂ := (((k : ℝ) / 2 : ℝ) : ℂ) + t * I

lemma sc_re (t : ℝ) : (sc k t).re = (k : ℝ) / 2 := by simp [sc]

lemma sc_ne_neg_nat (hk : 1 ≤ k) (t : ℝ) (n : ℕ) : sc k t ≠ -n := by
  intro h
  have := congrArg Complex.re h
  rw [sc_re] at this
  simp only [neg_re, natCast_re] at this
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `‖Λ(f,k/2+it)‖ ≤ K (1+|t|)^{k+1} e^{−π|t|/2}`. -/
lemma norm_heckeLambda_line_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖heckeLambda f (sc k t)‖ ≤ K * (1 + |t|) ^ (k + 1) * Real.exp (-(π * |t|) / 2) := by
  obtain ⟨C, hC0, hC⟩ := fL_convexity f (ε := 1 / 2) (by norm_num)
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set G : ℝ := ((k + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π)
  have hG0 : 0 ≤ G := by positivity
  refine ⟨G * 2 ^ k * C, by positivity, fun t => ?_⟩
  rw [heckeLambda_eq_fL f (sc_ne_neg_nat (by omega) t), norm_mul, norm_mul]
  have h2π : ‖(2 * π : ℂ) ^ (-(sc k t))‖ ≤ 1 := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, sc_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three]) (by linarith)
  have hΓ := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := (k : ℝ) / 2) (by linarith) k
    (by linarith) t
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
  have hTpow : Tn ^ ((k : ℝ) / 2 - 1 / 2) ≤ (2 * (1 + |t|)) ^ k := by
    calc Tn ^ ((k : ℝ) / 2 - 1 / 2) ≤ Tn ^ ((k : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = Tn ^ k := Real.rpow_natCast _ _
      _ ≤ (2 * (1 + |t|)) ^ k := pow_le_pow_left₀ (by positivity) hTle k
  have hΓ' : ‖Complex.Gamma (sc k t)‖ ≤ G * (2 * (1 + |t|)) ^ k *
      Real.exp (-(π * |t|) / 2) := by
    refine hΓ.trans ?_
    have := mul_le_mul_of_nonneg_left hTpow hG0
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hL := hC t
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at hL
  calc ‖(2 * π : ℂ) ^ (-(sc k t))‖ * ‖Complex.Gamma (sc k t)‖ * ‖fL f (sc k t)‖
      ≤ 1 * (G * (2 * (1 + |t|)) ^ k * Real.exp (-(π * |t|) / 2)) * (C * (1 + |t|)) := by
        gcongr; exact hL
    _ = G * 2 ^ k * C * (1 + |t|) ^ (k + 1) * Real.exp (-(π * |t|) / 2) := by
        rw [mul_pow, pow_succ]; ring

/-- **Decay on the critical line**: for every `b < π/2`,
`‖Λ(f,k/2+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹`. -/
theorem heckeLambda_line_decay (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {b : ℝ}
    (hb : b < π / 2) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖heckeLambda f (sc k t)‖ * (1 + |t|) * Real.exp (b * |t|) ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := norm_heckeLambda_line_le f hk
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    RamanujanTau.HardyZeros.one_add_pow_le_exp (c := π / 2 - b) (by linarith) (k + 4)
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
  calc ‖heckeLambda f (sc k t)‖ * (1 + |t|) * Real.exp (b * |t|) * (1 + t ^ 2)
      ≤ (K * (1 + |t|) ^ (k + 1) * Real.exp (-(π * |t|) / 2)) * (1 + |t|) * Real.exp (b * |t|) *
          (1 + |t|) ^ 2 := by gcongr
    _ = K * (1 + |t|) ^ (k + 4) * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by ring
    _ ≤ K * (K₁ * Real.exp ((π / 2 - b) * |t|)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by gcongr
    _ = K * K₁ * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
          Real.exp ((π / 2 - b) * |t|)) := by ring
    _ = K * K₁ := by rw [hexp, mul_one]

lemma continuous_heckeLambda_line (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    Continuous fun t : ℝ => heckeLambda f (sc k t) :=
  (heckeLambda_entire f hk).continuous.comp (by unfold sc; fun_prop)

/-- Integrability of `‖Λ(f,k/2+it)‖ (1+|t|) e^{b|t|}` for `b < π/2`. -/
theorem integrable_heckeLambda_line (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {b : ℝ}
    (hb : b < π / 2) :
    Integrable fun t : ℝ => ‖heckeLambda f (sc k t)‖ * (1 + |t|) * Real.exp (b * |t|) := by
  obtain ⟨C, hC⟩ := heckeLambda_line_decay f hk hb
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact (((continuous_heckeLambda_line f (by omega)).norm.mul (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hC t

end RamanujanTau.HardyZerosGeneral
