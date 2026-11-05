/-
# Window lower bound from the rectangle `[6, σ₁] × [a, b]` (no kernel)

Cauchy's theorem for `L(Δ,s)` on the rectangle gives

    i ∫_a^b L(6+iy) dy = ∫_6^{σ₁} L(x+ia) dx − ∫_6^{σ₁} L(x+ib) dx + i ∫_a^b L(σ₁+iy) dy.

If `|L(σ₁+iy) − 1| ≤ 1/4` the right side is `≥ 3(b−a)/4`, and the horizontal sides are bounded by
`F(a), F(b)` with `F(c) = ∫_6^{σ₁} |L(x+ic)| dx`.  So `F(a), F(b) ≤ (b−a)/8` gives
`∫_a^b |L(6+iy)| dy ≥ (b−a)/2`.  Compared with `HardyCountLinear.kernel_lower` there is no
kernel: the horizontal sides are controlled on average (`Horizontal.horizontal_mean`), not
pointwise.
-/
import RamanujanTau.HardyCountHafner.Horizontal

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL
open scoped Real

theorem window_lower {σ₁ : ℝ} (h7 : 7 ≤ σ₁) (hρ : ∀ y : ℝ, ‖tauL (σ₁ + y * I) - 1‖ ≤ 1 / 4)
    {a b : ℝ} (hab : a ≤ b) (ha : Fh σ₁ a ≤ (b - a) / 8) (hb : Fh σ₁ b ≤ (b - a) / 8) :
    (b - a) / 2 ≤ ∫ t in a..b, ‖tauL (6 + t * I)‖ := by
  set f : ℂ → ℂ := tauL with hfdef
  have hfd : Differentiable ℂ f := tauLSeries_entire
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((6 : ℂ) + a * I) ((σ₁ : ℂ) + b * I) hfd.differentiableOn
  have e1 : ((6 : ℂ) + a * I).re = 6 := by simp
  have e2 : ((6 : ℂ) + a * I).im = a := by simp
  have e3 : ((σ₁ : ℂ) + b * I).re = σ₁ := by simp
  have e4 : ((σ₁ : ℂ) + b * I).im = b := by simp
  rw [e1, e2, e3, e4] at hrect
  set Ha := ∫ x : ℝ in (6 : ℝ)..σ₁, f (x + a * I) with hHa
  set Hb := ∫ x : ℝ in (6 : ℝ)..σ₁, f (x + b * I) with hHb
  set X := ∫ y : ℝ in a..b, f (σ₁ + y * I) with hX
  set Y := ∫ y : ℝ in a..b, f (((6 : ℝ) : ℂ) + y * I) with hY
  have hEq : I • Y = Ha - Hb + I • X := by linear_combination -hrect
  have h6σ : (6 : ℝ) ≤ σ₁ := by linarith
  have hHa' : ‖Ha‖ ≤ (b - a) / 8 :=
    (intervalIntegral.norm_integral_le_integral_norm h6σ).trans ha
  have hHb' : ‖Hb‖ ≤ (b - a) / 8 :=
    (intervalIntegral.norm_integral_le_integral_norm h6σ).trans hb
  -- the right side
  have hcR : Continuous fun y : ℝ => f (σ₁ + y * I) := hfd.continuous.comp (by fun_prop)
  have hXsub : X - ((b - a : ℝ) : ℂ) = ∫ y : ℝ in a..b, (f (σ₁ + y * I) - 1) := by
    rw [intervalIntegral.integral_sub (hcR.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [hX]
  have hXb : ‖X - ((b - a : ℝ) : ℂ)‖ ≤ (b - a) / 4 := by
    rw [hXsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1 / 4) (f := fun y : ℝ => f (σ₁ + y * I) - 1)
      (fun y _ => hρ y)
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hXl : 3 * (b - a) / 4 ≤ ‖X‖ := by
    have h1 := norm_sub_norm_le (((b - a : ℝ) : ℂ)) X
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
    linarith
  have hYl : (b - a) / 2 ≤ ‖Y‖ := by
    have hn : ‖Y‖ = ‖I • Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [hn, hEq]
    have h3 : ‖I • X‖ = ‖X‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 := norm_sub_norm_le (I • X) (-(Ha - Hb))
    rw [sub_neg_eq_add, norm_neg, h3, add_comm] at h1
    have h2 := norm_sub_le Ha Hb
    linarith
  refine hYl.trans ?_
  have e6 : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
  rw [hY, e6]
  exact intervalIntegral.norm_integral_le_integral_norm hab

end RamanujanTau.HardyCountHafner
