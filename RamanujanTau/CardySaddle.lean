import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The Cardy saddle algebra

An isolated port of the completion-of-the-square argument in unifiedtheory's
`KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy`.
These are real-variable identities and inequalities; coefficient asymptotics
and a physical interpretation require separate proofs.

The parameter `C` follows unifiedtheory's normalization. In particular, the
ordinary partition exponent corresponds to `C = 1/12`.
-/

set_option autoImplicit false

namespace Cardy

noncomputable def saddleExponent (C E β : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * C / β + β * E

noncomputable def leadingEntropy (C E : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (2 * C * E)

/-- Exact nonnegative error above the balanced saddle value. -/
theorem saddle_sub_leading (C E β : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hβ : 0 < β) :
    saddleExponent C E β - leadingEntropy C E =
      (Real.sqrt (2 * Real.pi ^ 2 * C / β) - Real.sqrt (β * E)) ^ 2 := by
  have hA : 0 ≤ 2 * Real.pi ^ 2 * C / β := by positivity
  have hB : 0 ≤ β * E := by positivity
  have hAB : (2 * Real.pi ^ 2 * C / β) * (β * E) =
      Real.pi ^ 2 * (2 * C * E) := by field_simp
  have hsqrt : Real.sqrt (2 * Real.pi ^ 2 * C / β) * Real.sqrt (β * E) =
      Real.pi * Real.sqrt (2 * C * E) := by
    rw [← Real.sqrt_mul hA, hAB, Real.sqrt_mul (sq_nonneg Real.pi),
      Real.sqrt_sq Real.pi_pos.le]
  unfold saddleExponent leadingEntropy
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- A lower bound on the saddle expression, not a bound on a state count. -/
theorem leading_le_saddle (C E β : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hβ : 0 < β) :
    leadingEntropy C E ≤ saddleExponent C E β := by
  have := saddle_sub_leading C E β hC hE hβ
  nlinarith [sq_nonneg (Real.sqrt (2 * Real.pi ^ 2 * C / β) - Real.sqrt (β * E))]

/-- The lower bound is attained when the two saddle terms balance. -/
theorem saddle_eq_leading_of_balance (C E β : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hβ : 0 < β)
    (hbalance : 2 * Real.pi ^ 2 * C / β = β * E) :
    saddleExponent C E β = leadingEntropy C E := by
  have h := saddle_sub_leading C E β hC hE hβ
  rw [hbalance, sub_self, zero_pow (by decide)] at h
  exact sub_eq_zero.mp h

end Cardy
