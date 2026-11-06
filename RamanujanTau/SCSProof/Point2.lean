/-
# Pointwise bound for `G_h`, part 2: assembly

`pointwise_G`: there is `K` with, for `h ≥ 1`, `0 < σ ≤ 1`, `hσ ≤ 1`,
`‖G_h(σ + iτ)‖ ≤ K h (|2τ/σ| + 3)³² σ^{−12 + 3/40}`.
(Trivial bound: `≪ σ^{−12}`; saving `σ^{3/40}` at polynomial cost in `τ/σ` and `h`.)
-/
import RamanujanTau.SCSProof.Point1

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal Real ComplexConjugate

lemma sqrt_mul_sqrt_le {a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) :
    Real.sqrt a * Real.sqrt b ≤ (l * a + b / l) / 2 := by
  have h1 : 0 ≤ (Real.sqrt (l * a) - Real.sqrt (b / l)) ^ 2 := sq_nonneg _
  have e1 : Real.sqrt (l * a) * Real.sqrt (b / l) = Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul ha]
    congr 1; field_simp
  have e2 : Real.sqrt (l * a) ^ 2 = l * a := Real.sq_sqrt (by positivity)
  have e3 : Real.sqrt (b / l) ^ 2 = b / l := Real.sq_sqrt (by positivity)
  nlinarith

/-- `T(s) ≤ 2 C₀ s^{−12}` once `h s ≤ 1`. -/
lemma laplace_le_of {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (h : ℕ) {s : ℝ} (hs : 0 < s) (hhs : h * s ≤ 1)
    (hb : ∑' n : ℕ, aabs h n * Real.exp (-n * s) ≤ (1 + Real.exp (h * s)) / 2 * (C₀ * s ^ (-(12 : ℝ)))) :
    ∑' n : ℕ, aabs h n * Real.exp (-n * s) ≤ 2 * C₀ * (1 / s ^ 12) := by
  refine hb.trans ?_
  have he : Real.exp (h * s) ≤ 3 := by
    calc Real.exp (h * s) ≤ Real.exp 1 := Real.exp_le_exp.2 hhs
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hr : s ^ (-(12 : ℝ)) = 1 / s ^ 12 := by
    rw [Real.rpow_neg hs.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  rw [hr]
  have : 0 ≤ C₀ * (1 / s ^ 12) := by positivity
  nlinarith

end RamanujanTau.SCSProof
