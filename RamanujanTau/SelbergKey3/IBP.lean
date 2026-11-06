/-
# M2 building block: two-fold integration by parts against `e^{iωt}`

If `g` is `C²` on `[A, B]` with `g = g' = 0` at both ends and `ω ≠ 0`, then

    ∫_A^B g(t) e^{iωt} dt = −ω^{−2} ∫_A^B g''(t) e^{iωt} dt,   |·| ≤ ω^{−2} ∫_A^B |g''|.

This is the off-diagonal saving for the frequencies `ω = log(bdn/acm) ≠ 0` of
`SelbergKey.Expand.OffLag` once the amplitude `φ(t)·U·W̃` is known to be `C²` with
`∂^j ≪ T^{−j}` (`LagDeriv.Wlag_iteratedDeriv_bound` for `W̃`).  Level 1.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergKey3

open Complex MeasureTheory Set intervalIntegral

lemma hasDerivAt_expw {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cexp ((ω * s : ℝ) * I) / ((ω : ℂ) * I)) (cexp ((ω * t : ℝ) * I)) t := by
  have hωI : (ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) I_ne_zero
  have h1 : HasDerivAt (fun s : ℝ => ((ω * s : ℝ) : ℂ) * I) ((ω : ℂ) * I) t := by
    have := ((hasDerivAt_id t).const_mul ω).ofReal_comp.mul_const I
    simpa using this
  have h2 := (h1.cexp).div_const ((ω : ℂ) * I)
  convert h2 using 1
  rw [mul_div_assoc, div_self hωI, mul_one]

/-- **One integration by parts.** -/
theorem ibp_once {g g' : ℝ → ℂ} {A B ω : ℝ} (hω : ω ≠ 0) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg'c : Continuous g') (hA : g A = 0) (hB : g B = 0) :
    ∫ t in A..B, g t * cexp ((ω * t : ℝ) * I) =
      -(((ω : ℂ) * I)⁻¹ * ∫ t in A..B, g' t * cexp ((ω * t : ℝ) * I)) := by
  have hv : ∀ x ∈ uIcc A B, HasDerivAt (fun s : ℝ => cexp ((ω * s : ℝ) * I) / ((ω : ℂ) * I))
      (cexp ((ω * x : ℝ) * I)) x := fun x _ => hasDerivAt_expw hω x
  have hcont : Continuous fun t : ℝ => cexp ((ω * t : ℝ) * I) := by fun_prop
  have h := integral_mul_deriv_eq_deriv_mul (fun x _ => hg x) hv (hg'c.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)
  rw [h, hA, hB, zero_mul, zero_mul, sub_zero, zero_sub]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t; field_simp

/-- **Two integrations by parts**, with the norm bound `ω^{−2} ∫ |g''|`. -/
theorem ibp_twice {g g' g'' : ℝ → ℂ} {A B ω : ℝ} (hω : ω ≠ 0) (hAB : A ≤ B)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hg''c : Continuous g'') (hA : g A = 0) (hB : g B = 0) (hA' : g' A = 0) (hB' : g' B = 0) :
    ‖∫ t in A..B, g t * cexp ((ω * t : ℝ) * I)‖ ≤ (ω ^ 2)⁻¹ * ∫ t in A..B, ‖g'' t‖ := by
  have hg'c : Continuous g' := continuous_iff_continuousAt.2 fun t => (hg' t).continuousAt
  rw [ibp_once hω hg hg'c hA hB, ibp_once hω hg' hg''c hA' hB']
  have hn : ‖((ω : ℂ) * I)⁻¹‖ = |ω|⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_neg, norm_mul, norm_neg, norm_mul, hn, ← mul_assoc, ← mul_inv, ← sq, sq_abs]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm hAB).trans (le_of_eq ?_)
  congr 1; funext t
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

end RamanujanTau.SelbergKey3
