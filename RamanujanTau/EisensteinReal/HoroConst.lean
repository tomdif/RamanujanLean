/-
# The constants: `κ = 6/π²`, `W = π/4`, `K₀ = 6/π`

So the rectangle-count limit is `(6/π)(β − α)/A = 2 · (3/π) · μ_hyp([α,β) × [A,∞))`
(the factor `2` because `±γ` are both counted): Zagier's `3/π` appears.
-/
import RamanujanTau.EisensteinReal.HoroSandwich
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Real Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius LSeries.notation

theorem Wc_eq : Wc = π / 4 := by
  have h := integral_sqrt_one_sub_sq
  have hI : ∀ a b : ℝ, IntervalIntegrable wfun MeasureTheory.volume a b := wfun_ii
  change ∫ x in (-1 : ℝ)..1, wfun x = π / 2 at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hI _ _) (hI _ _)] at h
  have hneg : ∫ x in (-1 : ℝ)..0, wfun x = ∫ x in (0 : ℝ)..1, wfun x := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) wfun
    simp only [neg_zero] at this
    rw [← this]
    congr 1; funext x; simp [wfun]
  change (∫ x in (-1 : ℝ)..0, wfun x) + ∫ x in (0 : ℝ)..1, wfun x = π / 2 at h
  rw [hneg] at h
  unfold Wc
  linarith

theorem kappa_eq : kappa = 6 / π ^ 2 := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hL := LSeries_one_mul_Lseries_moebius h2
  rw [LSeries_one_eq_riemannZeta h2, riemannZeta_two] at hL
  have hμ : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = ((kappa : ℝ) : ℂ) := by
    unfold LSeries kappa
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn]
      push_cast
      rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have hμ' : LSeries (↗μ) 2 = ((kappa : ℝ) : ℂ) := hμ
  rw [hμ'] at hL
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : ((kappa : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by
    field_simp at hL ⊢
    linear_combination hL
  have h' : ((kappa : ℝ) : ℂ) = ((6 / π ^ 2 : ℝ) : ℂ) := by rw [this]; push_cast; rfl
  exact_mod_cast h'

theorem K0_eq : K0 = 6 / π := by
  unfold K0
  rw [kappa_eq, Wc_eq]
  field_simp

/-- **Rectangle count, with the constant:** `∫₀¹ #{γ : γ(x+iy) ∈ [α,β)×[A,∞)} dx → (6/π)(β−α)/A`. -/
theorem tendsto_horoR_const {α β A : ℝ} (hαβ : α ≤ β) (hA : 0 < A) :
    Tendsto (horoR α β A) (𝓝[>] 0) (𝓝 (6 / π * ((β - α) / A))) := by
  have h := tendsto_horoR hαβ hA
  have e : 4 * (β - α) / A * (kappa * Wc) = 6 / π * ((β - α) / A) := by
    rw [kappa_eq, Wc_eq]; field_simp
  rwa [e] at h

end RamanujanTau.EisensteinReal.Horo

#print axioms RamanujanTau.EisensteinReal.Horo.kappa_eq
#print axioms RamanujanTau.EisensteinReal.Horo.Wc_eq
#print axioms RamanujanTau.EisensteinReal.Horo.tendsto_horoR_const
