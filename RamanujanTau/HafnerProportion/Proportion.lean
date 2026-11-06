/-
# Positive proportion against Riemann–von Mangoldt

With `ZeroCountRvM.riemann_von_mangoldt` (`N(X) = (X/π) log(X/2πe) + O(log X)`, with
multiplicity), `tauL_critical_zeros_T_log_T_of_selberg` becomes a genuine proportion:
the number of distinct critical ordinates in `(0, 3T]` is `≥ c · N(3T)`.
-/
import RamanujanTau.HafnerProportion.Selberg
import RamanujanTau.ZeroCountRvM.RvM

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open Complex
open RamanujanTau.HeckeL RamanujanTau.ZeroCount
open scoped Real

/-- `N(3T) ≤ A · T log T` for `T ≥ 3`. -/
lemma zeroCount_three_le : ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 3 ≤ T →
    (zeroCount (3 * T) : ℝ) ≤ A * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.ZeroCountRvM.riemann_von_mangoldt
  refine ⟨6 / π + 2 * C + 1, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have h3 := hC (3 * T) (by linarith)
  have hlog3 : Real.log (3 * T) ≤ 2 * Real.log T := by
    rw [two_mul, ← Real.log_mul hT0.ne' hT0.ne']
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hpe : 1 ≤ 2 * π * Real.exp 1 := by
    have := Real.pi_gt_three
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have hl2 : Real.log (3 * T / (2 * π * Real.exp 1)) ≤ Real.log (3 * T) :=
    Real.log_le_log (by positivity) (div_le_self (by positivity) hpe)
  have hmain : 3 * T / π * Real.log (3 * T / (2 * π * Real.exp 1)) ≤ 6 / π * T * Real.log T := by
    have h0 : 0 ≤ 3 * T / π := by positivity
    calc 3 * T / π * Real.log (3 * T / (2 * π * Real.exp 1))
        ≤ 3 * T / π * (2 * Real.log T) := mul_le_mul_of_nonneg_left (hl2.trans hlog3) h0
      _ = 6 / π * T * Real.log T := by ring
  have hCl : C * Real.log (3 * T) ≤ 2 * C * T * Real.log T := by
    have : C * Real.log (3 * T) ≤ C * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlog3 hC0
    have h2 : 2 * C * Real.log T ≤ 2 * C * T * Real.log T := by
      have : 0 ≤ 2 * C * Real.log T := by positivity
      nlinarith
    linarith
  have habs := (abs_le.mp h3).2
  have hTl : 0 ≤ T * Real.log T := by positivity
  nlinarith

/-- **Hafner's positive proportion, conditional on `SelbergHyp`**: a positive proportion of the
zeros of `L(Δ,s)` up to height `3T` (Riemann–von Mangoldt count, with multiplicity) are distinct
zeros on the critical line `Re s = 6`. -/
theorem tauL_positive_proportion_of_selberg (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (zeroCount (3 * T) : ℝ) ≤ S.card := by
  obtain ⟨c, T₀, hc, hcount⟩ := tauL_critical_zeros_T_log_T_of_selberg H
  obtain ⟨A, hA, hN⟩ := zeroCount_three_le
  refine ⟨c / A, max T₀ 3, by positivity, fun T hT => ?_⟩
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨S, hS, hcard⟩ := hcount T (le_trans (le_max_left _ _) hT)
  refine ⟨S, fun γ hγ => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hS γ hγ
    exact ⟨by linarith, h2, h3⟩
  · have hN3 := hN T hT3
    calc c / A * (zeroCount (3 * T) : ℝ) ≤ c / A * (A * T * Real.log T) :=
          mul_le_mul_of_nonneg_left hN3 (by positivity)
      _ = c * T * Real.log T := by field_simp
      _ ≤ S.card := hcard

end RamanujanTau.HafnerProportion
