/-
# The mean square of `L(Δ,s)` on every vertical line

| line            | asymptotic                                                  | source                          |
|-----------------|-------------------------------------------------------------|---------------------------------|
| `σ > 6`         | `∫₀ᵀ |L(σ+it)|² ~ RS(2σ) · T`                               | `MeanSquareFull`                |
| `σ = 6`         | `∫₀ᵀ |L(6+it)|² ~ 2c · T log T`, `c` Rankin's constant      | `CriticalMeanSquareAsymp`       |
| `σ < 6`         | `∫₀ᵀ |L(σ+it)|² ~ (2π)^{4σ−24} RS(24−2σ)/(25−4σ) · T^{25−4σ}` | this directory                  |

`RS(β) = Σ τ(n)² n^{−β}`.  `mean_square_tauL_every_line` packages the three statements.
-/
import RamanujanTau.MeanSquareLeft.Left
import RamanujanTau.CriticalMeanSquareAsymp.Final

set_option autoImplicit false

namespace RamanujanTau.MeanSquareLeft

open Complex Real Filter Topology MeasureTheory Set
open RamanujanTau.HeckeL

/-- `RS(β) ≥ 1 > 0` for `β > 12` (the `n = 1` term is `τ(1)² = 1`). -/
theorem one_le_RS {β : ℝ} (hβ : 12 < β) : 1 ≤ RS β := by
  unfold RS
  have hs := summable_RS hβ
  have h := hs.le_tsum 1 (fun n _ => by positivity)
  simp [RamanujanTau.tau_one] at h
  simpa using h

/-- The left-line constant is positive. -/
theorem Cleft_pos {σ : ℝ} (hσ : σ < 6) : 0 < Cleft σ := by
  unfold Cleft
  have := one_le_RS (β := 2 * (12 - σ)) (by linarith)
  have : 0 < (2 * π) ^ (4 * σ - 24) := Real.rpow_pos_of_pos (by positivity) _
  have : 0 < 25 - 4 * σ := by linarith
  positivity

/-- **The mean square of `L(Δ,s)` on every vertical line.** -/
theorem mean_square_tauL_every_line :
    (∀ σ : ℝ, 6 < σ →
      Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
        (𝓝 (RS (2 * σ)))) ∧
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2) / (T * Real.log T)) atTop
      (𝓝 RamanujanTau.CriticalMeanSquareAsymp.cDelta) ∧
    (∀ σ : ℝ, σ < 6 →
      Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) /
        T ^ (25 - 4 * σ)) atTop (𝓝 (Cleft σ))) :=
  ⟨fun _ hσ => RamanujanTau.MeanSquareFull.mean_square_tauL_full hσ,
    RamanujanTau.CriticalMeanSquareAsymp.critical_mean_square_asymptotic,
    fun _ hσ => mean_square_tauL_left hσ⟩

/-- The strip `11/2 ≤ σ < 6` (the case originally requested), as a special case. -/
theorem mean_square_tauL_left_strip {σ : ℝ} (_hσ0 : 11 / 2 ≤ σ) (hσ : σ < 6) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) /
      T ^ (25 - 4 * σ)) atTop (𝓝 (Cleft σ)) :=
  mean_square_tauL_left hσ

end RamanujanTau.MeanSquareLeft

#print axioms RamanujanTau.MeanSquareLeft.mean_square_tauL_every_line
#print axioms RamanujanTau.MeanSquareLeft.mean_square_tauL_left
#print axioms RamanujanTau.MeanSquareLeft.mean_square_tauL_left_strip
#print axioms RamanujanTau.MeanSquareLeft.Cleft_pos
#print axioms RamanujanTau.MeanSquareLeft.one_le_RS
#print axioms RamanujanTau.MeanSquareLeft.norm_tauL_fe
#print axioms RamanujanTau.MeanSquareLeft.tendsto_chi_sq
#print axioms RamanujanTau.MeanSquareLeft.tendsto_Qr
#print axioms RamanujanTau.MeanSquareLeft.norm_Gamma_mul_rpow_le_sharp
#print axioms RamanujanTau.MeanSquareLeft.norm_Gamma_add_le_sharp
#print axioms RamanujanTau.MeanSquareLeft.abel_mean
#print axioms RamanujanTau.MeanSquareLeft.abel_rpow
#print axioms RamanujanTau.MeanSquareLeft.tendsto_weighted
