/-
# Good's mean-square asymptotic for every nonzero level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0` (so `k` is even and `k ≥ 12`):

    ∫_0^T |L(f, k/2+it)|² dt / (T log T) → c_f = 2 · rsConst f = 2 (3/π)(4π)^k ‖f‖² / (k−1)!

(`fL_critical_mean_square_asymptotic`), together with the weighted form
(`fL_weighted_asymptotic`) and the two-sided bound `≍ T log T`
(`fL_critical_mean_square_two_sided`).  At `f = Δ` the constant is the `cDelta` of
`CriticalMeanSquareAsymp` (`fL_discriminant_critical_mean_square_asymptotic`).
-/
import RamanujanTau.GeneralCuspMoments.CuspLaplace
import RamanujanTau.HardyZerosGeneral.Main
import RamanujanTau.CriticalMeanSquareAsymp.Final
import RamanujanTau.RankinSelbergGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex ModularForm MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
open scoped MatrixGroups Real

variable {k : ℕ}

/-- Good's constant `c_f = 2 · rsConst f`, twice the Rankin–Selberg constant of
`RankinSelbergGeneral.rankinSelberg_asymptotic` / `RankinExact.rankinSelberg_exact_general`. -/
noncomputable def cF (f : CuspForm 𝒮ℒ (k : ℤ)) : ℝ := 2 * RankinSelbergGeneral.rsConst f

theorem cF_eq (f : CuspForm 𝒮ℒ (k : ℤ)) :
    cF f = 2 * (3 / π * (4 * π) ^ k * RankinSelbergGeneral.petNormSqF f /
      (Nat.factorial (k - 1) : ℝ)) := rfl

theorem cF_pos (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : 0 < cF f := by
  have := RankinSelbergGeneral.rsConst_pos f hf
  unfold cF; positivity

/-- A nonzero level-one cusp form has weight `k = 2p + 2` with `12 ≤ k`. -/
lemma exists_weight_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ p : ℕ, k = 2 * p + 2 ∧ 12 ≤ 2 * p + 2 := by
  have hk12 : 12 ≤ k := by
    by_contra h
    exact hf (eq_zero_of_lt_twelve f (by omega))
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | h
  · exact ⟨j - 1, by omega, by omega⟩
  · exact absurd (eq_zero_of_odd f h) hf

lemma crit_point (k : ℕ) (t : ℝ) : (k : ℂ) / 2 + t * I = sc k t := by
  unfold sc; push_cast; ring

/-- **Good's theorem (1982) for every nonzero level-one cusp form `f` of weight `k`:**
`∫_0^T |L(f, k/2+it)|² dt / (T log T) → c_f = 2 · (3/π)(4π)^k ‖f‖² / (k−1)!`. -/
theorem fL_critical_mean_square_asymptotic (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2) / (T * Real.log T))
      atTop (𝓝 (cF f)) := by
  obtain ⟨p, rfl, hk⟩ := exists_weight_eq f hf
  have h := critical_mean_square_asymptotic_f f hk
  refine h.congr fun T => ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [crit_point]; rfl

/-- **Two-sided bound** `c₁ T log T ≤ ∫_0^T |L(f,k/2+it)|² dt ≤ c₂ T log T` for large `T`. -/
theorem fL_critical_mean_square_two_sided (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ c₁ c₂ T₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 1 < T₀ ∧ ∀ T ≥ T₀,
      c₁ * (T * Real.log T) ≤ ∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2 ∧
      ∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2 ≤ c₂ * (T * Real.log T) := by
  have hc := cF_pos f hf
  have h := fL_critical_mean_square_asymptotic f hf
  have h1 := (tendsto_order.1 h).1 (cF f / 2) (by linarith)
  have h2 := (tendsto_order.1 h).2 (2 * cF f) (by linarith)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨cF f / 2, 2 * cF f, max T₁ 2, by positivity, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTL : 0 < T * Real.log T := mul_pos (by linarith) (Real.log_pos (by linarith))
  obtain ⟨ha, hb⟩ := hT₁ T (le_trans (le_max_left _ _) hT)
  rw [lt_div_iff₀ hTL] at ha
  rw [div_lt_iff₀ hTL] at hb
  exact ⟨ha.le, hb.le⟩

/-- **The weighted asymptotic for `f`** (`κ = cot β → 0⁺`):
`κ^k ∫ |Λ(f,k/2+it)|² e^{2βt} dt / log(1/κ) → 12‖f‖²`. -/
theorem fL_weighted_asymptotic (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ k *
      (∫ t : ℝ, ‖heckeLambda f ((k : ℂ) / 2 + t * I)‖ ^ 2 * Real.exp (2 * β * t)) /
        Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
      (𝓝 (12 * RankinSelbergGeneral.petNormSqF f)) := by
  obtain ⟨p, rfl, hk⟩ := exists_weight_eq f hf
  refine (weighted_asymptotic_f f hk).congr fun β => ?_
  simp only [crit_point]

/-- **The Laplace form**:
`λ^k ∫_0^∞ t^{k−1} e^{−λt} |L(f,k/2+it)|² dt / log(1/λ) → (2π)^{k−1} 2^k · 12‖f‖²`. -/
theorem fL_laplace_asymptotic (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun l : ℝ => l ^ k / Real.log (1 / l) *
      ∫ x in Ioi (0 : ℝ), x ^ (k - 1) * ‖fL f ((k : ℂ) / 2 + (x : ℂ) * I)‖ ^ 2 *
        Real.exp (-(x * l)))
      (𝓝[>] 0)
      (𝓝 ((2 * π) ^ (k - 1) * (2 ^ k * (12 * RankinSelbergGeneral.petNormSqF f)))) := by
  obtain ⟨p, rfl, hk⟩ := exists_weight_eq f hf
  have h := laplace_asymptotic_f f hk
  rw [show 2 * p + 2 - 1 = 2 * p + 1 by omega]
  refine h.congr fun l => ?_
  unfold Lap LapG Lsq
  simp only [crit_point]

/-! ### The case `f = Δ` -/

/-- **Sanity check at `f = Δ`:** the general theorem gives Good's asymptotic for
`L(Δ,s) = fL Δ`, with exactly the constant `cDelta = 2c` of
`CriticalMeanSquareAsymp.critical_mean_square_asymptotic`. -/
theorem fL_discriminant_critical_mean_square_asymptotic :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T,
      ‖fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I)‖ ^ 2) /
        (T * Real.log T)) atTop (𝓝 RamanujanTau.CriticalMeanSquareAsymp.cDelta) := by
  have h := fL_critical_mean_square_asymptotic (k := 12) _ discriminant_ne_zero'
  have hc : cF (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) =
      RamanujanTau.CriticalMeanSquareAsymp.cDelta := by
    rw [cF_eq, RamanujanTau.CriticalMeanSquareAsymp.cDelta_eq,
      RankinSelbergGeneral.petNormSqF_discriminant]
  rw [hc] at h
  refine h.congr fun T => ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  have e : ((12 : ℕ) : ℂ) / 2 = 6 := by norm_num
  simp only [e]

end RamanujanTau.GeneralCuspMoments
