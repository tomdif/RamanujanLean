/-
# Cauchy–Schwarz: `|∫ Ψ conj ft| ≤ (λ A + B/λ)/4`

* `lintegral_U_le`: `μ(U) ≤ 2`.
* `two_Q_eq`: `2 ∫ Ψ conj ft = ∫_{U×ℍ} Ψ conj Pt` (unfolding).
* `normsq_Pt`: `(∫⁻_{U×ℍ} ‖Pt‖²).toReal ≤ 2 ‖Σ_γ I(γ)‖`.
* `norm_Q_le`: for every `λ > 0`,
  `‖∫ Ψ conj ft‖ ≤ (λ · 8 M² R¹⁶ + (2‖Σ_γ I(γ)‖)/λ) / 4`.
-/
import RamanujanTau.SCSProof.Bruhat8

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

/-- `∫⁻_{Ioi a} 1/y² = 1/a`. -/
lemma lintegral_Ioi_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in Ioi a, ENNReal.ofReal (1 / y ^ 2) = ENNReal.ofReal (1 / a) := by
  have hint := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha
  have hval := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha
  have e : ∀ y ∈ Ioi a, ENNReal.ofReal (1 / y ^ 2) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    intro y hy
    have hy0 : 0 < y := ha.trans hy
    congr 1
    rw [Real.rpow_neg hy0.le, one_div]; norm_cast
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun y : ℝ => y ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (ha.trans hy).le _
  rw [setLIntegral_congr_fun measurableSet_Ioi e, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    hval]
  congr 1
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- `μ(U) ≤ 2`. -/
theorem lintegral_U_le : ∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z ≤ ENNReal.ofReal 2 := by
  have hm : Measurable (Uset.indicator (1 : ℍ → ℝ≥0∞)) := measurable_one.indicator measurableSet_Uset
  rw [lintegral_H _ hm]
  have hle : ∀ p ∈ {p : ℝ × ℝ | 0 < p.2}, Uset.indicator (1 : ℍ → ℝ≥0∞) (toH p) *
      ENNReal.ofReal (1 / p.2 ^ 2) ≤
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator 1 p.1 *
        (Ioi (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 := by
    intro p hp
    by_cases hU : toH p ∈ Uset
    · obtain ⟨h1, h2, h3⟩ := hU
      rw [toH_re hp] at h1 h2
      have hnorm : Complex.normSq ((toH p : ℍ) : ℂ) = p.1 ^ 2 + p.2 ^ 2 := by
        rw [coe_toH hp, Complex.normSq_apply]; simp; ring
      rw [hnorm] at h3
      have hy : 1 / 2 < p.2 := by
        have : (1 / 2 : ℝ) ^ 2 < p.2 ^ 2 := by nlinarith
        have hp2 : 0 < p.2 := hp
        nlinarith
      rw [indicator_of_mem (show toH p ∈ Uset from ⟨by rwa [toH_re hp], by rwa [toH_re hp], by
        rwa [hnorm]⟩), indicator_of_mem (show p.1 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) from ⟨h1, h2.le⟩),
        indicator_of_mem (show p.2 ∈ Ioi (1 / 2 : ℝ) from hy)]
      simp
    · rw [indicator_of_notMem hU]; simp
  calc ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, Uset.indicator (1 : ℍ → ℝ≥0∞) (toH p) *
        ENNReal.ofReal (1 / p.2 ^ 2)
      ≤ ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator 1 p.1 *
          (Ioi (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 :=
        setLIntegral_mono' (measurableSet_lt measurable_const measurable_snd) hle
    _ ≤ ∫⁻ p : ℝ × ℝ, (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator 1 p.1 *
          (Ioi (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 :=
        setLIntegral_le_lintegral _ _
    _ = (∫⁻ x, (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator 1 x) *
          ∫⁻ y, (Ioi (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) y := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul ((measurable_one.indicator measurableSet_Icc).aemeasurable)
          (((ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const 2))).indicator
            measurableSet_Ioi).aemeasurable)
    _ = ENNReal.ofReal 2 := by
        rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ioi,
          lintegral_Ioi_inv_sq (by norm_num)]
        simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          univ_inter, Real.volume_Icc, one_mul]
        rw [← ENNReal.ofReal_mul (by norm_num)]
        norm_num

end RamanujanTau.SCSProof
