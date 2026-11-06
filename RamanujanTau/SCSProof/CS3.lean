/-
# Cauchy–Schwarz, part 3: `‖∫ Ψ conj ft‖ ≤ ½ (M R⁶) √(8R⁴) √(2‖Σ_γ I(γ)‖)`
-/
import RamanujanTau.SCSProof.CS2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma enorm_Psi_ft_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (p : ℍ × ℍ) :
    ‖Psi p.1 p.2‖ₑ * ‖ft P p‖ₑ ≤ ENNReal.ofReal (M * Rθ P ^ 6) * ‖ft P p‖ₑ := by
  by_cases h : ft P p = 0
  · simp [h]
  gcongr
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ((norm_Psi_le_Dh hM p.1 p.2).trans ?_)
  have hD := Dh_le_of_ft P p h
  have hD0 : 0 ≤ Dh p.1 p.2 := by
    unfold Dh; exact div_nonneg (Complex.normSq_nonneg _) (mul_pos p.1.im_pos p.2.im_pos).le
  gcongr

/-- **Unfolding `Ψ`.** -/
theorem two_Q_eq {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ∫ p, indUC p * (Psi p.1 p.2 * conj (Pt P p)) = 2 * ∫ p, Psi p.1 p.2 * conj (ft P p) := by
  have hfin : ∫⁻ p, ‖Psi p.1 p.2 * conj (ft P p)‖ₑ ≠ ∞ := by
    simp_rw [enorm_mul, RCLike.enorm_conj]
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (M * Rθ P ^ 6) * ∫⁻ p, ‖ft P p‖ₑ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_ft_ne_top P)) ?_
    rw [← lintegral_const_mul _ (measurable_ft P).enorm]
    exact lintegral_mono fun p => enorm_Psi_ft_le P hM0 hM p
  rw [← integral_unfold2 (fun p => Psi p.1 p.2 * conj (ft P p))
    ((measurable_Psi).mul (Complex.continuous_conj.measurable.comp (measurable_ft P))) hfin]
  congr 1; funext p
  congr 1
  simp only [dsmul]
  simp_rw [Psi_smul]
  rw [tsum_mul_left, ← Complex.conj_tsum]
  rfl

/-- `∫⁻_{U×ℍ} 1[Dh ≤ R] ≤ 8R⁴`. -/
lemma lintegral_U_ball (R : ℝ) (hR : 1 ≤ R) :
    ∫⁻ p : ℍ × ℍ, indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p ≤
      ENNReal.ofReal (8 * R ^ 4) := by
  have hmD : Measurable fun q : ℍ × ℍ => Dh q.1 q.2 := by
    unfold Dh
    refine Measurable.div ?_ ((measurable_im_H.comp measurable_fst).mul
      (measurable_im_H.comp measurable_snd))
    exact Complex.continuous_normSq.measurable.comp
      ((UpperHalfPlane.measurable_coe.comp measurable_fst).sub
        (Complex.continuous_conj.measurable.comp (UpperHalfPlane.measurable_coe.comp measurable_snd)))
  have hmS : MeasurableSet {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} := measurableSet_le hmD measurable_const
  rw [Measure.volume_eq_prod, lintegral_prod _ ((measurable_indU.mul
    (measurable_one.indicator hmS)).aemeasurable)]
  calc ∫⁻ z, ∫⁻ w, indU (z, w) * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 (z, w)
      ≤ ∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z * ENNReal.ofReal (4 * R ^ 4) := by
        refine lintegral_mono fun z => ?_
        simp only [indU]
        have hmw : Measurable fun w : ℍ => {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator
            (1 : ℍ × ℍ → ℝ≥0∞) (z, w) :=
          (measurable_one.indicator hmS).comp measurable_prodMk_left
        rw [lintegral_const_mul _ hmw]
        gcongr
        refine le_trans (le_of_eq ?_) (lintegral_ball_le z hR)
        congr 1
    _ = (∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z) * ENNReal.ofReal (4 * R ^ 4) :=
        lintegral_mul_const _ (measurable_one.indicator measurableSet_Uset)
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (4 * R ^ 4) := by gcongr; exact lintegral_U_le
    _ = ENNReal.ofReal (8 * R ^ 4) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf

end RamanujanTau.SCSProof
