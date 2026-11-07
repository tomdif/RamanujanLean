/-
# The main-term comparison `|c₀| W ≤ |Q| + E W`
-/
import RamanujanTau.SCSProof.Gbounds2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- `m_I = ∫_I y⁻² dy`. -/
noncomputable def mI : ℝ := ∫ y in Icc P.Y (P.Y * (1 + P.ε)), 1 / y ^ 2

/-- `m_B = μ(B)`. -/
noncomputable def mB : ℝ := (∫⁻ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator 1 (ζ : ℂ)).toReal

lemma integrableOn_inv_sq : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Icc P.Y (P.Y * (1 + P.ε))) := by
  refine ContinuousOn.integrableOn_Icc ?_
  refine ContinuousOn.div continuousOn_const (continuous_pow 2).continuousOn fun y hy => ?_
  have := P.hY.trans_le hy.1; positivity

lemma integrable_inB_C : Integrable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) := by
  have hm : MeasurableSet {ζ : ℍ | inB P (ζ : ℂ)} :=
    (measurableSet_inB P).preimage UpperHalfPlane.measurable_coe
  have e : (fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ)) =
      {ζ : ℍ | inB P (ζ : ℂ)}.indicator (fun _ => (1 : ℂ)) := by
    funext ζ; unfold indicator; split_ifs <;> simp_all
  rw [e]
  refine (integrable_indicator_iff hm).2 (integrableOn_const ?_)
  have := lintegral_B_le P
  rw [← lintegral_indicator_one hm]
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (le_of_eq ?_) this)
  congr 1

lemma integral_inB_C : ∫ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) = (mB P : ℂ) := by
  unfold mB
  have e : (fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ)) =
      fun ζ : ℍ => (({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℝ≥0∞) (ζ : ℂ)).toReal : ℂ) := by
    funext ζ; unfold indicator; split_ifs <;> simp
  rw [e, integral_complex_ofReal, integral_toReal]
  · exact ((measurable_one.indicator (measurableSet_inB P)).comp
      UpperHalfPlane.measurable_coe).aemeasurable
  · exact Filter.Eventually.of_forall fun ζ => by unfold indicator; split_ifs <;> simp

/-- The integrated `ζ`-function is integrable. -/
lemma integrable_Fζ {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    Integrable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, Ky P ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_g P hM0 hM
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      Az P p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact g_skew P p
  rw [Measure.volume_eq_prod] at hint
  have := hint.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_Az P ζ hM0 hM]

lemma integrable_Ky {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (ζ : ℍ) :
    Integrable (Ky P ζ) := by
  have h := integrable_Hf P hM0 hM ζ
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_right.congr (Filter.Eventually.of_forall fun y => integral_Hf_x P ζ y)

/-- **Main-term comparison.** -/
theorem main_term_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6)
    (c0 : ℂ) (E : ℝ) (hE : ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cf P y ζ - c0‖ ≤ E) :
    ‖c0‖ * (mI P * mB P) ≤ ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ + E * (mI P * mB P) := by
  have hY := P.hY
  have hE0 : 0 ≤ E ∨ ¬ ∃ ζ : ℍ, inB P (ζ : ℂ) := by
    by_cases hex : ∃ ζ : ℍ, inB P (ζ : ℂ)
    · obtain ⟨ζ, hζ⟩ := hex
      exact Or.inl ((norm_nonneg _).trans (hE P.Y ⟨le_rfl, by nlinarith [P.hε]⟩ ζ hζ))
    · exact Or.inr hex
  rw [Q_eq P hM0 hM]
  set F := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, Ky P ζ y
  set F0 := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * (c0 * (mI P : ℂ))
  have hF := integrable_Fζ P hM0 hM
  have hF0 : Integrable F0 := (integrable_inB_C P).mul_const _
  have hc0W : ∫ ζ, F0 ζ = c0 * ((mI P * mB P : ℝ) : ℂ) := by
    simp only [F0]
    rw [integral_mul_const, integral_inB_C]; push_cast; ring
  -- inner bound
  have hinner : ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖(∫ y, Ky P ζ y) - c0 * (mI P : ℂ)‖ ≤ E * mI P := by
    intro ζ hζ
    have hKi := integrable_Ky P hM0 hM ζ
    have hc : Integrable fun y : ℝ => (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y := by
      refine (integrable_indicator_iff measurableSet_Icc).2 ?_
      exact ((integrableOn_inv_sq P).ofReal).mul_const _
    have hcint : ∫ y, (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y = c0 * (mI P : ℂ) := by
      rw [integral_indicator measurableSet_Icc, integral_mul_const, integral_complex_ofReal]
      unfold mI; ring
    rw [← hcint, ← integral_sub hKi hc]
    have hbd : ∀ y, ‖Ky P ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y‖ ≤
        (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => 1 / y ^ 2 * E) y := by
      intro y
      unfold Ky
      by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
      · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy, ← mul_sub, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (by have := hY.trans_le hy.1; positivity)]
        gcongr
        exact hE y hy ζ hζ
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy]; simp
    calc ‖∫ y, (Ky P ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
          (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y)‖
        ≤ ∫ y, (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => 1 / y ^ 2 * E) y :=
          norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_Icc).2
            ((integrableOn_inv_sq P).mul_const _)) (Filter.Eventually.of_forall hbd)
      _ = E * mI P := by
          rw [integral_indicator measurableSet_Icc, integral_mul_const]; unfold mI; ring
  -- outer bound
  have hdiff : ‖(∫ ζ, F ζ) - c0 * ((mI P * mB P : ℝ) : ℂ)‖ ≤ E * (mI P * mB P) := by
    rw [← hc0W]
    have hs : ∫ ζ, (F ζ - F0 ζ) = (∫ ζ, F ζ) - ∫ ζ, F0 ζ := integral_sub hF hF0
    refine (le_of_eq (congrArg norm hs.symm)).trans ?_
    have hbd : ∀ ζ : ℍ, ‖F ζ - F0 ζ‖ ≤ {ζ : ℍ | inB P (ζ : ℂ)}.indicator (fun _ => E * mI P) ζ := by
      intro ζ
      simp only [F, F0]
      by_cases hζ : inB P (ζ : ℂ)
      · rw [indicator_of_mem (show (ζ : ℂ) ∈ {ζ : ℂ | inB P ζ} from hζ),
          indicator_of_mem (show ζ ∈ {ζ : ℍ | inB P (ζ : ℂ)} from hζ), Pi.one_apply, one_mul,
          one_mul]
        exact hinner ζ hζ
      · rw [indicator_of_notMem (show (ζ : ℂ) ∉ {ζ : ℂ | inB P ζ} from hζ),
          indicator_of_notMem (show ζ ∉ {ζ : ℍ | inB P (ζ : ℂ)} from hζ)]; simp
    have hm : MeasurableSet {ζ : ℍ | inB P (ζ : ℂ)} :=
      (measurableSet_inB P).preimage UpperHalfPlane.measurable_coe
    have hint : Integrable ({ζ : ℍ | inB P (ζ : ℂ)}.indicator (fun _ => E * mI P)) := by
      refine (integrable_indicator_iff hm).2 (integrableOn_const ?_)
      rw [← lintegral_indicator_one hm]
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (le_of_eq ?_) (lintegral_B_le P))
      congr 1
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbd)).trans (le_of_eq ?_)
    rw [integral_indicator hm, setIntegral_const]
    have : (volume.real {ζ : ℍ | inB P (ζ : ℂ)}) = mB P := by
      unfold mB Measure.real
      rw [← lintegral_indicator_one hm]
      congr 1
    rw [this, smul_eq_mul]; ring
  have := norm_sub_norm_le (c0 * ((mI P * mB P : ℝ) : ℂ)) (∫ ζ, F ζ)
  rw [norm_sub_rev] at hdiff
  have hW0 : 0 ≤ mI P * mB P := by
    unfold mI mB
    exact mul_nonneg (setIntegral_nonneg measurableSet_Icc fun y hy => by
      have := hY.trans_le hy.1; positivity) ENNReal.toReal_nonneg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0] at this
  linarith

end RamanujanTau.SCSProof
