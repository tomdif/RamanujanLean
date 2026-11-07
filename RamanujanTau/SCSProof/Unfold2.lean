/-
# Unfolding on `ℍ × ℍ` for the diagonal `SL₂(ℤ)` action

`U × ℍ` is a fundamental domain (up to `±1` and a null set) for the diagonal action, so
`∫_{U×ℍ} Σ_γ g(γz, γw) = 2 ∫_{ℍ×ℍ} g` (`lintegral_unfold2`, `integral_unfold2`).
-/
import RamanujanTau.SCSProof.TwoPoint
import RamanujanTau.RankinError.HMeasure

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal.Horo
open scoped MatrixGroups ENNReal

/-- Diagonal action. -/
noncomputable def dsmul (γ : SL(2, ℤ)) (p : ℍ × ℍ) : ℍ × ℍ := (γ • p.1, γ • p.2)

lemma measurePreserving_dsmul (γ : SL(2, ℤ)) :
    MeasurePreserving (dsmul γ) (volume : Measure (ℍ × ℍ)) volume :=
  (measurePreserving_sl γ).prod (measurePreserving_sl γ)

lemma measurable_dsmul (γ : SL(2, ℤ)) : Measurable (dsmul γ) :=
  (measurePreserving_dsmul γ).measurable

lemma dsmul_mul (γ δ : SL(2, ℤ)) (p : ℍ × ℍ) : dsmul (γ * δ) p = dsmul γ (dsmul δ p) := by
  simp [dsmul, mul_smul]

lemma dsmul_one (p : ℍ × ℍ) : dsmul 1 p = p := by simp [dsmul]

/-- The diagonal action as a measurable equivalence. -/
noncomputable def dsmulEquiv (γ : SL(2, ℤ)) : ℍ × ℍ ≃ᵐ ℍ × ℍ where
  toFun := dsmul γ
  invFun := dsmul γ⁻¹
  left_inv p := by rw [← dsmul_mul, inv_mul_cancel, dsmul_one]
  right_inv p := by rw [← dsmul_mul, mul_inv_cancel, dsmul_one]
  measurable_toFun := measurable_dsmul γ
  measurable_invFun := measurable_dsmul γ⁻¹

/-- The indicator of the fundamental domain in the first variable. -/
noncomputable def indU (p : ℍ × ℍ) : ℝ≥0∞ := Uset.indicator (1 : ℍ → ℝ≥0∞) p.1

lemma measurable_indU : Measurable indU :=
  (measurable_one.indicator measurableSet_Uset).comp measurable_fst

/-- **Unfolding** (non-negative form). -/
theorem lintegral_unfold2 (Ξ : ℍ × ℍ → ℝ≥0∞) (hΞ : Measurable Ξ) :
    ∫⁻ p, indU p * ∑' γ : SL(2, ℤ), Ξ (dsmul γ p) = 2 * ∫⁻ p, Ξ p := by
  have hm : ∀ γ : SL(2, ℤ), Measurable fun p => indU p * Ξ (dsmul γ p) :=
    fun γ => measurable_indU.mul (hΞ.comp (measurable_dsmul γ))
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun γ => (hm γ).aemeasurable]
  have step : ∀ γ : SL(2, ℤ), ∫⁻ p, indU p * Ξ (dsmul γ p) =
      ∫⁻ q, indU (dsmul γ⁻¹ q) * Ξ q := by
    intro γ
    rw [← (measurePreserving_dsmul γ⁻¹).lintegral_comp (hm γ)]
    congr 1; funext q
    rw [← dsmul_mul, mul_inv_cancel, dsmul_one]
  simp_rw [step]
  have hm2 : ∀ γ : SL(2, ℤ), Measurable fun q => indU (dsmul γ⁻¹ q) * Ξ q :=
    fun γ => (measurable_indU.comp (measurable_dsmul γ⁻¹)).mul hΞ
  rw [← lintegral_tsum fun γ => (hm2 γ).aemeasurable]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← lintegral_const_mul _ hΞ]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ q : ℍ × ℍ, ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1) = 2 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℍ))
      (ν := (volume : Measure ℍ))).ae ae_tsum_ind_U
  filter_upwards [hae] with q hq
  have hq2 : ∑' γ : SL(2, ℤ), indU (dsmul γ⁻¹ q) = 2 := by
    show ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • q.1) = 2
    exact ((Equiv.inv (SL(2, ℤ))).tsum_eq
      (fun γ => Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1))).trans hq
  rw [hq2]

/-- The complex indicator of `U` in the first variable. -/
noncomputable def indUC (p : ℍ × ℍ) : ℂ := Uset.indicator (1 : ℍ → ℂ) p.1

lemma measurable_indUC : Measurable indUC :=
  (measurable_one.indicator measurableSet_Uset).comp measurable_fst

lemma enorm_indUC_mul (p : ℍ × ℍ) (z : ℂ) : ‖indUC p * z‖ₑ = indU p * ‖z‖ₑ := by
  unfold indUC indU
  by_cases h : p.1 ∈ Uset
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- **Unfolding** (integrable complex form). -/
theorem integral_unfold2 (g : ℍ × ℍ → ℂ) (hg : Measurable g) (hgi : ∫⁻ p, ‖g p‖ₑ ≠ ∞) :
    ∫ p, indUC p * ∑' γ : SL(2, ℤ), g (dsmul γ p) = 2 * ∫ p, g p := by
  have hmγ : ∀ γ : SL(2, ℤ), Measurable fun p => indUC p * g (dsmul γ p) :=
    fun γ => measurable_indUC.mul (hg.comp (measurable_dsmul γ))
  have hfin : ∑' γ : SL(2, ℤ), ∫⁻ p, ‖indUC p * g (dsmul γ p)‖ₑ ≠ ∞ := by
    simp_rw [enorm_indUC_mul]
    rw [← lintegral_tsum (f := fun γ p => indU p * ‖g (dsmul γ p)‖ₑ) fun γ =>
      Measurable.aemeasurable (by exact measurable_indU.mul ((hg.comp (measurable_dsmul γ)).enorm))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [lintegral_unfold2 _ hg.enorm]
    exact ENNReal.mul_ne_top (by simp) hgi
  simp_rw [← tsum_mul_left]
  rw [integral_tsum (fun γ => (hmγ γ).aestronglyMeasurable) hfin]
  have step : ∀ γ : SL(2, ℤ), ∫ p, indUC p * g (dsmul γ p) =
      ∫ q, indUC (dsmul γ⁻¹ q) * g q := by
    intro γ
    rw [← (measurePreserving_dsmul γ⁻¹).integral_comp (dsmulEquiv γ⁻¹).measurableEmbedding]
    congr 1; funext q
    rw [← dsmul_mul, mul_inv_cancel, dsmul_one]
  simp_rw [step]
  have hfin2 : ∑' γ : SL(2, ℤ), ∫⁻ q, ‖indUC (dsmul γ⁻¹ q) * g q‖ₑ ≠ ∞ := by
    simp_rw [enorm_indUC_mul]
    rw [← lintegral_tsum (f := fun γ q => indU (dsmul γ⁻¹ q) * ‖g q‖ₑ) fun γ =>
      Measurable.aemeasurable (by exact (measurable_indU.comp (measurable_dsmul γ⁻¹)).mul hg.enorm)]
    have : ∫⁻ q, ∑' γ : SL(2, ℤ), indU (dsmul γ⁻¹ q) * ‖g q‖ₑ = 2 * ∫⁻ q, ‖g q‖ₑ := by
      rw [← lintegral_const_mul _ hg.enorm]
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ q : ℍ × ℍ, ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1) = 2 :=
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℍ))
          (ν := (volume : Measure ℍ))).ae ae_tsum_ind_U
      filter_upwards [hae] with q hq
      have hq2 : ∑' γ : SL(2, ℤ), indU (dsmul γ⁻¹ q) = 2 := by
        show ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • q.1) = 2
        exact ((Equiv.inv (SL(2, ℤ))).tsum_eq
          (fun γ => Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1))).trans hq
      rw [ENNReal.tsum_mul_right, hq2]
    rw [this]
    exact ENNReal.mul_ne_top (by simp) hgi
  rw [← integral_tsum (f := fun γ q => indUC (dsmul γ⁻¹ q) * g q) (fun γ =>
    Measurable.aestronglyMeasurable
      ((measurable_indUC.comp (measurable_dsmul γ⁻¹)).mul hg)) hfin2]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ q : ℍ × ℍ, ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1) = 2 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℍ))
      (ν := (volume : Measure ℍ))).ae ae_tsum_ind_U
  filter_upwards [hae] with q hq
  rw [tsum_mul_right]
  congr 1
  have hq' : ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • q.1) = 2 := by
    exact ((Equiv.inv (SL(2, ℤ))).tsum_eq
      (fun γ => Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • q.1))).trans hq
  have hre : ∀ γ : SL(2, ℤ), indUC (dsmul γ⁻¹ q) =
      (((Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • q.1)).toReal : ℝ) : ℂ) := by
    intro γ
    show Uset.indicator (1 : ℍ → ℂ) (γ⁻¹ • q.1) = _
    by_cases h : γ⁻¹ • q.1 ∈ Uset
    · rw [indicator_of_mem h, indicator_of_mem h]; simp
    · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
  simp_rw [hre]
  rw [← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq (fun γ => by
    unfold indicator; split_ifs <;> simp), hq']
  simp

end RamanujanTau.SCSProof
