/-
# Cauchy–Schwarz, part 2: unfolding `Ψ` and `‖Pt‖²`, and the bound for `∫ Ψ conj ft`

`norm_Q_le`: `‖∫ Ψ conj ft‖ ≤ ½ · √(8 M² R¹⁶) · √(2‖Σ_γ I(γ)‖)`.
-/
import RamanujanTau.SCSProof.CS

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma continuous_Delta : Continuous Δf :=
  (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous

lemma measurable_Psi : Measurable fun p : ℍ × ℍ => Psi p.1 p.2 := by
  unfold Psi
  refine Continuous.measurable ?_
  refine ((Continuous.pow ?_ 12).mul (continuous_Delta.comp continuous_fst)).mul
    (Complex.continuous_conj.comp (continuous_Delta.comp continuous_snd))
  exact (UpperHalfPlane.continuous_coe.comp continuous_fst).sub
    (Complex.continuous_conj.comp (UpperHalfPlane.continuous_coe.comp continuous_snd))

lemma norm_Psi_le_Dh {M : ℝ} (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (z w : ℍ) :
    ‖Psi z w‖ ≤ M * Dh z w ^ 6 := hM z w

lemma Pt_smul (γ : SL(2, ℤ)) (p : ℍ × ℍ) : Pt P (dsmul γ p) = Pt P p := by
  unfold Pt
  simp_rw [← dsmul_mul]
  exact (Equiv.mulRight γ).tsum_eq (fun δ => ft P (dsmul δ p))

lemma Dh_le_of_Pt (p : ℍ × ℍ) (hp : Pt P p ≠ 0) : Dh p.1 p.2 ≤ Rθ P := by
  by_contra hD
  apply hp
  unfold Pt
  have : ∀ γ : SL(2, ℤ), ft P (dsmul γ p) = 0 := by
    intro γ
    by_contra hne
    obtain ⟨-, hs⟩ := ft_ne_zero P hne
    have := Dh_le_of_suppF P hs
    simp only [dsmul] at this
    rw [Dh_smul] at this
    exact hD this
  simp [this]

lemma Dh_le_of_ft (p : ℍ × ℍ) (hp : ft P p ≠ 0) : Dh p.1 p.2 ≤ Rθ P :=
  Dh_le_of_suppF P (ft_ne_zero P hp).2

lemma enorm_Pt_le (p : ℍ × ℍ) : ‖Pt P p‖ₑ ≤ ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ :=
  enorm_tsum_le_tsum_enorm

/-- `∫⁻ ‖ft‖ ‖Pt‖ < ∞`. -/
lemma lintegral_ft_Pt_ne_top : ∫⁻ p, ‖ft P p‖ₑ * ‖Pt P p‖ₑ ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := (N0 P : ℝ≥0∞) * ∫⁻ p, ‖ft P p‖ₑ)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (lintegral_ft_ne_top P)) ?_
  rw [← lintegral_const_mul _ (measurable_ft P).enorm]
  refine lintegral_mono fun p => ?_
  calc ‖ft P p‖ₑ * ‖Pt P p‖ₑ ≤ ‖ft P p‖ₑ * ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ := by
        gcongr; exact enorm_Pt_le P p
    _ ≤ N0 P * ‖ft P p‖ₑ := tsum_enorm_ft_le P p

lemma measurable_Pt : Measurable (Pt P) := by
  unfold Pt
  exact Measurable.tsum fun γ => measurable_ft_dsmul P γ

/-- `∫ ft conj Pt = Σ_γ I(γ)`. -/
lemma integral_ft_Pt : ∫ p, ft P p * conj (Pt P p) = ∑' γ, Iγ P γ := by
  unfold Pt Iγ
  have hmeas : ∀ γ : SL(2, ℤ), AEStronglyMeasurable (fun p => ft P p * conj (ft P (dsmul γ p)))
      volume := fun γ => ((measurable_ft P).mul (Complex.continuous_conj.measurable.comp
        (measurable_ft_dsmul P γ))).aestronglyMeasurable
  have hfin : ∑' γ : SL(2, ℤ), ∫⁻ p, ‖ft P p * conj (ft P (dsmul γ p))‖ₑ ≠ ∞ := by
    simp_rw [enorm_mul, RCLike.enorm_conj]
    exact tsum_Ip_ne_top P
  rw [← integral_tsum hmeas hfin]
  congr 1; funext p
  rw [Complex.conj_tsum, tsum_mul_left]

/-- **Unfolding `‖Pt‖²`.** -/
theorem integral_Pt_sq :
    ∫ p, indUC p * ∑' γ : SL(2, ℤ), (ft P (dsmul γ p) * conj (Pt P (dsmul γ p))) =
      2 * ∑' γ, Iγ P γ := by
  rw [integral_unfold2 (fun p => ft P p * conj (Pt P p))
    ((measurable_ft P).mul (Complex.continuous_conj.measurable.comp (measurable_Pt P)))
    (by simp_rw [enorm_mul, RCLike.enorm_conj]; exact lintegral_ft_Pt_ne_top P),
    integral_ft_Pt]

lemma tsum_ft_Pt (p : ℍ × ℍ) :
    ∑' γ : SL(2, ℤ), (ft P (dsmul γ p) * conj (Pt P (dsmul γ p))) =
      ((‖Pt P p‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [Pt_smul]
  rw [tsum_mul_right]
  change Pt P p * conj (Pt P p) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `(∫⁻_{U×ℍ} ‖Pt‖²).toReal ≤ 2 ‖Σ_γ I(γ)‖`. -/
theorem lintegral_Pt_sq_le :
    (∫⁻ p, indU p * ‖Pt P p‖ₑ ^ 2).toReal ≤ 2 * ‖∑' γ, Iγ P γ‖ := by
  have h := integral_Pt_sq P
  simp_rw [tsum_ft_Pt] at h
  have hpt : ∀ p : ℍ × ℍ, indUC p * ((‖Pt P p‖ ^ 2 : ℝ) : ℂ) =
      (((indU p * ‖Pt P p‖ₑ ^ 2).toReal : ℝ) : ℂ) := by
    intro p
    unfold indUC indU
    by_cases hU : p.1 ∈ Uset
    · rw [indicator_of_mem hU, indicator_of_mem hU]
      simp only [Pi.one_apply, one_mul]
      rw [ENNReal.toReal_pow, ← ofReal_norm_eq_enorm, ENNReal.toReal_ofReal (norm_nonneg _)]
    · rw [indicator_of_notMem hU, indicator_of_notMem hU]; simp
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  have hmeas : AEMeasurable (fun p => indU p * ‖Pt P p‖ₑ ^ 2) volume :=
    (measurable_indU.mul ((measurable_Pt P).enorm.pow_const 2)).aemeasurable
  have hfin : ∀ᵐ p ∂(volume : Measure (ℍ × ℍ)), indU p * ‖Pt P p‖ₑ ^ 2 < ∞ := by
    refine Filter.Eventually.of_forall fun p => ?_
    unfold indU
    by_cases hU : p.1 ∈ Uset
    · rw [indicator_of_mem hU]; simp
    · rw [indicator_of_notMem hU]; simp
  rw [integral_toReal hmeas hfin] at h
  have := congrArg norm h
  rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, norm_mul] at this
  rw [this]; simp

end RamanujanTau.SCSProof
