/-
# The pairing `Q = ∫ Ψ conj ft` as an integral of horocycle coefficients

`Q_eq`: `∫ Ψ conj ft = ∫_ζ 1_B(ζ) ∫_y 1_I(y) y⁻² cf(y,ζ)`,
`cf(y,ζ) = (y(i − ζ̄))¹² e^{−2πhy} G_h(2πy(1 + iζ̄))` (`coeff_Psi`).
-/
import RamanujanTau.SCSProof.Coord

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- The skew map `(z, ζ) ↦ (z, Re z + Im z · ζ)`. -/
noncomputable def skew (p : ℍ × ℍ) : ℍ × ℍ := (p.1, affGL p.1.re p.1.im p.1.im_pos • p.2)

lemma measurable_aff_uncurry :
    Measurable (uncurry fun (z ζ : ℍ) => affGL z.re z.im z.im_pos • ζ) := by
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have : (UpperHalfPlane.coe ∘ uncurry fun (z ζ : ℍ) => affGL z.re z.im z.im_pos • ζ) =
      fun p : ℍ × ℍ => (p.1.re : ℂ) + p.1.im * (p.2 : ℂ) := by
    funext p
    show ((affGL p.1.re p.1.im p.1.im_pos • p.2 : ℍ) : ℂ) = _
    rw [coe_affGL_smul]
  rw [this]
  exact ((Complex.measurable_ofReal.comp (measurable_re_H.comp measurable_fst)).add
    ((Complex.measurable_ofReal.comp (measurable_im_H.comp measurable_fst)).mul
      (UpperHalfPlane.measurable_coe.comp measurable_snd)))

lemma measurePreserving_skew : MeasurePreserving skew (volume : Measure (ℍ × ℍ)) volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℍ)).skew_product measurable_aff_uncurry
    (Filter.Eventually.of_forall fun z => (measurePreserving_affGL z.re z.im z.im_pos).map_eq)

/-- The closed-form horocycle coefficient. -/
noncomputable def cf (y : ℝ) (ζ : ℍ) : ℂ :=
  ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12 * (Real.exp (-2 * π * P.h * y) : ℂ) *
    Gh P.h (2 * π * y * (1 + I * conj (ζ : ℂ)))

lemma ft_skew (p : ℍ × ℍ) : ft P (skew p) =
    strip.indicator 1 p.1 * ({u : ℍ | inI P u.im}.indicator 1 p.1 *
      ({ζ : ℂ | inB P ζ}.indicator 1 (p.2 : ℂ) * cexp (2 * π * I * P.h * p.1.re))) := by
  unfold ft ff skew suppF
  simp only [mem_setOf_eq, rel_affGL]
  by_cases h1 : p.1 ∈ strip
  · by_cases h2 : inI P p.1.im
    · by_cases h3 : inB P (p.2 : ℂ)
      · rw [if_pos h1, if_pos ⟨h2, by rw [rel_affGL]; exact h3⟩, indicator_of_mem h1, indicator_of_mem (show p.1 ∈
          {u : ℍ | inI P u.im} from h2), indicator_of_mem (show (p.2 : ℂ) ∈ {ζ : ℂ | inB P ζ}
          from h3)]
        simp
      · rw [if_pos h1, if_neg (fun h => h3 (by have := h.2; rwa [rel_affGL] at this)), indicator_of_notMem (show (p.2 : ℂ) ∉
          {ζ : ℂ | inB P ζ} from h3)]
        simp
    · rw [if_pos h1, if_neg (fun h => h2 h.1), indicator_of_notMem (show p.1 ∉
        {u : ℍ | inI P u.im} from h2)]
      simp
  · rw [if_neg h1, indicator_of_notMem h1]; simp

end RamanujanTau.SCSProof

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma aff_eq_affGL {y : ℝ} (hy : 0 < y) (x : ℝ) (ζ : ℍ) :
    affGL (toH (x, y)).re (toH (x, y)).im (toH (x, y)).im_pos • ζ = aff hy x ζ := by
  apply UpperHalfPlane.ext
  rw [coe_affGL_smul, aff_coe, toH_re (show 0 < (x, y).2 from hy),
    toH_im (show 0 < (x, y).2 from hy)]

/-- `D(ζ) = ((Re ζ)² + (1 + Im ζ)²)/Im ζ`. -/
noncomputable def Dz (ζ : ℍ) : ℝ := ((ζ : ℂ).re ^ 2 + (1 + (ζ : ℂ).im) ^ 2) / (ζ : ℂ).im

lemma norm_Psi_aff {M : ℝ} (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (z ζ : ℍ) :
    ‖Psi z (affGL z.re z.im z.im_pos • ζ)‖ ≤ M * Dz ζ ^ 6 := by
  have := norm_Psi_le_Dh hM z (affGL z.re z.im z.im_pos • ζ)
  rwa [Dh_eq_rel, rel_affGL] at this

lemma measurable_g : Measurable fun p : ℍ × ℍ => Psi p.1 p.2 * conj (ft P p) :=
  measurable_Psi.mul (Complex.continuous_conj.measurable.comp (measurable_ft P))

lemma integrable_g {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    Integrable fun p : ℍ × ℍ => Psi p.1 p.2 * conj (ft P p) := by
  refine ⟨(measurable_g P).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp_rw [enorm_mul, RCLike.enorm_conj]
  refine lt_of_le_of_lt (b := ENNReal.ofReal (M * Rθ P ^ 6) * ∫⁻ p, ‖ft P p‖ₑ) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ft_ne_top P).lt_top)
  rw [← lintegral_const_mul _ (measurable_ft P).enorm]
  exact lintegral_mono fun p => enorm_Psi_ft_le P hM0 hM p

end RamanujanTau.SCSProof
