/-
# The invariant measure on `ℍ` in coordinates, for complex integrands

`integral_H`: `∫_ℍ φ = ∫_{y>0} φ(x+iy) dx dy / y²`.
-/
import RamanujanTau.SCSProof.CS4

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError
open scoped ENNReal NNReal

lemma measurable_density :
    Measurable fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
  refine Measurable.pow_const (Measurable.div measurable_const ?_) 2
  exact Measurable.subtype_mk measurable_im_H

theorem integral_H (φ : ℍ → ℂ) :
    ∫ w, φ w = ∫ p in {p : ℝ × ℝ | 0 < p.2}, ((1 / p.2 ^ 2 : ℝ) : ℂ) * φ (toH p) := by
  rw [UpperHalfPlane.volume_def, integral_withDensity_eq_integral_smul measurable_density]
  set F : ℂ → ℂ := fun z => ((1 / z.im ^ 2 : ℝ) : ℂ) * φ (toH (z.re, z.im)) with hF
  have e1 : (fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) • φ z) =
      F ∘ UpperHalfPlane.coe := by
    funext z
    simp only [Function.comp_apply, hF, NNReal.smul_def, Complex.real_smul]
    rw [show ((z : ℂ).re, (z : ℂ).im) = (z.re, z.im) from rfl, toH_re_im]
    congr 1
    have : (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) = 1 / (z : ℂ).im ^ 2 := by
      push_cast; rw [div_pow, one_pow]; rfl
    rw [this]
  rw [e1]
  change ∫ z, F (UpperHalfPlane.coe z) ∂(volume.comap UpperHalfPlane.coe) = _
  rw [← measurableEmbedding_coe.integral_map, measurableEmbedding_coe.map_comap]
  have hrange : Set.range UpperHalfPlane.coe = {z : ℂ | 0 < z.im} := by
    ext z; constructor
    · rintro ⟨w, rfl⟩; exact w.im_pos
    · intro hz; exact ⟨⟨z, hz⟩, rfl⟩
  rw [hrange]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.setIntegral_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding
    F {z : ℂ | 0 < z.im}]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im} =
      {p : ℝ × ℝ | 0 < p.2} := by
    ext p; simp
  rw [hpre]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_snd) fun p _ => ?_
  simp only [hF, mE_symm]
  simp

end RamanujanTau.SCSProof
