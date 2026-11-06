/-
# The pairing `Q` as an integral of horocycle coefficients (part 2)
-/
import RamanujanTau.SCSProof.Qform

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- The `z`-integrand for fixed relative position `ζ`. -/
noncomputable def Az (ζ : ℍ) (z : ℍ) : ℂ :=
  (strip ∩ {u : ℍ | inI P u.im}).indicator (1 : ℍ → ℂ) z *
    (cexp (-2 * π * I * P.h * z.re) * Psi z (affGL z.re z.im z.im_pos • ζ))

/-- Its coordinate version. -/
noncomputable def Hf (ζ : ℍ) (p : ℝ × ℝ) : ℂ :=
  (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator (fun p : ℝ × ℝ =>
    ((1 / p.2 ^ 2 : ℝ) : ℂ) * (cexp (-2 * π * I * P.h * p.1) *
      Psi (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ))) p

lemma measurable_aff_of {α : Type*} [MeasurableSpace α] {f : α → ℍ} (hf : Measurable f)
    (ζ : ℍ) : Measurable fun p => affGL (f p).re (f p).im (f p).im_pos • ζ := by
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have : (UpperHalfPlane.coe ∘ fun p => affGL (f p).re (f p).im (f p).im_pos • ζ) =
      fun p => ((f p).re : ℂ) + (f p).im * (ζ : ℂ) := by
    funext p
    show ((affGL (f p).re (f p).im (f p).im_pos • ζ : ℍ) : ℂ) = _
    rw [coe_affGL_smul]
  rw [this]
  exact (Complex.measurable_ofReal.comp (measurable_re_H.comp hf)).add
    ((Complex.measurable_ofReal.comp (measurable_im_H.comp hf)).mul measurable_const)

lemma measurable_toH_aff (ζ : ℍ) :
    Measurable fun p : ℝ × ℝ => affGL (toH p).re (toH p).im (toH p).im_pos • ζ :=
  measurable_aff_of measurable_toH ζ

lemma measurable_Psi_comp {α : Type*} [MeasurableSpace α] {u v : α → ℍ} (hu : Measurable u)
    (hv : Measurable v) : Measurable fun a => Psi (u a) (v a) :=
  Measurable.comp (f := fun a => (u a, v a)) measurable_Psi (hu.prodMk hv)

lemma integrable_Hf {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖Psi z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (ζ : ℍ) :
    Integrable (Hf P ζ) := by
  have hY := P.hY
  have hbox : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hmeas : Measurable fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) *
      (cexp (-2 * π * I * P.h * p.1) *
        Psi (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ)) := by
    refine (Complex.measurable_ofReal.comp (measurable_const.div
      (measurable_snd.pow_const 2))).mul ((Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_fst))).mul ?_)
    exact measurable_Psi_comp (u := toH)
      (v := fun p : ℝ × ℝ => affGL (toH p).re (toH p).im (toH p).im_pos • ζ)
      measurable_toH (measurable_toH_aff ζ)
  refine Integrable.mono' (g := (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator
    (fun _ => 1 / P.Y ^ 2 * (M * Dz ζ ^ 6))) ?_ ((hmeas.indicator hbox).aestronglyMeasurable) ?_
  · refine (integrable_indicator_iff hbox).2 (integrableOn_const ?_)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun p => ?_
    unfold Hf
    by_cases hp : p ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))
    · rw [indicator_of_mem hp, indicator_of_mem hp, norm_mul, norm_mul]
      have hy : P.Y ≤ p.2 := hp.2.1
      have hy0 : 0 < p.2 := hY.trans_le hy
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Complex.ofReal_natCast,
        show (-2 * ↑π * I * ((P.h : ℝ) : ℂ) * (p.1 : ℂ)) = ((-2 * π * P.h * p.1 : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
      gcongr
      · exact norm_Psi_aff hM _ _
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero]

lemma integral_Az_eq_Hf (ζ : ℍ) : ∫ z, Az P ζ z = ∫ p, Hf P ζ p := by
  have hzero : ∀ p : ℝ × ℝ, p ∉ {p : ℝ × ℝ | 0 < p.2} → Hf P ζ p = 0 := by
    intro p hp
    simp only [mem_setOf_eq, not_lt] at hp
    unfold Hf
    refine indicator_of_notMem (fun hb => ?_) _
    have := hb.2.1
    have := P.hY
    linarith
  rw [integral_H, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_snd) fun p hp => ?_
  simp only [Az, Hf]
  have hp' : 0 < p.2 := hp
  by_cases hb : p ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))
  · have hm : toH p ∈ strip ∩ {u : ℍ | inI P u.im} := by
      refine ⟨?_, ?_⟩
      · show 0 ≤ (toH p).re ∧ (toH p).re < 1
        rw [toH_re hp']; exact hb.1
      · show inI P (toH p).im
        rw [toH_im hp']; exact hb.2
    rw [indicator_of_mem hm, indicator_of_mem hb, toH_re hp']
    simp
  · have hm : toH p ∉ strip ∩ {u : ℍ | inI P u.im} := by
      rintro ⟨h1, h2⟩
      apply hb
      refine ⟨?_, ?_⟩
      · have h1' : 0 ≤ (toH p).re ∧ (toH p).re < 1 := h1
        rw [toH_re hp'] at h1'; exact h1'
      · have h2' : inI P (toH p).im := h2
        rw [toH_im hp'] at h2'; exact h2'
    rw [indicator_of_notMem hm, indicator_of_notMem hb]; simp

end RamanujanTau.SCSProof
