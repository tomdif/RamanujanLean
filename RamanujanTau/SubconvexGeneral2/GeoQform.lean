/-
# Weight-`k` pairing `Q_f = ∫ Ψ_f conj ft` as an integral of horocycle coefficients
(copy of `SCSProof.Qform/Qform2/Qform3`)

`QF_eq`: `∫ Ψ_f conj ft = ∫_ζ 1_B(ζ) ∫_y 1_I(y) y⁻² cfF(y,ζ)`,
`cfF(y,ζ) = (y(i − ζ̄))^k e^{−2πhy} G^f_h(2πy(1 + iζ̄))` (`coeff_PsiF`).
-/
import RamanujanTau.SubconvexGeneral2.GeoCS

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof RamanujanTau.SubconvexGeneral
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (P : Par)

/-- The closed-form horocycle coefficient, weight `k`. -/
noncomputable def cfF (y : ℝ) (ζ : ℍ) : ℂ :=
  ((y : ℂ) * (I - conj (ζ : ℂ))) ^ k * (Real.exp (-2 * π * P.h * y) : ℂ) *
    GhF f P.h (2 * π * y * (1 + I * conj (ζ : ℂ)))

lemma norm_PsiF_aff {m : ℕ} {M : ℝ} (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) (z ζ : ℍ) :
    ‖PsiF f z (affGL z.re z.im z.im_pos • ζ)‖ ≤ M * Dz ζ ^ m := by
  have := norm_PsiF_le_Dh f hM z (affGL z.re z.im z.im_pos • ζ)
  rwa [Dh_eq_rel, rel_affGL] at this

lemma measurable_gF : Measurable fun p : ℍ × ℍ => PsiF f p.1 p.2 * conj (ft P p) :=
  (measurable_PsiF f).mul (Complex.continuous_conj.measurable.comp (measurable_ft P))

lemma integrable_gF {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) :
    Integrable fun p : ℍ × ℍ => PsiF f p.1 p.2 * conj (ft P p) := by
  refine ⟨(measurable_gF f P).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp_rw [enorm_mul, RCLike.enorm_conj]
  refine lt_of_le_of_lt (b := ENNReal.ofReal (M * Rθ P ^ m) * ∫⁻ p, ‖ft P p‖ₑ) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ft_ne_top P).lt_top)
  rw [← lintegral_const_mul _ (measurable_ft P).enorm]
  exact lintegral_mono fun p => enorm_PsiF_ft_le f P hM0 hM p

/-- The `z`-integrand for fixed relative position `ζ`. -/
noncomputable def AzF (ζ : ℍ) (z : ℍ) : ℂ :=
  (strip ∩ {u : ℍ | inI P u.im}).indicator (1 : ℍ → ℂ) z *
    (cexp (-2 * π * I * P.h * z.re) * PsiF f z (affGL z.re z.im z.im_pos • ζ))

/-- Its coordinate version. -/
noncomputable def HfF (ζ : ℍ) (p : ℝ × ℝ) : ℂ :=
  (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator (fun p : ℝ × ℝ =>
    ((1 / p.2 ^ 2 : ℝ) : ℂ) * (cexp (-2 * π * I * P.h * p.1) *
      PsiF f (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ))) p

lemma measurable_PsiF_comp {α : Type*} [MeasurableSpace α] {u v : α → ℍ} (hu : Measurable u)
    (hv : Measurable v) : Measurable fun a => PsiF f (u a) (v a) :=
  Measurable.comp (f := fun a => (u a, v a)) (measurable_PsiF f) (hu.prodMk hv)

lemma integrable_HfF {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) (ζ : ℍ) :
    Integrable (HfF f P ζ) := by
  have hY := P.hY
  have hbox : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hmeas : Measurable fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) *
      (cexp (-2 * π * I * P.h * p.1) *
        PsiF f (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ)) := by
    refine (Complex.measurable_ofReal.comp (measurable_const.div
      (measurable_snd.pow_const 2))).mul ((Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_fst))).mul ?_)
    exact measurable_PsiF_comp f (u := toH)
      (v := fun p : ℝ × ℝ => affGL (toH p).re (toH p).im (toH p).im_pos • ζ)
      measurable_toH (measurable_toH_aff ζ)
  refine Integrable.mono' (g := (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator
    (fun _ => 1 / P.Y ^ 2 * (M * Dz ζ ^ m))) ?_ ((hmeas.indicator hbox).aestronglyMeasurable) ?_
  · refine (integrable_indicator_iff hbox).2 (integrableOn_const ?_)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun p => ?_
    unfold HfF
    by_cases hp : p ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))
    · rw [indicator_of_mem hp, indicator_of_mem hp, norm_mul, norm_mul]
      have hy : P.Y ≤ p.2 := hp.2.1
      have hy0 : 0 < p.2 := hY.trans_le hy
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Complex.ofReal_natCast,
        show (-2 * ↑π * I * ((P.h : ℝ) : ℂ) * (p.1 : ℂ)) = ((-2 * π * P.h * p.1 : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
      gcongr
      · exact norm_PsiF_aff f hM _ _
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero]

lemma integral_AzF_eq_HfF (ζ : ℍ) : ∫ z, AzF f P ζ z = ∫ p, HfF f P ζ p := by
  have hzero : ∀ p : ℝ × ℝ, p ∉ {p : ℝ × ℝ | 0 < p.2} → HfF f P ζ p = 0 := by
    intro p hp
    simp only [mem_setOf_eq, not_lt] at hp
    unfold HfF
    refine indicator_of_notMem (fun hb => ?_) _
    have := hb.2.1
    have := P.hY
    linarith
  rw [integral_H, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_snd) fun p hp => ?_
  simp only [AzF, HfF]
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

/-- The `y`-integrand. -/
noncomputable def KyF (ζ : ℍ) (y : ℝ) : ℂ :=
  (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * cfF f P y ζ) y

lemma integral_HfF_x (ζ : ℍ) (y : ℝ) : ∫ x, HfF f P ζ (x, y) = KyF f P ζ y := by
  unfold KyF
  by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
  · have hy0 : 0 < y := P.hY.trans_le hy.1
    rw [indicator_of_mem hy]
    have e : ∀ x : ℝ, HfF f P ζ (x, y) = (Ico (0 : ℝ) 1).indicator (fun x =>
        ((1 / y ^ 2 : ℝ) : ℂ) *
        (PsiF f (hp hy0 x) (aff hy0 x ζ) * cexp (-2 * π * I * P.h * x))) x := by
      intro x
      unfold HfF
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · rw [indicator_of_mem (show (x, y) ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε)) from
          ⟨hx, hy⟩), indicator_of_mem hx, aff_eq_affGL hy0, toH_hp hy0]
        ring
      · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]
    simp_rw [e]
    rw [integral_indicator measurableSet_Ico, integral_const_mul]
    unfold cfF
    rw [← coeff_PsiF f P.h hy0 ζ]
    congr 1
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  · rw [indicator_of_notMem hy]
    have : ∀ x : ℝ, HfF f P ζ (x, y) = 0 := fun x => by
      unfold HfF; exact indicator_of_notMem (fun h => hy h.2) _
    simp [this]

lemma integral_AzF (ζ : ℍ) {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) :
    ∫ z, AzF f P ζ z = ∫ y, KyF f P ζ y := by
  rw [integral_AzF_eq_HfF, Measure.volume_eq_prod,
    integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact integrable_HfF f P hM0 hM ζ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => integral_HfF_x f P ζ y)

lemma gF_skew (p : ℍ × ℍ) :
    (fun p : ℍ × ℍ => PsiF f p.1 p.2 * conj (ft P p)) (skew p) =
      ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) * AzF f P p.2 p.1 := by
  simp only
  rw [ft_skew]
  unfold AzF skew
  simp only [map_mul]
  have h1 : conj (strip.indicator (1 : ℍ → ℂ) p.1) = strip.indicator 1 p.1 := by
    unfold indicator; split_ifs <;> simp
  have h2 : conj ({u : ℍ | inI P u.im}.indicator (1 : ℍ → ℂ) p.1) =
      {u : ℍ | inI P u.im}.indicator 1 p.1 := by
    unfold indicator; split_ifs <;> simp
  have h3 : conj ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) =
      {ζ : ℂ | inB P ζ}.indicator 1 (p.2 : ℂ) := by
    unfold indicator; split_ifs <;> simp
  have h4 : conj (cexp (2 * π * I * P.h * p.1.re)) = cexp (-2 * π * I * P.h * p.1.re) := by
    rw [← Complex.exp_conj]; congr 1; apply Complex.ext <;> simp
  have h5 : (strip ∩ {u : ℍ | inI P u.im}).indicator (1 : ℍ → ℂ) p.1 =
      strip.indicator 1 p.1 * {u : ℍ | inI P u.im}.indicator 1 p.1 := by
    by_cases ha : p.1 ∈ strip <;> by_cases hb : p.1 ∈ {u : ℍ | inI P u.im} <;>
      simp [indicator, ha, hb]
  rw [h1, h2, h3, h4, h5]
  ring

/-- **The weight-`k` pairing in coordinates.** -/
theorem QF_eq {m : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiF f z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ m) :
    ∫ p, PsiF f p.1 p.2 * conj (ft P p) =
      ∫ ζ : ℍ, ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ)) * ∫ y, KyF f P ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_gF f P hM0 hM
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hgi.aestronglyMeasurable)]
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      AzF f P p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact gF_skew f P p
  simp_rw [gF_skew]
  rw [Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_AzF f P ζ hM0 hM]

end RamanujanTau.SubconvexGeneral2
