/-
# Item 3 (part 1): the pairing `∫ Ψ_{a,b} conj ft` as an integral of horocycle coefficients

Copy of `SCSProof.Qform*`/`Main1` with `Ψ` replaced by `Ψ_{a,b}` and the coefficient
`cfAB(y,ζ) = (y(i − ζ̄))¹² e^{−2πℓy} G_{a,b,ℓ}(2πy(1 + iζ̄))` (`coeff_PsiAB`), `ℓ = P.h`:

* `Q_eqAB`: `∫ Ψ_{a,b} conj ft = ∫_ζ 1_B(ζ) ∫_y 1_I(y) y⁻² cfAB(y,ζ)`;
* **`main_term_leAB`**: `|c₀| m_I m_B ≤ ‖∫ Ψ_{a,b} conj ft‖ + E m_I m_B` whenever
  `‖cfAB(y,ζ) − c₀‖ ≤ E` on the box.
-/
import RamanujanTau.SCS2Coprime.Holder2

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par) (a b : ℕ+)

lemma norm_PsiAB_le_Dh {M : ℝ} (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (z w : ℍ) :
    ‖PsiAB a b z w‖ ≤ M * Dh z w ^ 6 := hM z w

lemma enorm_PsiAB_ft_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (p : ℍ × ℍ) :
    ‖PsiAB a b p.1 p.2‖ₑ * ‖ft P p‖ₑ ≤ ENNReal.ofReal (M * Rθ P ^ 6) * ‖ft P p‖ₑ := by
  by_cases h : ft P p = 0
  · simp [h]
  gcongr
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ((norm_PsiAB_le_Dh a b hM p.1 p.2).trans ?_)
  have hD := Dh_le_of_ft P p h
  have hD0 := Dh_nonneg p
  gcongr

/-- The closed-form horocycle coefficient. -/
noncomputable def cfAB (y : ℝ) (ζ : ℍ) : ℂ :=
  ((y : ℂ) * (I - conj (ζ : ℂ))) ^ 12 * (Real.exp (-2 * π * P.h * y) : ℂ) *
    GAB a b (P.h : ℤ) (2 * π * y * (1 + I * conj (ζ : ℂ)))

lemma norm_PsiAB_aff {M : ℝ} (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (z ζ : ℍ) :
    ‖PsiAB a b z (affGL z.re z.im z.im_pos • ζ)‖ ≤ M * Dz ζ ^ 6 := by
  have := norm_PsiAB_le_Dh a b hM z (affGL z.re z.im z.im_pos • ζ)
  rwa [Dh_eq_rel, rel_affGL] at this

lemma measurable_gAB : Measurable fun p : ℍ × ℍ => PsiAB a b p.1 p.2 * conj (ft P p) :=
  (measurable_PsiAB a b).mul (Complex.continuous_conj.measurable.comp (measurable_ft P))

lemma integrable_gAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    Integrable fun p : ℍ × ℍ => PsiAB a b p.1 p.2 * conj (ft P p) := by
  refine ⟨(measurable_gAB P a b).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp_rw [enorm_mul, RCLike.enorm_conj]
  refine lt_of_le_of_lt (b := ENNReal.ofReal (M * Rθ P ^ 6) * ∫⁻ p, ‖ft P p‖ₑ) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ft_ne_top P).lt_top)
  rw [← lintegral_const_mul _ (measurable_ft P).enorm]
  exact lintegral_mono fun p => enorm_PsiAB_ft_le P a b hM0 hM p

/-- The `z`-integrand for fixed relative position `ζ`. -/
noncomputable def AzAB (ζ : ℍ) (z : ℍ) : ℂ :=
  (strip ∩ {u : ℍ | inI P u.im}).indicator (1 : ℍ → ℂ) z *
    (cexp (-2 * π * I * P.h * z.re) * PsiAB a b z (affGL z.re z.im z.im_pos • ζ))

/-- Its coordinate version. -/
noncomputable def HfAB (ζ : ℍ) (p : ℝ × ℝ) : ℂ :=
  (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator (fun p : ℝ × ℝ =>
    ((1 / p.2 ^ 2 : ℝ) : ℂ) * (cexp (-2 * π * I * P.h * p.1) *
      PsiAB a b (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ))) p

lemma measurable_PsiAB_comp {α : Type*} [MeasurableSpace α] {u v : α → ℍ} (hu : Measurable u)
    (hv : Measurable v) : Measurable fun t => PsiAB a b (u t) (v t) :=
  Measurable.comp (f := fun t => (u t, v t)) (measurable_PsiAB a b) (hu.prodMk hv)

lemma integrable_HfAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (ζ : ℍ) :
    Integrable (HfAB P a b ζ) := by
  have hY := P.hY
  have hbox : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hmeas : Measurable fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) *
      (cexp (-2 * π * I * P.h * p.1) *
        PsiAB a b (toH p) (affGL (toH p).re (toH p).im (toH p).im_pos • ζ)) := by
    refine (Complex.measurable_ofReal.comp (measurable_const.div
      (measurable_snd.pow_const 2))).mul ((Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_fst))).mul ?_)
    exact measurable_PsiAB_comp a b (u := toH)
      (v := fun p : ℝ × ℝ => affGL (toH p).re (toH p).im (toH p).im_pos • ζ)
      measurable_toH (measurable_toH_aff ζ)
  refine Integrable.mono' (g := (Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))).indicator
    (fun _ => 1 / P.Y ^ 2 * (M * Dz ζ ^ 6))) ?_ ((hmeas.indicator hbox).aestronglyMeasurable) ?_
  · refine (integrable_indicator_iff hbox).2 (integrableOn_const ?_)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun p => ?_
    unfold HfAB
    by_cases hp : p ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε))
    · rw [indicator_of_mem hp, indicator_of_mem hp, norm_mul, norm_mul]
      have hy : P.Y ≤ p.2 := hp.2.1
      have hy0 : 0 < p.2 := hY.trans_le hy
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Complex.ofReal_natCast,
        show (-2 * ↑π * I * ((P.h : ℝ) : ℂ) * (p.1 : ℂ)) = ((-2 * π * P.h * p.1 : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
      gcongr
      · exact norm_PsiAB_aff a b hM _ _
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero]

lemma integral_Az_eq_HfAB (ζ : ℍ) : ∫ z, AzAB P a b ζ z = ∫ p, HfAB P a b ζ p := by
  have hzero : ∀ p : ℝ × ℝ, p ∉ {p : ℝ × ℝ | 0 < p.2} → HfAB P a b ζ p = 0 := by
    intro p hp
    simp only [mem_setOf_eq, not_lt] at hp
    unfold HfAB
    refine indicator_of_notMem (fun hb => ?_) _
    have := hb.2.1
    have := P.hY
    linarith
  rw [integral_H, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_snd) fun p hp => ?_
  simp only [AzAB, HfAB]
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
noncomputable def KyAB (ζ : ℍ) (y : ℝ) : ℂ :=
  (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * cfAB P a b y ζ) y

lemma integral_Hf_xAB (ζ : ℍ) (y : ℝ) : ∫ x, HfAB P a b ζ (x, y) = KyAB P a b ζ y := by
  unfold KyAB
  by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
  · have hy0 : 0 < y := P.hY.trans_le hy.1
    rw [indicator_of_mem hy]
    have e : ∀ x : ℝ, HfAB P a b ζ (x, y) = (Ico (0 : ℝ) 1).indicator (fun x => ((1 / y ^ 2 : ℝ) : ℂ) *
        (PsiAB a b (hp hy0 x) (aff hy0 x ζ) * cexp (-2 * π * I * P.h * x))) x := by
      intro x
      unfold HfAB
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · rw [indicator_of_mem (show (x, y) ∈ Ico (0 : ℝ) 1 ×ˢ Icc P.Y (P.Y * (1 + P.ε)) from
          ⟨hx, hy⟩), indicator_of_mem hx, aff_eq_affGL hy0, toH_hp hy0]
        ring
      · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]
    simp_rw [e]
    rw [integral_indicator measurableSet_Ico, integral_const_mul]
    unfold cfAB
    have hc := coeff_PsiAB a b (P.h : ℤ) hy0 ζ
    simp only [Int.cast_natCast] at hc
    rw [← hc]
    congr 1
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  · rw [indicator_of_notMem hy]
    have : ∀ x : ℝ, HfAB P a b ζ (x, y) = 0 := fun x => by
      unfold HfAB; exact indicator_of_notMem (fun h => hy h.2) _
    simp [this]

lemma integral_AzAB (ζ : ℍ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ∫ z, AzAB P a b ζ z = ∫ y, KyAB P a b ζ y := by
  rw [integral_Az_eq_HfAB, Measure.volume_eq_prod,
    integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact integrable_HfAB P a b hM0 hM ζ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => integral_Hf_xAB P a b ζ y)

lemma g_skewAB (p : ℍ × ℍ) :
    (fun p : ℍ × ℍ => PsiAB a b p.1 p.2 * conj (ft P p)) (skew p) =
      ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) * AzAB P a b p.2 p.1 := by
  simp only
  rw [ft_skew]
  unfold AzAB skew
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

/-- **The pairing in coordinates.** -/
theorem Q_eqAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ∫ p, PsiAB a b p.1 p.2 * conj (ft P p) =
      ∫ ζ : ℍ, ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ)) * ∫ y, KyAB P a b ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_gAB P a b hM0 hM
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hgi.aestronglyMeasurable)]
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      AzAB P a b p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact g_skewAB P a b p
  simp_rw [g_skewAB]
  rw [Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_AzAB P a b ζ hM0 hM]

/-- The integrated `ζ`-function is integrable. -/
lemma integrable_FζAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    Integrable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, KyAB P a b ζ y := by
  have hmp := measurePreserving_skew
  have hgi := integrable_gAB P a b hM0 hM
  have hint : Integrable (fun p : ℍ × ℍ => ({ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (p.2 : ℂ)) *
      AzAB P a b p.2 p.1) := by
    have := (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    exact g_skewAB P a b p
  rw [Measure.volume_eq_prod] at hint
  have := hint.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_AzAB P a b ζ hM0 hM]

lemma integrable_KyAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (ζ : ℍ) :
    Integrable (KyAB P a b ζ) := by
  have h := integrable_HfAB P a b hM0 hM ζ
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_right.congr (Filter.Eventually.of_forall fun y => integral_Hf_xAB P a b ζ y)

/-- **Main-term comparison.** -/
theorem main_term_leAB {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ,
    ‖PsiAB a b z w‖ ≤ M * (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6)
    (c0 : ℂ) (E : ℝ) (hE : ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cfAB P a b y ζ - c0‖ ≤ E) :
    ‖c0‖ * (mI P * mB P) ≤ ‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ + E * (mI P * mB P) := by
  have hY := P.hY
  have hE0 : 0 ≤ E ∨ ¬ ∃ ζ : ℍ, inB P (ζ : ℂ) := by
    by_cases hex : ∃ ζ : ℍ, inB P (ζ : ℂ)
    · obtain ⟨ζ, hζ⟩ := hex
      exact Or.inl ((norm_nonneg _).trans (hE P.Y ⟨le_rfl, by nlinarith [P.hε]⟩ ζ hζ))
    · exact Or.inr hex
  rw [Q_eqAB P a b hM0 hM]
  set F := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * ∫ y, KyAB P a b ζ y
  set F0 := fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℂ) (ζ : ℂ) * (c0 * (mI P : ℂ))
  have hF := integrable_FζAB P a b hM0 hM
  have hF0 : Integrable F0 := (integrable_inB_C P).mul_const _
  have hc0W : ∫ ζ, F0 ζ = c0 * ((mI P * mB P : ℝ) : ℂ) := by
    simp only [F0]
    rw [integral_mul_const, integral_inB_C]; push_cast; ring
  -- inner bound
  have hinner : ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖(∫ y, KyAB P a b ζ y) - c0 * (mI P : ℂ)‖ ≤ E * mI P := by
    intro ζ hζ
    have hKi := integrable_KyAB P a b hM0 hM ζ
    have hc : Integrable fun y : ℝ => (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y := by
      refine (integrable_indicator_iff measurableSet_Icc).2 ?_
      exact ((integrableOn_inv_sq P).ofReal).mul_const _
    have hcint : ∫ y, (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y = c0 * (mI P : ℂ) := by
      rw [integral_indicator measurableSet_Icc, integral_mul_const, integral_complex_ofReal]
      unfold mI; ring
    rw [← hcint, ← integral_sub hKi hc]
    have hbd : ∀ y, ‖KyAB P a b ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
        (fun y => ((1 / y ^ 2 : ℝ) : ℂ) * c0) y‖ ≤
        (Icc P.Y (P.Y * (1 + P.ε))).indicator (fun y => 1 / y ^ 2 * E) y := by
      intro y
      unfold KyAB
      by_cases hy : y ∈ Icc P.Y (P.Y * (1 + P.ε))
      · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy, ← mul_sub, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (by have := hY.trans_le hy.1; positivity)]
        gcongr
        exact hE y hy ζ hζ
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy]; simp
    calc ‖∫ y, (KyAB P a b ζ y - (Icc P.Y (P.Y * (1 + P.ε))).indicator
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

end RamanujanTau.SCS2Coprime
