import RamanujanTau.ThetaLift.ModularDomain

/-!
# The invariant measure on the strip

The integral over `stripSet` of a function `f` on `ℍ` is the iterated integral with `du dv / v²`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open MeasureTheory Set UpperHalfPlane
open scoped ENNReal NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The point `u + iv`, when `v > 0`. -/
def pt (p : ℝ × ℝ) : ℍ := ofComplex (p.1 + p.2 * Complex.I)

/-- The rectangle corresponding to the strip. -/
def rect : Set (ℝ × ℝ) := Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)

lemma measurableSet_rect : MeasurableSet rect := measurableSet_Ico.prod measurableSet_Ioi

/-- The transfer function on the rectangle. -/
def tr' (f : ℍ → E) (p : ℝ × ℝ) : E := (p.2 ^ 2)⁻¹ • f (pt p)

/-- The map to coordinates and its properties. -/
def toRect (z : ℍ) : ℝ × ℝ := (z.re, z.im)

lemma toRect_pt {z : ℍ} : pt (toRect z) = z := by
  have him : 0 < ((z.re : ℂ) + (z.im : ℂ) * Complex.I).im := by simpa using z.im_pos
  apply UpperHalfPlane.ext
  simp only [pt, toRect, ofComplex_apply_of_im_pos him]
  apply Complex.ext <;> simp

lemma measurable_toRect : Measurable toRect := by
  have h1 : Continuous fun z : ℍ => z.re := UpperHalfPlane.continuous_re
  have h2 : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  exact (h1.prodMk h2).measurable

/-- The strip is the preimage of the rectangle. -/
lemma strip_eq : stripSet = toRect ⁻¹' rect := by
  ext z
  simp only [stripSet, rect, toRect, mem_setOf_eq, mem_preimage, mem_prod, mem_Ico, mem_Ioi]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0, h1⟩, z.im_pos⟩
  · rintro ⟨⟨h0, h1⟩, _⟩
    exact ⟨h0, h1⟩

/-- The coordinates as a composition of embeddings. -/
lemma toRect_eq (z : ℍ) : toRect z = Complex.measurableEquivRealProd (z : ℂ) := rfl

lemma measurableEmbedding_toRect : MeasurableEmbedding toRect :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp measurableEmbedding_coe

/-- The upper half-plane in coordinates. -/
def upperR : Set (ℝ × ℝ) := univ ×ˢ Ioi (0 : ℝ)

lemma measurableSet_upperR : MeasurableSet upperR := MeasurableSet.univ.prod measurableSet_Ioi

/-- The density `v⁻²`. -/
def rhoV (p : ℝ × ℝ) : ℝ≥0 := ((p.2 ^ 2)⁻¹).toNNReal

lemma measurable_rhoV : Measurable rhoV := by
  unfold rhoV
  fun_prop

/-- **The image of the invariant measure.** -/
theorem map_toRect : (volume : Measure ℍ).map toRect =
    (volume.restrict upperR).withDensity fun p => (rhoV p : ℝ≥0∞) := by
  ext s hs
  rw [measurableEmbedding_toRect.map_apply, volume_eq_lintegral,
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  have himg : ((↑) '' (toRect ⁻¹' s) : Set ℂ) = Complex.measurableEquivRealProd ⁻¹' (s ∩ upperR) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, trivial, w.im_pos⟩
    · rintro ⟨hz, -, him⟩
      exact ⟨⟨z, him⟩, hz, rfl⟩
  rw [himg, ← Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  refine setLIntegral_congr_fun
    (Complex.measurableEquivRealProd.measurableEmbedding.measurable (hs.inter measurableSet_upperR))
    fun z hz => ?_
  have him : 0 < z.im := hz.2.2
  simp only [rhoV]
  norm_cast
  ext
  have : Complex.measurableEquivRealProd z = (z.re, z.im) := rfl
  rw [this]
  simp only [Real.coe_toNNReal _ (by positivity : 0 ≤ (z.im ^ 2)⁻¹)]
  simp [Real.nnnorm_of_nonneg him.le]

/-- The integrand on the rectangle. -/
lemma tr'_eq (f : ℍ → E) (p : ℝ × ℝ) : (rhoV p : ℝ) • f (pt p) = tr' f p := by
  unfold tr' rhoV
  rw [Real.coe_toNNReal _ (by positivity)]

lemma rect_subset : rect ⊆ upperR := fun _ h => ⟨trivial, h.2⟩

/-- **Integrability transfers from the rectangle.** -/
theorem integrableOn_strip {f : ℍ → E} (hf : IntegrableOn (tr' f) rect) :
    IntegrableOn f stripSet := by
  have h1 : IntegrableOn (f ∘ pt) rect ((volume.restrict upperR).withDensity fun p => (rhoV p : ℝ≥0∞)) := by
    rw [IntegrableOn, restrict_withDensity measurableSet_rect,
      integrable_withDensity_iff_integrable_smul measurable_rhoV, Measure.restrict_restrict measurableSet_rect,
      inter_eq_left.mpr rect_subset]
    refine hf.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (tr'_eq f p).symm
  rw [← map_toRect] at h1
  have h2 := (measurableEmbedding_toRect.integrableOn_map_iff (f := f ∘ pt) (s := rect)).mp h1
  rw [strip_eq]
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [toRect_pt]

/-- **The integral over the strip.** -/
theorem integral_strip (f : ℍ → E) :
    ∫ z in stripSet, f z = ∫ p in rect, tr' f p := by
  have h1 : ∫ p in rect, (f ∘ pt) p ∂((volume : Measure ℍ).map toRect) =
      ∫ z in toRect ⁻¹' rect, (f ∘ pt) (toRect z) :=
    measurableEmbedding_toRect.setIntegral_map _ _
  simp only [Function.comp, toRect_pt] at h1
  rw [strip_eq, ← h1, map_toRect, setIntegral_withDensity_eq_setIntegral_smul measurable_rhoV _
    measurableSet_rect, Measure.restrict_restrict measurableSet_rect, inter_eq_left.mpr rect_subset]
  exact setIntegral_congr_fun measurableSet_rect fun p _ => tr'_eq f p

/-- **Domination on the rectangle.** -/
theorem integrableOn_rect {F : ℝ × ℝ → E} {B : ℝ → ℝ} (hB : IntegrableOn B (Ioi 0))
    (hm : AEStronglyMeasurable F (volume.restrict rect))
    (hb : ∀ p ∈ rect, ‖F p‖ ≤ B p.2) : IntegrableOn F rect := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrable_const_iff.mpr (Or.inr (by simp [isFiniteMeasure_restrict]))
  have h2 := h1.mul_prod hB
  rw [IntegrableOn, rect, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [rect, Measure.volume_eq_prod, ← Measure.prod_restrict] at hm
  refine h2.mono' hm ?_
  have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))),
      p ∈ rect := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem measurableSet_rect
  filter_upwards [hmem] with p hp
  simpa using hb p hp

/-- **The iterated integral over the rectangle.** -/
theorem integral_rect {F : ℝ × ℝ → E} (hF : IntegrableOn F rect) :
    ∫ p in rect, F p = ∫ v in Ioi (0 : ℝ), ∫ u in Ico (0 : ℝ) 1, F (u, v) := by
  have hsw : ∫ p in Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1, F p.swap = ∫ p in rect, F p := by
    exact setIntegral_prod_swap (Ico (0 : ℝ) 1) (Ioi (0 : ℝ)) F
  have hI : IntegrableOn (fun p : ℝ × ℝ => F p.swap) (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := by
    have e : (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' rect = Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1 := by
      ext ⟨a, b⟩
      simp [rect]
    have hmp := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).restrict_preimage_emb
        MeasurableEquiv.prodComm.measurableEmbedding rect
    rw [e] at hmp
    exact hmp.integrable_comp_of_integrable hF
  rw [← hsw]
  exact setIntegral_prod (fun p : ℝ × ℝ => F p.swap) hI

/-- **Exchange of a sum and an integral under a summed bound.** -/
theorem tsum_integral_of_bound {ι : Type*} [Countable ι] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → E} {B : α → ℝ} (hB : Integrable B μ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hs : ∀ᵐ a ∂μ, Summable (fun i => ‖f i a‖) ∧ ∑' i, ‖f i a‖ ≤ B a) :
    (∀ i, Integrable (f i) μ) ∧ HasSum (fun i => ∫ a, f i a ∂μ) (∫ a, ∑' i, f i a ∂μ) := by
  have hle : ∀ i, ∀ᵐ a ∂μ, ‖f i a‖ ≤ B a := fun i => by
    filter_upwards [hs] with a ha
    exact (ha.1.le_tsum i fun _ _ => norm_nonneg _).trans ha.2
  have hint : ∀ i, Integrable (f i) μ := fun i => hB.mono' (hm i) (hle i)
  refine ⟨hint, ?_⟩
  have hlin : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun i => (hm i).enorm]
    have hbd : ∀ᵐ a ∂μ, ∑' i, ‖f i a‖ₑ ≤ ENNReal.ofReal (B a) := by
      filter_upwards [hs] with a ha
      have h1 : ∑' i, ‖f i a‖ₑ = ENNReal.ofReal (∑' i, ‖f i a‖) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) ha.1]
        exact tsum_congr fun i => (ofReal_norm_eq_enorm _).symm
      rw [h1]
      exact ENNReal.ofReal_le_ofReal ha.2
    exact ne_top_of_le_ne_top hB.lintegral_lt_top.ne (lintegral_mono_ae hbd)
  refine hasSum_integral_of_summable_integral_norm hint ?_
  have hS := ENNReal.summable_toReal hlin
  refine hS.congr fun i => ?_
  exact (integral_norm_eq_lintegral_enorm (hm i)).symm

end

end RamanujanTau.ThetaLift
