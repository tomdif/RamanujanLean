/-
# The invariant measure on `ℍ` and the unfolding of an `SL₂(ℤ)`-sum

* `lintegral_H`: `∫_ℍ φ dμ = ∫_{y>0} φ(x+iy) dx dy / y²` (Mathlib's `GL(2,ℝ)`-invariant measure
  `dx dy / y²` on `ℍ`, written in real coordinates);
* `measurePreserving_sl`: `w ↦ γw` preserves `μ` for `γ ∈ SL₂(ℤ)`;
* `ae_tsum_ind_U`: for a.e. `w`, `∑_γ 1_U(γw) = 2` (`U = {−½ ≤ Re < ½, |w| ≥ 1}`): every orbit
  meets `U` (at `±γ`), and the orbits meeting the unit circle form a null set;
* `lintegral_unfold_U`: `∫_ℍ 1_U(z) ∑_γ Ψ(γz) dμ = 2 ∫_ℍ Ψ dμ` for measurable `Ψ ≥ 0`.
-/
import RamanujanTau.RankinError.RSFE

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set ModularGroup
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-- `x + iy ∈ ℍ` (the junk value `i` if `y ≤ 0`). -/
noncomputable def toH (p : ℝ × ℝ) : ℍ :=
  if h : 0 < p.2 then ⟨(p.1 : ℂ) + (p.2 : ℂ) * Complex.I, by simpa using h⟩ else UpperHalfPlane.I

lemma coe_toH {p : ℝ × ℝ} (h : 0 < p.2) : (toH p : ℂ) = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  simp [toH, h]

lemma toH_re {p : ℝ × ℝ} (h : 0 < p.2) : (toH p).re = p.1 := by
  simp [UpperHalfPlane.re, coe_toH h]

lemma toH_im {p : ℝ × ℝ} (h : 0 < p.2) : (toH p).im = p.2 := by
  simp [UpperHalfPlane.im, coe_toH h]

lemma toH_re_im (w : ℍ) : toH (w.re, w.im) = w := by
  apply UpperHalfPlane.ext
  rw [coe_toH (show 0 < (w.re, w.im).2 from w.im_pos)]
  exact Complex.re_add_im _

lemma measurable_toH : Measurable toH := by
  refine (measurableEmbedding_coe.measurable_comp_iff).1 ?_
  have e : (UpperHalfPlane.coe ∘ toH) = fun p : ℝ × ℝ =>
      if 0 < p.2 then (p.1 : ℂ) + (p.2 : ℂ) * Complex.I else Complex.I := by
    funext p
    by_cases h : 0 < p.2
    · simp [coe_toH h, h]
    · simp [toH, h]
  rw [e]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  fun_prop

lemma toH_gpt {p : ℝ × ℝ} (h : 1 / 4 ≤ p.2) : toH p = gpt p.1 p.2 := by
  apply UpperHalfPlane.ext
  rw [coe_toH (by linarith)]
  have h' : (4:ℝ)⁻¹ ≤ p.2 := by norm_num; linarith
  simp [gpt, h']

lemma toH_hp {y : ℝ} (hy : 0 < y) (x : ℝ) : toH (x, y) = hp hy x := by
  apply UpperHalfPlane.ext
  rw [coe_toH (show 0 < (x, y).2 from hy), hp_coe]

lemma density_eq (z : ℍ) :
    (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal (1 / z.im ^ 2) := by
  rw [ENNReal.ofReal]
  congr 1
  ext
  rw [Real.coe_toNNReal _ (by positivity)]
  simp

lemma measurable_im_H : Measurable fun z : ℍ => z.im := UpperHalfPlane.continuous_im.measurable
lemma measurable_re_H : Measurable fun z : ℍ => z.re := UpperHalfPlane.continuous_re.measurable

lemma mE_symm (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm p = (p.1 : ℂ) + p.2 * Complex.I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- **Change of variables** `ℍ ↔ {(x,y) : y > 0}` for the invariant measure. -/
theorem lintegral_H (φ : ℍ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ w, φ w = ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, φ (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) := by
  have hρ : Measurable fun z : ℍ => ENNReal.ofReal (1 / z.im ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_im_H.pow_const 2))
  rw [UpperHalfPlane.volume_def]
  simp_rw [density_eq]
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ hφ]
  -- write the integrand as `F ∘ coe`
  set F : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / z.im ^ 2) * φ (toH (z.re, z.im)) with hF
  have hFm : Measurable F := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.div
      (Complex.measurable_im.pow_const 2))).mul (hφ.comp (measurable_toH.comp ?_))
    exact Complex.measurable_re.prodMk Complex.measurable_im
  have e1 : (fun z : ℍ => ENNReal.ofReal (1 / z.im ^ 2)) * φ = F ∘ UpperHalfPlane.coe := by
    funext z
    simp only [Pi.mul_apply, Function.comp_apply, hF]
    rw [show ((z : ℂ).re, (z : ℂ).im) = (z.re, z.im) from rfl, toH_re_im]
    rfl
  rw [e1]
  change ∫⁻ z, F (UpperHalfPlane.coe z) ∂(volume.comap UpperHalfPlane.coe) = _
  rw [← measurableEmbedding_coe.lintegral_map, measurableEmbedding_coe.map_comap]
  have hrange : Set.range UpperHalfPlane.coe = {z : ℂ | 0 < z.im} := by
    ext z; constructor
    · rintro ⟨w, rfl⟩; exact w.im_pos
    · intro hz; exact ⟨⟨z, hz⟩, rfl⟩
  rw [hrange]
  -- transport to `ℝ × ℝ`
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← (hmp.setLIntegral_comp_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding
    F {z : ℂ | 0 < z.im})]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im} =
      {p : ℝ × ℝ | 0 < p.2} := by
    ext p; simp
  rw [hpre]
  refine setLIntegral_congr_fun (measurableSet_lt measurable_const measurable_snd) fun p hp => ?_
  simp only [hF, mE_symm]
  simp [mul_comm]

/-! ### Invariance under `SL₂(ℤ)` -/

lemma measurePreserving_sl (γ : SL(2, ℤ)) : MeasurePreserving (fun w : ℍ => γ • w) volume volume := by
  have h := measurePreserving_smul
    (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
    (volume : Measure ℍ)
  have e : (fun w : ℍ => γ • w) = fun w : ℍ =>
      Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ) • w := by
    funext w; exact ModularGroup.sl_moeb γ w
  rw [e]; exact h

/-! ### The unit circle is null -/

/-- The unit circle in `ℍ`. -/
def circ : Set ℍ := {w | Complex.normSq (w : ℂ) = 1}

lemma measurableSet_circ : MeasurableSet circ :=
  measurableSet_eq_fun (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable
    measurable_const

lemma volume_circ : volume circ = 0 := by
  rw [UpperHalfPlane.volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_coe.comap_apply]
  refine measure_mono_null ?_ (Measure.addHaar_sphere volume (0 : ℂ) 1)
  rintro _ ⟨w, hw, rfl⟩
  simp only [Metric.mem_sphere, dist_zero_right]
  have h : ‖(w : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hw
  have h0 : 0 ≤ ‖(w : ℂ)‖ := norm_nonneg _
  nlinarith

lemma measurableSet_Uset : MeasurableSet Uset := by
  have h1 := measurable_re_H
  have h2 : Measurable fun w : ℍ => Complex.normSq (w : ℂ) :=
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable
  exact (measurableSet_le measurable_const h1).inter
    ((measurableSet_lt h1 measurable_const).inter (measurableSet_le measurable_const h2))

/-- **Almost every orbit meets `U` exactly at `±γ`.** -/
theorem ae_tsum_ind_U :
    ∀ᵐ w : ℍ, ∑' γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • w) = 2 := by
  have hnull : volume (⋃ γ : SL(2, ℤ), (fun w : ℍ => γ • w) ⁻¹' circ) = 0 := by
    refine measure_iUnion_null fun γ => ?_
    rw [(measurePreserving_sl γ).measure_preimage measurableSet_circ.nullMeasurableSet]
    exact volume_circ
  refine measure_mono_null (fun w hw => ?_) hnull
  simp only [mem_iUnion, mem_preimage]
  by_contra hcon
  push Not at hcon
  apply hw
  have hUS : ∀ γ : SL(2, ℤ), Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • w) =
      Sset.indicator (1 : ℍ → ℝ≥0∞) (γ • w) := by
    intro γ
    have hc : Complex.normSq ((γ • w : ℍ) : ℂ) ≠ 1 := hcon γ
    by_cases hU : γ • w ∈ Uset
    · have hS : γ • w ∈ Sset := ⟨hU.1, hU.2.1, lt_of_le_of_ne hU.2.2 (Ne.symm hc)⟩
      rw [indicator_of_mem hU, indicator_of_mem hS]
    · have hS : γ • w ∉ Sset := fun hS => hU ⟨hS.1, hS.2.1, hS.2.2.le⟩
      rw [indicator_of_notMem hU, indicator_of_notMem hS]
  refine le_antisymm ?_ ?_
  · simp_rw [hUS]
    have := tsum_le_two (Sset.indicator (1 : ℍ → ℝ≥0∞)) (fun _ => 1) (fun _ _ => rfl)
      (fun w hw => indicator_of_notMem hw _) (fun w _ => by
        simp only [indicator]; split_ifs <;> simp) w
    simpa using this
  · obtain ⟨γ₀, h₀⟩ := exists_smul_mem_U w
    have := two_le_tsum (Uset.indicator (1 : ℍ → ℝ≥0∞)) w γ₀
    rw [indicator_of_mem h₀] at this
    simpa using this

/-- **Unfolding.** `∫_ℍ 1_U(z) ∑_γ Ψ(γz) dμ = 2 ∫_ℍ Ψ dμ`. -/
theorem lintegral_unfold_U (Ψ : ℍ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z * ∑' γ : SL(2, ℤ), Ψ (γ • z) = 2 * ∫⁻ w, Ψ w := by
  have hind : Measurable (Uset.indicator (1 : ℍ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Uset
  have hm : ∀ γ : SL(2, ℤ), Measurable fun z : ℍ => Uset.indicator (1 : ℍ → ℝ≥0∞) z * Ψ (γ • z) :=
    fun γ => hind.mul (hΨ.comp (measurePreserving_sl γ).measurable)
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun γ => (hm γ).aemeasurable]
  have step : ∀ γ : SL(2, ℤ), ∫⁻ z, Uset.indicator (1 : ℍ → ℝ≥0∞) z * Ψ (γ • z) =
      ∫⁻ w, Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • w) * Ψ w := by
    intro γ
    rw [← (measurePreserving_sl γ⁻¹).lintegral_comp (hm γ)]
    congr 1; funext w
    simp only [smul_smul, mul_inv_cancel, one_smul]
  simp_rw [step]
  rw [← lintegral_tsum (f := fun γ w => Uset.indicator (1 : ℍ → ℝ≥0∞) (γ⁻¹ • w) * Ψ w)
    fun γ => ((hind.comp (measurePreserving_sl γ⁻¹).measurable).mul hΨ).aemeasurable]
  simp_rw [ENNReal.tsum_mul_right]
  rw [← lintegral_const_mul _ hΨ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_tsum_ind_U] with w hw
  rw [← hw]
  congr 1
  exact (Equiv.inv (SL(2, ℤ))).tsum_eq (fun γ => Uset.indicator (1 : ℍ → ℝ≥0∞) (γ • w))

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.lintegral_H
#print axioms RamanujanTau.RankinError.lintegral_unfold_U
