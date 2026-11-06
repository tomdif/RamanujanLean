/-
# Measure-theoretic helpers on `ℍ`

* `affH x y ζ = x + yζ` is measure preserving (`GL(2,ℝ)`-invariance of `dx dy/y²`);
  `rel z w = (w − Re z)/Im z` inverts it.
* `lintegral_box_le`: a function `≤ 1` supported in a box `[a,b] × [c,d]`, `c > 0`, has
  `∫⁻ ≤ (b−a)(d−c)/c²`.
* `integral_H`: `∫_ℍ φ = ∫_{y>0} φ(x+iy) dx dy / y²` for complex `φ`.
-/
import RamanujanTau.SCSProof.Unfold2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError
open scoped MatrixGroups ENNReal

/-- The relative position `(w − Re z)/Im z`. -/
noncomputable def rel (z w : ℍ) : ℂ := ((w : ℂ) - z.re) / z.im

lemma rel_im (z w : ℍ) : (rel z w).im = w.im / z.im := by
  unfold rel
  rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]; rfl

lemma rel_re (z w : ℍ) : (rel z w).re = (w.re - z.re) / z.im := by
  unfold rel
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]; rfl

lemma rel_im_pos (z w : ℍ) : 0 < (rel z w).im := by
  rw [rel_im]; exact div_pos w.im_pos z.im_pos

/-- The affine matrix `[[y, x],[0, 1]]`. -/
noncomputable def affGL (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![y, x; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simp; exact hy.ne')

lemma affGL_det (x y : ℝ) (hy : 0 < y) : 0 < (affGL x y hy).det.val := by
  simp [affGL, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of, hy]

lemma coe_affGL_smul (x y : ℝ) (hy : 0 < y) (ζ : ℍ) :
    ((affGL x y hy • ζ : ℍ) : ℂ) = (x : ℂ) + y * (ζ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (affGL_det x y hy)]
  simp [affGL, UpperHalfPlane.num, UpperHalfPlane.denom]
  ring

lemma measurePreserving_affGL (x y : ℝ) (hy : 0 < y) :
    MeasurePreserving (fun ζ : ℍ => affGL x y hy • ζ) volume volume :=
  measurePreserving_smul (affGL x y hy) (volume : Measure ℍ)

/-- The measurable equivalence `ζ ↦ x + yζ`. -/
noncomputable def affEquiv (x y : ℝ) (hy : 0 < y) : ℍ ≃ᵐ ℍ where
  toFun ζ := affGL x y hy • ζ
  invFun w := (affGL x y hy)⁻¹ • w
  left_inv ζ := by simp
  right_inv w := by simp
  measurable_toFun := (measurePreserving_affGL x y hy).measurable
  measurable_invFun := (measurable_const_smul _ : Measurable fun w : ℍ => (affGL x y hy)⁻¹ • w)

lemma rel_affGL (z : ℍ) (ζ : ℍ) : rel z (affGL z.re z.im z.im_pos • ζ) = (ζ : ℂ) := by
  unfold rel
  rw [coe_affGL_smul]
  have : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  field_simp
  ring

/-- `∫⁻_w F(w) = ∫⁻_ζ F(Re z + Im z · ζ)`. -/
lemma lintegral_affGL (z : ℍ) (F : ℍ → ℝ≥0∞) :
    ∫⁻ w, F w = ∫⁻ ζ, F (affGL z.re z.im z.im_pos • ζ) := by
  rw [← (measurePreserving_affGL z.re z.im z.im_pos).lintegral_comp_emb
    (affEquiv z.re z.im z.im_pos).measurableEmbedding]

lemma integral_affGL (z : ℍ) (F : ℍ → ℂ) :
    ∫ w, F w = ∫ ζ, F (affGL z.re z.im z.im_pos • ζ) := by
  rw [← (measurePreserving_affGL z.re z.im z.im_pos).integral_comp
    (affEquiv z.re z.im z.im_pos).measurableEmbedding]

/-- **Box bound.** -/
theorem lintegral_box_le (φ : ℍ → ℝ≥0∞) (hφ : Measurable φ) {a b c d : ℝ} (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (h1 : ∀ ζ, φ ζ ≤ 1)
    (hsupp : ∀ ζ : ℍ, φ ζ ≠ 0 → a ≤ ζ.re ∧ ζ.re ≤ b ∧ c ≤ ζ.im ∧ ζ.im ≤ d) :
    ∫⁻ ζ, φ ζ ≤ ENNReal.ofReal ((b - a) * (d - c) / c ^ 2) := by
  rw [lintegral_H φ hφ]
  have hle : ∀ p ∈ {p : ℝ × ℝ | 0 < p.2}, φ (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) ≤
      (Icc a b ×ˢ Icc c d).indicator (fun _ => ENNReal.ofReal (1 / c ^ 2)) p := by
    intro p hp
    by_cases h0 : φ (toH p) = 0
    · simp [h0]
    obtain ⟨ha, hb, hc', hd⟩ := hsupp _ h0
    rw [toH_re hp] at ha hb
    rw [toH_im hp] at hc' hd
    have hmem : p ∈ Icc a b ×ˢ Icc c d := ⟨⟨ha, hb⟩, ⟨hc', hd⟩⟩
    rw [indicator_of_mem hmem]
    calc φ (toH p) * ENNReal.ofReal (1 / p.2 ^ 2) ≤ 1 * ENNReal.ofReal (1 / c ^ 2) := by
          refine mul_le_mul' (h1 _) (ENNReal.ofReal_le_ofReal ?_)
          gcongr
      _ = _ := one_mul _
  calc ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, φ (toH p) * ENNReal.ofReal (1 / p.2 ^ 2)
      ≤ ∫⁻ p in {p : ℝ × ℝ | 0 < p.2},
          (Icc a b ×ˢ Icc c d).indicator (fun _ => ENNReal.ofReal (1 / c ^ 2)) p :=
        setLIntegral_mono' (measurableSet_lt measurable_const measurable_snd) hle
    _ ≤ ∫⁻ p, (Icc a b ×ˢ Icc c d).indicator (fun _ => ENNReal.ofReal (1 / c ^ 2)) p :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (1 / c ^ 2) * volume (Icc a b ×ˢ Icc c d) := by
        rw [lintegral_indicator_const (measurableSet_Icc.prod measurableSet_Icc)]
    _ = ENNReal.ofReal ((b - a) * (d - c) / c ^ 2) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
        rw [← ENNReal.ofReal_mul (sub_nonneg.2 hab), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end RamanujanTau.SCSProof
