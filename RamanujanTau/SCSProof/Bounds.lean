/-
# Measure bounds for the test function

* `lintegral_rel_prod`: `∫⁻ A(z) 1_S(rel(z,w)) = (∫⁻ A) (∫⁻ 1_S)`.
* `lintegral_B_le`: `μ(B) ≤ 16 ε²`; `lintegral_ft_le`: `∫⁻ ‖ft‖ ≤ 16 ε³ / Y`.
* `Dh`: the invariant `|z − w̄|² / (Im z Im w)`; `Dh_smul`; `Dh_rel`; on `supp ff`, `Dh ≤ R(θ)`.
* `lintegral_U_ball_le`: `∫⁻_{U×ℍ} 1[Dh ≤ R] ≤ 4 R⁴`.
-/
import RamanujanTau.SCSProof.Test

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma measurable_rel : Measurable fun p : ℍ × ℍ => rel p.1 p.2 := continuous_rel.measurable

/-- `∫⁻ A(z) 1_S(rel(z,w)) = (∫⁻ A)(∫⁻ 1_S)`. -/
theorem lintegral_rel_prod (A : ℍ → ℝ≥0∞) (hA : Measurable A) (S : Set ℂ) (hS : MeasurableSet S) :
    ∫⁻ p : ℍ × ℍ, A p.1 * S.indicator 1 (rel p.1 p.2) =
      (∫⁻ z, A z) * ∫⁻ ζ : ℍ, S.indicator 1 (ζ : ℂ) := by
  have hm : Measurable fun p : ℍ × ℍ => A p.1 * S.indicator (1 : ℂ → ℝ≥0∞) (rel p.1 p.2) :=
    (hA.comp measurable_fst).mul ((measurable_one.indicator hS).comp measurable_rel)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  rw [← lintegral_mul_const _ hA]
  refine lintegral_congr fun z => ?_
  simp only
  have hmw : Measurable fun w : ℍ => S.indicator (1 : ℂ → ℝ≥0∞) (rel z w) :=
    (measurable_one.indicator hS).comp (measurable_rel.comp measurable_prodMk_left)
  rw [lintegral_const_mul _ hmw]
  congr 1
  rw [lintegral_affGL z]
  refine lintegral_congr fun ζ => ?_
  rw [rel_affGL]

lemma measurableSet_inB : MeasurableSet {ζ : ℂ | inB P ζ} := by
  simp only [inB, Set.setOf_and]
  exact (measurableSet_le ((Complex.measurable_re.sub measurable_const).abs) measurable_const).inter
    (measurableSet_le ((Complex.measurable_im.sub measurable_const).abs) measurable_const)

/-- `μ(B) ≤ 16 ε²`. -/
theorem lintegral_B_le :
    ∫⁻ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator 1 (ζ : ℂ) ≤ ENNReal.ofReal (16 * P.ε ^ 2) := by
  have hε := P.hε; have hε1 := P.hε1
  have hm : Measurable fun ζ : ℍ => {ζ : ℂ | inB P ζ}.indicator (1 : ℂ → ℝ≥0∞) (ζ : ℂ) :=
    (measurable_one.indicator (measurableSet_inB P)).comp UpperHalfPlane.measurable_coe
  refine (lintegral_box_le _ hm (a := P.θ - P.ε) (b := P.θ + P.ε) (c := 1 - P.ε) (d := 1 + P.ε)
    (by linarith) (by linarith) (by linarith) (fun ζ => by unfold indicator; split_ifs <;> simp)
    (fun ζ hζ => ?_)).trans ?_
  · have hmem : inB P (ζ : ℂ) := by
      by_contra h; exact hζ (indicator_of_notMem (show (ζ : ℂ) ∉ {ζ : ℂ | inB P ζ} from h) _)
    obtain ⟨h1, h2⟩ := hmem
    rw [abs_le] at h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show P.θ - P.ε ≤ (ζ : ℂ).re; linarith
    · show (ζ : ℂ).re ≤ P.θ + P.ε; linarith
    · show 1 - P.ε ≤ (ζ : ℂ).im; linarith
    · show (ζ : ℂ).im ≤ 1 + P.ε; linarith
  · refine ENNReal.ofReal_le_ofReal ?_
    have h4 : (1 / 2 : ℝ) ^ 2 ≤ (1 - P.ε) ^ 2 := by gcongr <;> linarith
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith

/-- The strip-and-window indicator. -/
noncomputable def Astrip (z : ℍ) : ℝ≥0∞ :=
  (strip ∩ {u : ℍ | inI P u.im}).indicator 1 z

lemma measurableSet_inI_set : MeasurableSet {u : ℍ | inI P u.im} := by
  simp only [inI, Set.setOf_and]
  exact (measurableSet_le measurable_const measurable_im_H).inter
    (measurableSet_le measurable_im_H measurable_const)

lemma measurable_Astrip : Measurable (Astrip P) :=
  measurable_one.indicator (measurableSet_strip.inter (measurableSet_inI_set P))

lemma lintegral_Astrip_le : ∫⁻ z, Astrip P z ≤ ENNReal.ofReal (P.ε / P.Y) := by
  have hY := P.hY; have hε := P.hε
  refine (lintegral_box_le _ (measurable_Astrip P) (a := 0) (b := 1) (c := P.Y)
    (d := P.Y * (1 + P.ε)) hY (by norm_num) (by nlinarith)
    (fun ζ => by unfold Astrip indicator; split_ifs <;> simp) (fun ζ hζ => ?_)).trans ?_
  · have hmem : ζ ∈ strip ∩ {u : ℍ | inI P u.im} := by
      by_contra h; exact hζ (indicator_of_notMem h _)
    exact ⟨hmem.1.1, hmem.1.2.le, hmem.2.1, hmem.2.2⟩
  · refine le_of_eq (congrArg ENNReal.ofReal ?_)
    field_simp; ring

lemma enorm_ft_le (p : ℍ × ℍ) :
    ‖ft P p‖ₑ ≤ Astrip P p.1 * {ζ : ℂ | inB P ζ}.indicator 1 (rel p.1 p.2) := by
  by_cases h : ft P p = 0
  · simp [h]
  obtain ⟨h1, h2⟩ := ft_ne_zero P h
  rw [Astrip, indicator_of_mem (show p.1 ∈ strip ∩ {u : ℍ | inI P u.im} from ⟨h1, h2.1⟩),
    indicator_of_mem (show rel p.1 p.2 ∈ {ζ : ℂ | inB P ζ}
    from h2.2)]
  simp only [Pi.one_apply, mul_one]
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_one.2 (norm_ft_le P p)

/-- `∫⁻ ‖ft‖ ≤ 16 ε³/Y`. -/
theorem lintegral_ft_le : ∫⁻ p, ‖ft P p‖ₑ ≤ ENNReal.ofReal (16 * P.ε ^ 3 / P.Y) := by
  calc ∫⁻ p, ‖ft P p‖ₑ
      ≤ ∫⁻ p : ℍ × ℍ, Astrip P p.1 * {ζ : ℂ | inB P ζ}.indicator 1 (rel p.1 p.2) :=
        lintegral_mono fun p => enorm_ft_le P p
    _ = (∫⁻ z, Astrip P z) * ∫⁻ ζ : ℍ, {ζ : ℂ | inB P ζ}.indicator 1 (ζ : ℂ) :=
        lintegral_rel_prod _ (measurable_Astrip P) _ (measurableSet_inB P)
    _ ≤ ENNReal.ofReal (P.ε / P.Y) * ENNReal.ofReal (16 * P.ε ^ 2) :=
        mul_le_mul' (lintegral_Astrip_le P) (lintegral_B_le P)
    _ = ENNReal.ofReal (16 * P.ε ^ 3 / P.Y) := by
        rw [← ENNReal.ofReal_mul (by have := P.hε; have := P.hY; positivity)]
        congr 1; ring

lemma lintegral_ft_ne_top : ∫⁻ p, ‖ft P p‖ₑ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_ft_le P)

/-! ### The invariant `Dh` -/

/-- `Dh(z,w) = |z − w̄|² / (Im z Im w)`. -/
noncomputable def Dh (z w : ℍ) : ℝ := Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)

lemma Dh_smul (γ : SL(2, ℤ)) (z w : ℍ) : Dh (γ • z) (γ • w) = Dh z w := by
  unfold Dh
  rw [smul_sub_conj, ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq]
  have hz := denom_ne_zero' γ z
  have hw := denom_ne_zero' γ w
  simp only [ModularGroup.denom_apply]
  push_cast
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_conj]
  have hz' : Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  have hw' : Complex.normSq ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (Complex.normSq_pos.2 hw).ne'
  have hz'' : Complex.normSq ((z : ℂ) * γ 1 0 + γ 1 1) ≠ 0 := by rw [mul_comm]; exact hz'
  have hw'' : Complex.normSq ((w : ℂ) * γ 1 0 + γ 1 1) ≠ 0 := by rw [mul_comm]; exact hw'
  have hzi := z.im_pos.ne'
  have hwi := w.im_pos.ne'
  field_simp

/-- `Dh` in relative coordinates. -/
lemma Dh_eq_rel (z w : ℍ) :
    Dh z w = ((rel z w).re ^ 2 + (1 + (rel z w).im) ^ 2) / (rel z w).im := by
  unfold Dh
  rw [rel_re, rel_im, Complex.normSq_apply]
  have hz := z.im_pos
  have hw := w.im_pos
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  change ((z.re - w.re) * (z.re - w.re) + (z.im - -w.im) * (z.im - -w.im)) / (z.im * w.im) = _
  field_simp
  ring

/-- The radius `R(θ) = 2(|θ| + 3)²`. -/
noncomputable def Rθ : ℝ := 2 * (|P.θ| + 3) ^ 2

lemma one_le_Rθ : 1 ≤ Rθ P := by
  unfold Rθ; nlinarith [abs_nonneg P.θ]

lemma Dh_le_of_suppF {p : ℍ × ℍ} (hp : p ∈ suppF P) : Dh p.1 p.2 ≤ Rθ P := by
  rw [Dh_eq_rel]
  obtain ⟨h1, h2⟩ := hp.2
  have hε1 := P.hε1
  rw [abs_le] at h1 h2
  have him : 1 / 2 ≤ (rel p.1 p.2).im := by linarith
  have hre : |(rel p.1 p.2).re| ≤ |P.θ| + 1 := by
    have := abs_sub_abs_le_abs_sub (rel p.1 p.2).re P.θ
    rw [abs_le] at *
    constructor <;> nlinarith [abs_nonneg P.θ, le_abs_self P.θ, neg_abs_le P.θ]
  rw [div_le_iff₀ (by linarith)]
  unfold Rθ
  have : (rel p.1 p.2).re ^ 2 ≤ (|P.θ| + 1) ^ 2 := by
    rw [← sq_abs]; gcongr
  nlinarith [abs_nonneg P.θ]

/-- The ball `{w : Dh(z,w) ≤ R}` has measure `≤ 2R⁴`, uniformly in `z`. -/
theorem lintegral_ball_le (z : ℍ) {R : ℝ} (hR : 1 ≤ R) :
    ∫⁻ w, {w : ℍ | Dh z w ≤ R}.indicator 1 w ≤ ENNReal.ofReal (4 * R ^ 4) := by
  rw [lintegral_affGL z]
  have hm : Measurable fun ζ : ℍ => {w : ℍ | Dh z w ≤ R}.indicator (1 : ℍ → ℝ≥0∞)
      (affGL z.re z.im z.im_pos • ζ) := by
    refine (measurable_one.indicator ?_).comp (measurePreserving_affGL _ _ _).measurable
    refine measurableSet_le ?_ measurable_const
    unfold Dh
    refine Measurable.div ?_ (measurable_const.mul measurable_im_H)
    exact Complex.continuous_normSq.measurable.comp (measurable_const.sub
      (Complex.continuous_conj.measurable.comp UpperHalfPlane.measurable_coe))
  refine (lintegral_box_le _ hm (a := -R) (b := R) (c := 1 / R) (d := R) (by positivity)
    (by linarith) (by rw [div_le_iff₀ (by linarith)]; nlinarith)
    (fun ζ => by unfold indicator; split_ifs <;> simp) (fun ζ hζ => ?_)).trans ?_
  · have hmem : Dh z (affGL z.re z.im z.im_pos • ζ) ≤ R := by
      by_contra h
      exact hζ (indicator_of_notMem (show affGL z.re z.im z.im_pos • ζ ∉ {w : ℍ | Dh z w ≤ R}
        from h) _)
    rw [Dh_eq_rel, rel_affGL] at hmem
    have hpos : 0 < (ζ : ℂ).im := ζ.im_pos
    rw [div_le_iff₀ hpos] at hmem
    have hζim : ζ.im = (ζ : ℂ).im := rfl
    have hζre : ζ.re = (ζ : ℂ).re := rfl
    rw [hζim, hζre]
    have h1 : (1 + (ζ : ℂ).im) ^ 2 ≤ R * (ζ : ℂ).im := by nlinarith [sq_nonneg (ζ : ℂ).re]
    have h2 : (ζ : ℂ).re ^ 2 ≤ R * (ζ : ℂ).im := by nlinarith [sq_nonneg (1 + (ζ : ℂ).im)]
    have hi1 : (ζ : ℂ).im ≤ R := by nlinarith
    have hi2 : 1 / R ≤ (ζ : ℂ).im := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hr2 : (ζ : ℂ).re ^ 2 ≤ R ^ 2 := by nlinarith
    have hr : |(ζ : ℂ).re| ≤ R := by
      rw [← abs_of_pos (by linarith : (0 : ℝ) < R)]; exact sq_le_sq.1 hr2
    rw [abs_le] at hr
    exact ⟨hr.1, hr.2, hi2, hi1⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have hR0 : 0 < R := by linarith
    have e1 : 4 * R ^ 4 * (1 / R) ^ 2 = 4 * R ^ 2 := by field_simp
    have e2 : (R - -R) * (R - 1 / R) = 2 * R ^ 2 - 2 := by field_simp; ring
    rw [div_le_iff₀ (by positivity), e1, e2]
    nlinarith

end RamanujanTau.SCSProof
