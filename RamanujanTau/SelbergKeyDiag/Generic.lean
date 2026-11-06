/-
# M4, analytic core: a lag integral is controlled by a pointwise approximant

`lagInt_le_of_approx`: if `G` is jointly continuous and, for every `t ∈ [A,B]` and every
`x ≠ x'` in `[0,h]`, `|G(t+x, x'−x) − a(x'−x, ℓ(t))| ≤ ε` with `a(·, L)` measurable, and the
`(h−|v|)`-integrals of `a(·, ℓ(t))` are bounded by `M`, then for every continuous window
`0 ≤ φ ≤ 1`

    lagInt G φ A B h ≤ (B − A)(M + ε h²).

The approximant may be singular on the diagonal `x = x'` (`v = 0`), as `𝒜(v,L)` is.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag.Conv
import RamanujanTau.SelbergKey.Reduce

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag

open MeasureTheory Set Filter
open RamanujanTau.SelbergKey

lemma ae_ne_real (c : ℝ) : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ c := by
  rw [ae_iff]; simp

/-- `lagInt` with the `t`-integral outermost. -/
lemma lagInt_eq_outer {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {A B h : ℝ} (hAB : A ≤ B) (hh : 0 ≤ h) :
    lagInt G φ A B h = ∫ t in A..B, φ t * ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x) := by
  unfold lagInt
  have c3 : Continuous (fun q : (ℝ × ℝ) × ℝ => φ q.2 * G (q.2 + q.1.1) (q.1.2 - q.1.1)) := cont_lag hG hφ
  -- swap `x'` and `t` inside
  have e1 : ∀ x : ℝ, (∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * G (t + x) (x' - x)) =
      ∫ t in A..B, ∫ x' in (0:ℝ)..h, φ t * G (t + x) (x' - x) := by
    intro x
    have hc : Continuous (Function.uncurry fun (x' t : ℝ) => φ t * G (t + x) (x' - x)) :=
      c3.comp (Continuous.prodMk (Continuous.prodMk continuous_const continuous_fst) continuous_snd)
    exact intervalIntegral_swap hc hh hAB
  simp_rw [e1]
  have hc2 : Continuous (Function.uncurry fun (x t : ℝ) => ∫ x' in (0:ℝ)..h, φ t * G (t + x) (x' - x)) := by
    have : Continuous (Function.uncurry fun (p : ℝ × ℝ) (x' : ℝ) => φ p.2 * G (p.2 + p.1) (x' - p.1)) :=
      c3.comp (Continuous.prodMk (Continuous.prodMk (continuous_fst.comp continuous_fst) continuous_snd)
        (continuous_snd.comp continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 h
  rw [intervalIntegral_swap hc2 hh hAB]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral.integral_const_mul]

lemma continuous_inner2 {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) (h : ℝ) :
    Continuous fun t => ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x) := by
  have c1 : Continuous (Function.uncurry fun (p : ℝ × ℝ) (x' : ℝ) => G (p.1 + p.2) (x' - p.2)) :=
    hG.comp (Continuous.prodMk ((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst))
      (continuous_snd.sub (continuous_snd.comp continuous_fst)))
  have c2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) c1 0 h
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun t x => ∫ x' in (0:ℝ)..h, G (t + x) (x' - x)) c2 0 h

/-- **The inner double integral is bounded by the approximant's kernel integral.** -/
theorem inner_le_of_approx {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {a : ℝ → ℝ}
    (ha : Measurable a) {t h ε Mg : ℝ} (hh : 0 ≤ h)
    (hMg : ∀ x ∈ Icc 0 h, ∀ v ∈ Icc (-h) h, |G (t + x) v| ≤ Mg)
    (happ : ∀ x ∈ Icc 0 h, ∀ x' ∈ Icc 0 h, x' ≠ x → |G (t + x) (x' - x) - a (x' - x)| ≤ ε) :
    (∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x)) ≤
      (∫ v in (-h)..h, (h - |v|) * a v) + ε * h ^ 2 := by
  -- `a` is bounded off `0` on `[−h, h]`
  have hbd : ∀ v ∈ Icc (-h) h, v ≠ 0 → |a v| ≤ Mg + ε := by
    intro v hv hv0
    have hx : (h - v) / 2 ∈ Icc 0 h := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have hx' : (h + v) / 2 ∈ Icc 0 h := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hne : (h + v) / 2 ≠ (h - v) / 2 := by intro e; apply hv0; linarith
    have e : (h + v) / 2 - (h - v) / 2 = v := by ring
    have h1 := happ _ hx _ hx' hne
    have h2 := hMg _ hx v hv
    rw [e] at h1
    calc |a v| = |G (t + (h - v) / 2) v - (G (t + (h - v) / 2) v - a v)| := by ring_nf
      _ ≤ |G (t + (h - v) / 2) v| + |G (t + (h - v) / 2) v - a v| := abs_sub _ _
      _ ≤ Mg + ε := add_le_add h2 h1
  have haI : IntegrableOn a (Ioc (-h) h) := by
    refine Measure.integrableOn_of_bounded (M := Mg + ε) (by simp [Real.volume_Ioc])
      ha.aestronglyMeasurable ?_
    have h0 := ae_restrict_of_ae (μ := volume) (s := Ioc (-h) h) (ae_ne_real 0)
    filter_upwards [h0, ae_restrict_mem measurableSet_Ioc] with v hv0 hv
    rw [Real.norm_eq_abs]
    exact hbd v (Ioc_subset_Icc_self hv) hv0
  have haII : IntervalIntegrable a volume (-h) h :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 haI
  obtain ⟨hint, hconv⟩ := lag_conv hh haI
  -- integrability of `x' ↦ a(x' − x)`
  have hshift : ∀ x ∈ Icc 0 h, IntervalIntegrable (fun x' => a (x' - x)) volume 0 h := by
    intro x hx
    have h1 : IntervalIntegrable a volume (-x) (h - x) :=
      haII.mono_set (uIcc_subset_uIcc (by
        rw [uIcc_of_le (by linarith)]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩) (by
        rw [uIcc_of_le (by linarith)]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩))
    have h2 := h1.comp_sub_right x
    simpa using h2
  have hGc : ∀ x, Continuous fun x' => G (t + x) (x' - x) := fun x =>
    hG.comp (Continuous.prodMk continuous_const (continuous_id.sub continuous_const))
  have hin : ∀ x ∈ Icc 0 h, (∫ x' in (0:ℝ)..h, G (t + x) (x' - x)) ≤
      (∫ x' in (0:ℝ)..h, a (x' - x)) + ε * h := by
    intro x hx
    have hI := hshift x hx
    have e : (∫ x' in (0:ℝ)..h, a (x' - x)) + ε * h = ∫ x' in (0:ℝ)..h, (a (x' - x) + ε) := by
      rw [intervalIntegral.integral_add hI intervalIntegrable_const, intervalIntegral.integral_const]
      simp; ring
    rw [e]
    refine intervalIntegral.integral_mono_ae_restrict hh ((hGc x).intervalIntegrable _ _)
      (hI.add intervalIntegrable_const) ?_
    have h0 := ae_restrict_of_ae (μ := volume) (s := Icc 0 h) (ae_ne_real x)
    filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with x' hx'0 hx'
    have := happ x hx x' hx' hx'0
    have := (abs_le.1 this).2
    linarith
  have hcont : Continuous fun x => ∫ x' in (0:ℝ)..h, G (t + x) (x' - x) := by
    have c1 : Continuous (Function.uncurry fun (x x' : ℝ) => G (t + x) (x' - x)) :=
      hG.comp (Continuous.prodMk (continuous_const.add continuous_fst) (continuous_snd.sub continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' c1 0 h
  calc (∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x))
      ≤ ∫ x in (0:ℝ)..h, ((∫ x' in (0:ℝ)..h, a (x' - x)) + ε * h) :=
        intervalIntegral.integral_mono_on hh (hcont.intervalIntegrable _ _)
          (hint.add intervalIntegrable_const) hin
    _ = (∫ v in (-h)..h, (h - |v|) * a v) + ε * h ^ 2 := by
        rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const,
          hconv]
        simp; ring

/-- **M4 core**: the lag integral from a pointwise approximant with bounded kernel integrals. -/
theorem lagInt_le_of_approx {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G))
    {a : ℝ → ℝ → ℝ} (ha : ∀ L, Measurable fun v => a v L) (ℓ : ℝ → ℝ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∀ t, φ t ≤ 1)
    {A B h ε M : ℝ} (hAB : A ≤ B) (hh : 0 ≤ h) (hε : 0 ≤ ε)
    (happ : ∀ t ∈ Icc A B, ∀ x ∈ Icc 0 h, ∀ x' ∈ Icc 0 h, x' ≠ x →
      |G (t + x) (x' - x) - a (x' - x) (ℓ t)| ≤ ε)
    (hM : ∀ t ∈ Icc A B, |∫ v in (-h)..h, (h - |v|) * a v (ℓ t)| ≤ M) :
    lagInt G φ A B h ≤ (B - A) * (M + ε * h ^ 2) := by
  rw [lagInt_eq_outer hG hφ hAB hh]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM A ⟨le_rfl, hAB⟩)
  have hc0 : 0 ≤ M + ε * h ^ 2 := by positivity
  -- a bound for `G` on the compact region
  obtain ⟨Mg, hMg⟩ := (isCompact_Icc.prod (isCompact_Icc (a := -h) (b := h))).exists_bound_of_continuousOn
    (s := Icc A (B + h) ×ˢ Icc (-h) h) hG.continuousOn
  have hJ : ∀ t ∈ Icc A B, (∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x)) ≤ M + ε * h ^ 2 := by
    intro t ht
    refine (inner_le_of_approx hG (ha (ℓ t)) hh (Mg := Mg) (fun x hx v hv => ?_)
      (happ t ht)).trans ?_
    · have := hMg (t + x, v) ⟨⟨by linarith [ht.1, hx.1], by linarith [ht.2, hx.2]⟩, hv⟩
      simpa [Real.norm_eq_abs] using this
    · have := (abs_le.1 (hM t ht)).2
      linarith
  have hcJ := continuous_inner2 hG h
  calc (∫ t in A..B, φ t * ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, G (t + x) (x' - x))
      ≤ ∫ t in A..B, (M + ε * h ^ 2) :=
        intervalIntegral.integral_mono_on hAB ((hφ.mul hcJ).intervalIntegrable _ _)
          intervalIntegrable_const fun t ht => by
            have h1 := hJ t ht
            calc φ t * _ ≤ φ t * (M + ε * h ^ 2) := mul_le_mul_of_nonneg_left h1 (hφ0 t)
              _ ≤ 1 * (M + ε * h ^ 2) := mul_le_mul_of_nonneg_right (hφ1 t) hc0
              _ = _ := one_mul _
    _ = (B - A) * (M + ε * h ^ 2) := by rw [intervalIntegral.integral_const]; simp

end RamanujanTau.SelbergKeyDiag
