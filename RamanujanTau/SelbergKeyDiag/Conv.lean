/-
# The lag convolution identity `∫_0^h∫_0^h a(x'−x) = ∫_{−h}^{h} (h−|v|) a(v)`

For any `a` integrable on `(−h, h]` (no continuity: the diagonal approximant `Re 𝒜(v, L)`
of `SelbergKey.Arith` is only known to be measurable and bounded off `v = 0`).
Proof by Fubini on `ℝ × ℝ` with the kernel `1_{(0,h]}(x) 1_{(0,h]}(x+v)`.  Level 1.
-/
import RamanujanTau.SelbergKey.Lag

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag

open MeasureTheory Set

lemma vol_inter_Ioc {h v : ℝ} (hv : |v| ≤ h) :
    (volume (Ioc 0 h ∩ Ioc (-v) (h - v))).toReal = h - |v| := by
  rw [Ioc_inter_Ioc, Real.volume_Ioc]
  rcases le_total 0 v with hv0 | hv0
  · rw [abs_of_nonneg hv0] at hv ⊢
    rw [max_eq_left (by linarith), min_eq_right (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    ring
  · rw [abs_of_nonpos hv0] at hv ⊢
    rw [max_eq_right (by linarith), min_eq_left (by linarith),
      ENNReal.toReal_ofReal (by linarith)]

/-- **The lag convolution identity** (with integrability of the outer integrand). -/
theorem lag_conv {a : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) (ha : IntegrableOn a (Ioc (-h) h)) :
    IntervalIntegrable (fun x => ∫ x' in (0:ℝ)..h, a (x' - x)) volume 0 h ∧
    ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, a (x' - x) = ∫ v in (-h)..h, (h - |v|) * a v := by
  set at' := (Ioc (-h) h).indicator a with hat'
  have hai : Integrable at' := (integrable_indicator_iff measurableSet_Ioc).2 ha
  set F : ℝ → ℝ → ℝ := fun x v =>
    (Ioc 0 h).indicator 1 x * ((Ioc 0 h).indicator 1 (x + v) * at' v) with hF
  have hmeas1 : Measurable ((Ioc (0:ℝ) h).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioc
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => (Ioc 0 h).indicator (1 : ℝ → ℝ) z.1 * ‖at' z.2‖)
        (volume.prod volume) := by
      refine Integrable.mul_prod ?_ hai.norm
      exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => (Ioc 0 h).indicator (1 : ℝ → ℝ) z.1)
          (volume.prod volume) := (hmeas1.comp measurable_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => (Ioc 0 h).indicator (1 : ℝ → ℝ) (z.1 + z.2))
          (volume.prod volume) := (hmeas1.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ => at' z.2) (volume.prod volume) :=
        hai.aestronglyMeasurable.comp_snd
      exact h1.mul (h2.mul h3)
    · obtain ⟨x, v⟩ := z
      simp only [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_mul]
      have e1 : |(Ioc 0 h).indicator (1 : ℝ → ℝ) x| = (Ioc 0 h).indicator 1 x := by
        by_cases hx : x ∈ Ioc 0 h <;> simp [hx]
      have e2 : |(Ioc 0 h).indicator (1 : ℝ → ℝ) (x + v)| ≤ 1 := by
        by_cases hx : x + v ∈ Ioc 0 h <;> simp [hx]
      rw [e1]
      have : 0 ≤ (Ioc 0 h).indicator (1 : ℝ → ℝ) x := by
        by_cases hx : x ∈ Ioc 0 h <;> simp [hx]
      refine mul_le_mul_of_nonneg_left ?_ this
      calc |(Ioc 0 h).indicator (1 : ℝ → ℝ) (x + v)| * |at' v| ≤ 1 * |at' v| :=
            mul_le_mul_of_nonneg_right e2 (abs_nonneg _)
        _ = |at' v| := one_mul _
  -- inner integral in `v`, for fixed `x`
  have hin : ∀ x : ℝ, ∫ v, F x v = (Ioc 0 h).indicator (fun x => ∫ x' in (0:ℝ)..h, a (x' - x)) x := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
    by_cases hx : x ∈ Ioc 0 h
    · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
      have hx' := hx
      rw [mem_Ioc] at hx'
      have e : (fun v => (Ioc 0 h).indicator (1 : ℝ → ℝ) (x + v) * at' v) =
          (Ioc (-x) (h - x)).indicator a := by
        funext v
        by_cases hv : v ∈ Ioc (-x) (h - x)
        · rw [mem_Ioc] at hv
          have h1 : x + v ∈ Ioc 0 h := ⟨by linarith, by linarith⟩
          have h2 : v ∈ Ioc (-h) h := ⟨by linarith, by linarith⟩
          rw [indicator_of_mem h1, hat', indicator_of_mem h2,
            indicator_of_mem (show v ∈ Ioc (-x) (h - x) from mem_Ioc.2 hv)]
          simp
        · have h1 : x + v ∉ Ioc 0 h := by
            intro h1; rw [mem_Ioc] at h1; exact hv ⟨by linarith, by linarith⟩
          rw [indicator_of_notMem h1, indicator_of_notMem hv]; simp
      rw [e, integral_indicator measurableSet_Ioc, intervalIntegral.integral_comp_sub_right,
        intervalIntegral.integral_of_le (by linarith)]
      simp
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  -- inner integral in `x`, for fixed `v`
  have hout : ∀ v : ℝ, ∫ x, F x v = (Ioc (-h) h).indicator (fun v => (h - |v|) * a v) v := by
    intro v
    simp only [hF]
    have e : (fun x => (Ioc 0 h).indicator (1 : ℝ → ℝ) x * ((Ioc 0 h).indicator 1 (x + v) * at' v)) =
        fun x => (Ioc 0 h ∩ Ioc (-v) (h - v)).indicator (1 : ℝ → ℝ) x * at' v := by
      funext x
      rw [inter_indicator_one]
      have : (Ioc 0 h).indicator (1 : ℝ → ℝ) (x + v) = (Ioc (-v) (h - v)).indicator 1 x := by
        by_cases hx : x ∈ Ioc (-v) (h - v)
        · rw [mem_Ioc] at hx
          rw [indicator_of_mem (show x + v ∈ Ioc 0 h from ⟨by linarith, by linarith⟩),
            indicator_of_mem (show x ∈ Ioc (-v) (h - v) from ⟨by linarith, by linarith⟩)]
          rfl
        · have h1 : x + v ∉ Ioc 0 h := by
            intro h1; rw [mem_Ioc] at h1; exact hx ⟨by linarith, by linarith⟩
          rw [indicator_of_notMem h1, indicator_of_notMem hx]
      rw [this, Pi.mul_apply]; ring
    rw [e, integral_mul_const, integral_indicator_one ((measurableSet_Ioc).inter measurableSet_Ioc)]
    by_cases hv : v ∈ Ioc (-h) h
    · have hv' := hv
      rw [mem_Ioc] at hv'
      rw [hat', indicator_of_mem hv, indicator_of_mem hv, measureReal_def,
        vol_inter_Ioc (abs_le.2 ⟨by linarith, hv'.2⟩)]
    · rw [hat', indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]
  have hswap := integral_integral_swap hint
  simp only [hin, hout] at hswap
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc] at hswap
  have hl := hint.integral_prod_left
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh]
    have : Integrable (fun x => ∫ v, F x v) := hl
    simp only [hin] at this
    exact (integrable_indicator_iff measurableSet_Ioc).1 this
  · rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le (by linarith), hswap]

end RamanujanTau.SelbergKeyDiag
