/-
# The lag form of `∫ I(t)²`

For continuous `F` (here `F = Z·w`) and any continuous weight `φ`,

    ∫_A^B φ(t) (∫_t^{t+h} F)² dt = ∫_0^h ∫_0^h ∫_A^B φ(t) F(t+x) F(t+x') dt dx' dx
                                   = ∫_0^h ∫_0^h ∫_{A+x}^{B+x} φ(u−x) F(u) F(u + (x'−x)) du dx' dx,

so `∫ I²` is the `(h−|v|)`-weighted integral over lags `v = x'−x ∈ [−h, h]` of the lag
correlations `∫ F(u)F(u+v)`.  This is the entry point for Selberg's key lemma: the lag product
`Z(u)Z(u+v)` is then expanded by `ShiftAFE.ZH_mul_ZH_afe`.  Since `I² ≥ 0`, any weight
`φ ≥ 1_{[T,2T]}` gives an upper bound (`sk_le_weighted`).  Level 1.
-/
import RamanujanTau.SelbergKey.ShiftAFE

set_option autoImplicit false

namespace RamanujanTau.SelbergKey

open MeasureTheory Set Filter

/-- Fubini for interval integrals of a jointly continuous function. -/
lemma intervalIntegral_swap {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
    exact (hf.continuousOn.integrableOn_compact hK).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- `(∫_t^{t+h} F)² = ∫_0^h ∫_0^h F(t+x) F(t+x')`. -/
lemma shortInt_sq (F : ℝ → ℝ) (t h : ℝ) :
    (∫ u in t..t + h, F u) ^ 2 = ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, F (t + x) * F (t + x') := by
  have e : (∫ u in t..t + h, F u) = ∫ x in (0:ℝ)..h, F (t + x) := by
    rw [intervalIntegral.integral_comp_add_left F t]; simp
  rw [e, sq, ← intervalIntegral.integral_mul_const]
  congr 1; ext x
  rw [← intervalIntegral.integral_const_mul]

/-- **Lag form** of the weighted mean square of the short integrals. -/
theorem weighted_shortInt_sq {F φ : ℝ → ℝ} (hF : Continuous F) (hφ : Continuous φ)
    {A B h : ℝ} (hAB : A ≤ B) (hh : 0 ≤ h) :
    ∫ t in A..B, φ t * (∫ u in t..t + h, F u) ^ 2 =
      ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, ∫ t in A..B, φ t * (F (t + x) * F (t + x')) := by
  simp_rw [shortInt_sq F]
  have e1 : ∀ t, φ t * (∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, F (t + x) * F (t + x')) =
      ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h, φ t * (F (t + x) * F (t + x')) := by
    intro t
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x
    rw [← intervalIntegral.integral_const_mul]
  simp_rw [e1]
  -- swap `t` with `x`
  have hc1 : Continuous (Function.uncurry fun (t x : ℝ) =>
      ∫ x' in (0:ℝ)..h, φ t * (F (t + x) * F (t + x'))) := by
    have : Continuous (Function.uncurry fun (p : ℝ × ℝ) (x' : ℝ) =>
        φ p.1 * (F (p.1 + p.2) * F (p.1 + x'))) := by
      exact (hφ.comp (continuous_fst.comp continuous_fst)).mul
        ((hF.comp ((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst))).mul
          (hF.comp ((continuous_fst.comp continuous_fst).add continuous_snd)))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 h
  rw [intervalIntegral_swap hc1 hAB hh]
  refine intervalIntegral.integral_congr fun x _ => ?_
  -- swap `t` with `x'`
  have hc2 : Continuous (Function.uncurry fun (t x' : ℝ) => φ t * (F (t + x) * F (t + x'))) := by
    exact (hφ.comp continuous_fst).mul ((hF.comp (continuous_fst.add continuous_const)).mul
      (hF.comp (continuous_fst.add continuous_snd)))
  exact intervalIntegral_swap hc2 hAB hh

/-- The inner integral in lag form: `∫_A^B φ(t)F(t+x)F(t+x') dt = ∫_{A+x}^{B+x} φ(u−x)F(u)F(u+(x'−x)) du`. -/
lemma inner_lag {F φ : ℝ → ℝ} (A B x x' : ℝ) :
    ∫ t in A..B, φ t * (F (t + x) * F (t + x')) =
      ∫ u in (A + x)..(B + x), φ (u - x) * (F u * F (u + (x' - x))) := by
  rw [← intervalIntegral.integral_comp_add_right
    (fun u => φ (u - x) * (F u * F (u + (x' - x)))) x]
  congr 1; ext t
  simp only [add_sub_cancel_right]
  congr 3; ring

/-- **Sharp window ≤ weighted window**: for `φ ≥ 0` with `φ ≥ 1` on `[T, 2T]`,
`∫_{[T,2T]} I(t)² ≤ ∫_A^B φ(t) I(t)²`, `[T,2T] ⊆ [A,B]`. -/
theorem sk_le_weighted {F φ : ℝ → ℝ} (hF : Continuous F) (hφ : Continuous φ)
    (hφ0 : ∀ t, 0 ≤ φ t) {T A B h : ℝ} (hAT : A ≤ T) (hTB : 2 * T ≤ B) (hT : 0 ≤ T)
    (hφ1 : ∀ t ∈ Icc T (2 * T), 1 ≤ φ t) :
    ∫ t in Icc T (2 * T), (∫ u in t..t + h, F u) ^ 2 ≤
      ∫ t in A..B, φ t * (∫ u in t..t + h, F u) ^ 2 := by
  have hI : Continuous fun t => ∫ u in t..t + h, F u :=
    RamanujanTau.HafnerProportion.continuous_shortInt hF h
  have hg : Continuous fun t => φ t * (∫ u in t..t + h, F u) ^ 2 := hφ.mul (hI.pow 2)
  have hg0 : ∀ t, 0 ≤ φ t * (∫ u in t..t + h, F u) ^ 2 := fun t => mul_nonneg (hφ0 t) (sq_nonneg _)
  rw [RamanujanTau.HafnerProportion.setIcc_eq_interval (by linarith)]
  calc ∫ t in T..(2 * T), (∫ u in t..t + h, F u) ^ 2
      ≤ ∫ t in T..(2 * T), φ t * (∫ u in t..t + h, F u) ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) ((hI.pow 2).intervalIntegrable _ _)
          (hg.intervalIntegrable _ _) fun t ht => ?_
        have := hφ1 t ht
        have h2 := sq_nonneg (∫ u in t..t + h, F u)
        nlinarith
    _ ≤ ∫ t in A..B, φ t * (∫ u in t..t + h, F u) ^ 2 :=
        intervalIntegral.integral_mono_interval hAT (by linarith) hTB
          (Eventually.of_forall hg0) (hg.intervalIntegrable _ _)

/-- **(SK) in lag form**: the sharp-window Selberg integral is bounded by the
`(x, x')`-integrated weighted lag correlations of `F = Z·w`. -/
theorem sk_le_lag {F φ : ℝ → ℝ} (hF : Continuous F) (hφ : Continuous φ)
    (hφ0 : ∀ t, 0 ≤ φ t) {T A B h : ℝ} (hAT : A ≤ T) (hTB : 2 * T ≤ B) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (hφ1 : ∀ t ∈ Icc T (2 * T), 1 ≤ φ t) :
    ∫ t in Icc T (2 * T), (∫ u in t..t + h, F u) ^ 2 ≤
      ∫ x in (0:ℝ)..h, ∫ x' in (0:ℝ)..h,
        ∫ u in (A + x)..(B + x), φ (u - x) * (F u * F (u + (x' - x))) := by
  refine (sk_le_weighted hF hφ hφ0 hAT hTB hT hφ1).trans (le_of_eq ?_)
  rw [weighted_shortInt_sq hF hφ (by linarith) hh]
  simp_rw [inner_lag]

end RamanujanTau.SelbergKey
