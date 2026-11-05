/-
# The triangle function and its Fourier transform

`tri h v = max 0 (h − |v|)`.  Its Fourier transform (Mathlib normalisation
`𝓕 f ξ = ∫ e^{−2πivξ} f(v) dv`) is the real, nonnegative Fejér kernel

    𝓕 tri (ξ) = 2 ∫₀ʰ cos(2πξv)(h − v) dv = 2(1 − cos 2πξh)/(2πξ)²,

which is integrable; Fourier inversion then writes `tri h v = ∫ 𝓕 tri (ξ) e^{2πiξv} dξ`,
and `∫ 𝓕 tri = tri h 0 = h`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.HardyCount

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Real FourierTransform ComplexConjugate

/-- The triangle function of half-width `h`. -/
noncomputable def tri (h v : ℝ) : ℝ := max 0 (h - |v|)

/-- The triangle as a complex-valued function. -/
noncomputable def triC (h : ℝ) (v : ℝ) : ℂ := (tri h v : ℂ)

lemma tri_nonneg (h v : ℝ) : 0 ≤ tri h v := le_max_left _ _

lemma tri_le (h v : ℝ) (hh : 0 ≤ h) : tri h v ≤ h := by
  unfold tri; exact max_le hh (by linarith [abs_nonneg v])

lemma tri_of_abs_le {h v : ℝ} (hv : |v| ≤ h) : tri h v = h - |v| := by
  unfold tri; exact max_eq_right (by linarith)

lemma tri_of_le_abs {h v : ℝ} (hv : h ≤ |v|) : tri h v = 0 := by
  unfold tri; exact max_eq_left (by linarith)

lemma continuous_tri (h : ℝ) : Continuous (tri h) := by
  unfold tri; fun_prop

lemma continuous_triC (h : ℝ) : Continuous (triC h) := by
  unfold triC; exact Complex.continuous_ofReal.comp (continuous_tri h)

lemma hasCompactSupport_triC (h : ℝ) : HasCompactSupport (triC h) := by
  refine HasCompactSupport.intro (K := Icc (-|h|) |h|) isCompact_Icc fun v hv => ?_
  have : |h| < |v| := by
    by_contra hc
    exact hv (abs_le.mp (not_lt.mp hc))
  unfold triC
  rw [tri_of_le_abs (by linarith [le_abs_self h])]; simp

lemma integrable_triC (h : ℝ) : Integrable (triC h) :=
  (continuous_triC h).integrable_of_hasCompactSupport (hasCompactSupport_triC h)

lemma integrable_tri (h : ℝ) : Integrable (tri h) := by
  have := (integrable_triC h).re
  simpa [triC] using this

/-- `𝓕 tri` as a real function: `2 ∫₀ʰ cos(2πξv)(h−v) dv`. -/
noncomputable def triHat (h ξ : ℝ) : ℝ := 2 * ∫ v in (0 : ℝ)..h, Real.cos (2 * π * ξ * v) * (h - v)

/-- Closed form of `triHat` for `ξ ≠ 0`. -/
lemma triHat_eq {h ξ : ℝ} (hξ : ξ ≠ 0) :
    triHat h ξ = 2 * (1 - Real.cos (2 * π * ξ * h)) / (2 * π * ξ) ^ 2 := by
  set c : ℝ := 2 * π * ξ with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact mul_ne_zero (by positivity) hξ
  have hF : ∀ v : ℝ, HasDerivAt (fun v => (h - v) * Real.sin (c * v) / c - Real.cos (c * v) / c ^ 2)
      (Real.cos (c * v) * (h - v)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => c * v) c v := by
      simpa using (hasDerivAt_id v).const_mul c
    have hs := (Real.hasDerivAt_sin (c * v)).comp v h1
    have hco := (Real.hasDerivAt_cos (c * v)).comp v h1
    have hl : HasDerivAt (fun v : ℝ => h - v) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub h
    have := ((hl.mul hs).div_const c).sub (hco.div_const (c ^ 2))
    convert this using 1
    simp only [Function.comp_apply]
    field_simp
    ring
  have hint := integral_eq_sub_of_hasDerivAt (fun v _ => hF v)
    ((by fun_prop : Continuous fun v : ℝ => Real.cos (c * v) * (h - v)).intervalIntegrable 0 h)
  unfold triHat
  rw [← hc]
  have e : ∀ v : ℝ, Real.cos (c * v) * (h - v) = Real.cos (c * v) * (h - v) := fun _ => rfl
  rw [hint]
  simp only [sub_self, zero_mul, zero_div, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

lemma triHat_nonneg {h ξ : ℝ} (hh : 0 ≤ h) : 0 ≤ triHat h ξ := by
  rcases eq_or_ne ξ 0 with hξ | hξ
  · unfold triHat
    refine mul_nonneg (by norm_num) (integral_nonneg hh fun v hv => ?_)
    rw [hξ]; simp only [mul_zero, zero_mul, Real.cos_zero, one_mul]
    linarith [hv.2]
  · rw [triHat_eq hξ]
    have := Real.cos_le_one (2 * π * ξ * h)
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)

lemma triHat_le_const {h ξ : ℝ} (hh : 0 ≤ h) : triHat h ξ ≤ 2 * h ^ 2 := by
  unfold triHat
  have : ‖∫ v in (0 : ℝ)..h, Real.cos (2 * π * ξ * v) * (h - v)‖ ≤ h * |h - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
    rw [uIoc_of_le hh] at hv
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos (2 * π * ξ * v)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |h - v| ≤ h := by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
    calc |Real.cos (2 * π * ξ * v)| * |h - v| ≤ 1 * h := by gcongr
      _ = h := one_mul h
  rw [sub_zero, abs_of_nonneg hh, Real.norm_eq_abs] at this
  have := (le_abs_self _).trans this
  nlinarith

lemma triHat_le_inv {h ξ : ℝ} (hξ : 1 ≤ |ξ|) : triHat h ξ ≤ 1 / ξ ^ 2 := by
  have hξ0 : ξ ≠ 0 := by intro h0; rw [h0, abs_zero] at hξ; linarith
  rw [triHat_eq hξ0]
  have h1 : 1 - Real.cos (2 * π * ξ * h) ≤ 2 := by linarith [Real.neg_one_le_cos (2 * π * ξ * h)]
  have hpi : 4 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hξ2 : 0 < ξ ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hξ2, mul_pow]
  nlinarith

lemma triHat_le {h ξ : ℝ} (hh : 0 ≤ h) : triHat h ξ ≤ (4 * h ^ 2 + 2) * (1 + ξ ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rcases le_or_gt 1 |ξ| with hξ | hξ
  · have h1 := triHat_le_inv (h := h) hξ
    have hξ2 : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    have h0 := triHat_nonneg (h := h) (ξ := ξ) hh
    have : triHat h ξ * ξ ^ 2 ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  · have h1 := triHat_le_const (h := h) (ξ := ξ) hh
    have h0 := triHat_nonneg (h := h) (ξ := ξ) hh
    have hξ2 : ξ ^ 2 ≤ 1 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    nlinarith

/-- **The Fourier transform of the triangle.** -/
theorem fourier_triC {h : ℝ} (hh : 0 ≤ h) (ξ : ℝ) : 𝓕 (triC h) ξ = (triHat h ξ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set g : ℝ → ℂ := fun v => cexp (↑(-2 * π * v * ξ) * I) * ((h - |v|) : ℝ) with hg
  have hsupp : ∀ v, v ∉ Icc (-h) h → cexp (↑(-2 * π * v * ξ) * I) • triC h v = 0 := by
    intro v hv
    have : h < |v| := by
      simp only [mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hv
    simp [triC, tri_of_le_abs this.le]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ v ∈ uIcc (-h) h, cexp (↑(-2 * π * v * ξ) * I) • triC h v = g v := by
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    have : |v| ≤ h := abs_le.mpr ⟨hv.1, hv.2⟩
    simp [triC, tri_of_abs_le this, hg]
  rw [intervalIntegral.integral_congr hcongr]
  have hgc : Continuous g := by rw [hg]; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hgc.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _)]
  -- reflect the left half
  have hleft : (∫ v in (-h)..0, g v) = ∫ v in (0 : ℝ)..h, g (-v) := by
    rw [intervalIntegral.integral_comp_neg]; simp
  have hgn : Continuous fun v => g (-v) := hgc.comp continuous_neg
  rw [hleft, ← intervalIntegral.integral_add (hgn.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _)]
  have hcongr2 : ∀ v ∈ uIcc 0 h, g (-v) + g v =
      ((2 * (Real.cos (2 * π * ξ * v) * (h - v)) : ℝ) : ℂ) := by
    intro v hv
    rw [uIcc_of_le hh] at hv
    have hv0 : |v| = v := abs_of_nonneg hv.1
    have hnv : |-v| = v := by rw [abs_neg, hv0]
    simp only [hg, hnv, hv0]
    have e1 : cexp (↑(-2 * π * -v * ξ) * I) + cexp (↑(-2 * π * v * ξ) * I) =
        ((2 * Real.cos (2 * π * ξ * v) : ℝ) : ℂ) := by
      rw [show ((-2 * π * -v * ξ : ℝ) : ℂ) * I = ((2 * π * ξ * v : ℝ) : ℂ) * I by push_cast; ring,
        show ((-2 * π * v * ξ : ℝ) : ℂ) * I = -(((2 * π * ξ * v : ℝ) : ℂ) * I) by push_cast; ring]
      rw [show ((2 * Real.cos (2 * π * ξ * v) : ℝ) : ℂ) =
          2 * Complex.cos (((2 * π * ξ * v : ℝ)) : ℂ) by push_cast; ring, Complex.two_cos]
      push_cast; ring_nf
    rw [← add_mul, e1]; push_cast; ring
  rw [intervalIntegral.integral_congr hcongr2, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul]
  rfl

lemma integrable_triHat {h : ℝ} (hh : 0 ≤ h) : Integrable (triHat h) := by
  have hc : Continuous fun ξ => triHat h ξ := by
    have : (fun ξ => triHat h ξ) = fun ξ => (𝓕 (triC h) ξ).re := by
      funext ξ; rw [fourier_triC hh]; simp
    rw [this]
    exact Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ (integrable_triC h))
  refine (integrable_inv_one_add_sq.const_mul (4 * h ^ 2 + 2)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (triHat_nonneg hh)]
  exact triHat_le hh

lemma integrable_fourier_triC {h : ℝ} (hh : 0 ≤ h) : Integrable (𝓕 (triC h)) := by
  have : 𝓕 (triC h) = fun ξ => ((triHat h ξ : ℝ) : ℂ) := funext (fourier_triC hh)
  rw [this]; exact (integrable_triHat hh).ofReal

/-- **Fourier inversion for the triangle**: `tri h v = ∫ triHat h ξ · e^{2πiξv} dξ`. -/
theorem tri_inversion {h : ℝ} (hh : 0 ≤ h) (v : ℝ) :
    (tri h v : ℂ) = ∫ ξ : ℝ, cexp (↑(2 * π * ξ * v) * I) * (triHat h ξ : ℂ) := by
  have := congrFun ((continuous_triC h).fourierInv_fourier_eq (integrable_triC h)
    (integrable_fourier_triC hh)) v
  rw [Real.fourierInv_eq'] at this
  rw [← show triC h v = (tri h v : ℂ) from rfl, ← this]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [fourier_triC hh, smul_eq_mul, RCLike.inner_apply', conj_trivial]
  congr 3
  ring_nf

/-- `∫ triHat h = h`. -/
theorem integral_triHat {h : ℝ} (hh : 0 ≤ h) : ∫ ξ : ℝ, triHat h ξ = h := by
  have h0 := tri_inversion hh 0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at h0
  have e : (∫ ξ : ℝ, ((triHat h ξ : ℝ) : ℂ)) = ((∫ ξ, triHat h ξ : ℝ) : ℂ) := integral_ofReal
  rw [e, tri_of_abs_le (by simpa using hh), abs_zero, sub_zero] at h0
  exact_mod_cast h0.symm

end RamanujanTau.HardyCount
