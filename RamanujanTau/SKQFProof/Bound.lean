/-
# `SvStripHyp` and the fixed-`y` bound for the `SKQFHyp` (ii) integral (level 1)

`SvStripHyp c'` (named hypothesis; the remaining arithmetic input, see `docs/SKQF_PROOF.md`):
for every `y ≥ 2`, `v ↦ 𝒮(v)` continues holomorphically from `[−1,1]` to a neighbourhood of the
strip `R = {|Re z| ≤ 1, −δ₀ ≤ Im z ≤ 0}` (that is, `Re s ∈ [1 − δ₀, 1]` for `s = 1 − iz`), and there

    |𝒮(z)| ≤ C (1 + |Re z| log y)² y^{c'|Im z|} / log y.

On the real axis this is a `v`-uniform version of `Q⁰(y) ≪ 1/log y` (`QFHyp`, proved under Deligne),
with polynomial loss `(1 + |v| log y)²` in the twist.

`int_bound`: with `ℓ = log y`, `M₀ = C/ℓ`, `M₁ = C(1+hℓ)²/ℓ`, `b = L − c'ℓ > 0`, `0 < h ≤ 1`, `L ≥ 0`,

    |∫_{−h}^{h}(h−|v|) Re 𝒜(v,L) dv| ≤ 2|γ_R|h²M₁ + 4|r₀|M₀ h log(1+hL)
                                       + |r₀|(4h(h+δ₀)M₁e^{−bδ₀}/δ₀ + 16M₁/(hb²) + 4M₀/b).
-/
import RamanujanTau.SKQFProof.Real
import RamanujanTau.SKQFProof.Contour

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

open Complex MeasureTheory intervalIntegral Set
open scoped Interval
open RamanujanTau.SelbergKey

/-- The closed strip `|Re z| ≤ 1`, `−δ₀ ≤ Im z ≤ 0`. -/
def stripR (δ₀ : ℝ) : Set ℂ := {z | |z.re| ≤ 1 ∧ -δ₀ ≤ z.im ∧ z.im ≤ 0}

/-- **The strip hypothesis** (holomorphic continuation of `𝒮` below the real axis, with a
`v`-uniform `1/log y` bound). -/
def SvStripHyp (c' : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ y : ℕ, 2 ≤ y → ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧
    stripR δ₀ ⊆ U ∧ DifferentiableOn ℂ F U ∧ (∀ v : ℝ, |v| ≤ 1 → F v = Sv y v) ∧
    ∀ z ∈ stripR δ₀, ‖F z‖ ≤
      C * (1 + |z.re| * Real.log y) ^ 2 * Real.exp (c' * |z.im| * Real.log y) / Real.log y

lemma rect_sub_strip {h δ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) :
    [[-h, h]] ×ℂ [[-δ, 0]] ⊆ stripR δ := by
  intro z hz
  rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hz
  exact ⟨abs_le.2 ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2.1, hz.2.2⟩

theorem int_bound {c' C δ₀ : ℝ} (hc' : 0 ≤ c') (hC : 0 ≤ C) (hδ₀ : 0 < δ₀) {y : ℕ} (hy : 2 ≤ y)
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hRU : stripR δ₀ ⊆ U) (hFd : DifferentiableOn ℂ F U)
    (hFS : ∀ v : ℝ, |v| ≤ 1 → F v = Sv y v)
    (hFb : ∀ z ∈ stripR δ₀, ‖F z‖ ≤
      C * (1 + |z.re| * Real.log y) ^ 2 * Real.exp (c' * |z.im| * Real.log y) / Real.log y)
    {h L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 ≤ L) (hb : 0 < L - c' * Real.log y) :
    |∫ v in (-h)..h, (h - |v|) * (Av y v L).re| ≤
      2 * |GoodSecondTerm.gammaD| * h ^ 2 * (C * (1 + h * Real.log y) ^ 2 / Real.log y) +
      4 * |HafnerBridge.r0| * (C / Real.log y) * h * Real.log (1 + h * L) +
      |HafnerBridge.r0| * (4 * h * (h + δ₀) * (C * (1 + h * Real.log y) ^ 2 / Real.log y) *
          Real.exp (-((L - c' * Real.log y) * δ₀)) / δ₀ +
        16 * (C * (1 + h * Real.log y) ^ 2 / Real.log y) / (h * (L - c' * Real.log y) ^ 2) +
        4 * (C / Real.log y) / (L - c' * Real.log y)) := by
  set ℓ := Real.log y with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  set M₀ := C / ℓ with hM₀
  set M₁ := C * (1 + h * ℓ) ^ 2 / ℓ with hM₁
  set a := c' * ℓ with ha
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hM : M₀ ≤ M₁ := by
    rw [hM₀, hM₁]
    have h1 : (1:ℝ) ≤ (1 + h * ℓ) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    exact div_le_div_of_nonneg_right (by nlinarith) hℓ0.le
  have hrect := rect_sub_strip hh hh1 hδ₀
  -- bounds on the rectangle
  have hbd : ∀ z ∈ [[-h, h]] ×ℂ [[-δ₀, 0]], ‖F z‖ ≤ M₁ * Real.exp (-(a * z.im)) := by
    intro z hz
    have hzR := hrect hz
    have h1 := hFb z hzR
    have hre : |z.re| ≤ h := by
      have := (mem_reProdIm.1 hz).1; rw [uIcc_of_le (by linarith)] at this; exact abs_le.2 this
    have him : |z.im| = -z.im := abs_of_nonpos hzR.2.2
    refine h1.trans ?_
    rw [hM₁, him, ha]
    have : (1 + |z.re| * ℓ) ^ 2 ≤ (1 + h * ℓ) ^ 2 := by
      have : 0 ≤ |z.re| * ℓ := by positivity
      gcongr
    calc C * (1 + |z.re| * ℓ) ^ 2 * Real.exp (c' * -z.im * ℓ) / ℓ
        ≤ C * (1 + h * ℓ) ^ 2 * Real.exp (c' * -z.im * ℓ) / ℓ := by gcongr
      _ = C * (1 + h * ℓ) ^ 2 / ℓ * Real.exp (-(c' * ℓ * z.im)) := by ring_nf
  have hbd0 : ∀ t : ℝ, -δ₀ ≤ t → t ≤ 0 → ‖F (t * I)‖ ≤ M₀ * Real.exp (-(a * t)) := by
    intro t ht1 ht2
    have hz : (t : ℂ) * I ∈ stripR δ₀ := ⟨by simp, by simpa using ht1, by simpa using ht2⟩
    refine (hFb _ hz).trans (le_of_eq ?_)
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, abs_zero,
      zero_mul, add_zero, one_pow, mul_im]
    rw [hM₀, ha, abs_of_nonpos ht2]; ring_nf
  have hF0 : ‖F 0‖ ≤ M₀ := by
    have hz : (0 : ℂ) ∈ stripR δ₀ := ⟨by simp, by simp; linarith, by simp⟩
    refine (hFb 0 hz).trans (le_of_eq ?_)
    simp [hM₀]
  have hab : 0 < L - a := hb
  have hcont := contour_bound F U hU hFd hh hδ₀ hab (by positivity) (hrect.trans hRU) hM₀0 hM hbd hbd0 hF0
  -- F(0) is real
  have hF0eq : F 0 = Sv y 0 := by have := hFS 0 (by simp); simpa using this
  set F0 : ℝ := (F 0).re with hF0def
  have hF0real : F 0 = (F0 : ℂ) := by
    apply Complex.ext <;> simp [hF0def, hF0eq, Sv_zero_im]
  have hF0abs : |F0| ≤ M₀ := by
    have := abs_re_le_norm (F 0); rw [← hF0def] at this; exact this.trans hF0
  -- continuity on the real segment
  have hseg : ∀ v ∈ uIcc (-h) h, (v : ℂ) ∈ U := by
    intro v hv
    apply hRU
    rw [uIcc_of_le (by linarith)] at hv
    refine ⟨?_, by simp; linarith, by simp⟩
    simp only [ofReal_re]; exact abs_le.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hFc : ContinuousOn (fun v : ℝ => F v) (uIcc (-h) h) :=
    (hFd.continuousOn).comp (by fun_prop) hseg
  have h0U : (0 : ℂ) ∈ U := hRU ⟨by simp, by simp; linarith, by simp⟩
  have hGd : DifferentiableOn ℂ (dslope F 0) U := (differentiableOn_dslope (hU.mem_nhds h0U)).2 hFd
  have hGc : ContinuousOn (fun v : ℝ => dslope F 0 v) (uIcc (-h) h) :=
    (hGd.continuousOn).comp (by fun_prop) hseg
  -- the three pieces
  set f1 : ℝ → ℝ := fun v => GoodSecondTerm.gammaD *
    ((h - |v|) * (cexp (-((v * L : ℝ) : ℂ) * I) * F v).re) with hf1
  set f2 : ℝ → ℝ := fun v => HafnerBridge.r0 * F0 * ((h - |v|) * (L * Real.sinc (v * L))) with hf2
  set f3 : ℝ → ℝ := fun v => HafnerBridge.r0 *
    ((((h - |v|) : ℝ) : ℂ) * (cexp (-((v * L : ℝ) : ℂ) * I) * dslope F 0 v)).im with hf3
  have hc3 : ContinuousOn (fun v : ℝ => (((h - |v|) : ℝ) : ℂ) *
      (cexp (-((v * L : ℝ) : ℂ) * I) * dslope F 0 v)) (uIcc (-h) h) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) hGc)
  have hi1 : IntervalIntegrable f1 volume (-h) h := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (ContinuousOn.mul (by fun_prop)
      (Complex.continuous_re.comp_continuousOn (ContinuousOn.mul (by fun_prop) hFc)))
  have hi2 : IntervalIntegrable f2 volume (-h) h :=
    (by fun_prop : Continuous fun v : ℝ => HafnerBridge.r0 * F0 * ((h - |v|) * (L * Real.sinc (v * L))))
      |>.intervalIntegrable _ _
  have hi3c : IntervalIntegrable (fun v : ℝ => (((h - |v|) : ℝ) : ℂ) *
      (cexp (-((v * L : ℝ) : ℂ) * I) * dslope F 0 v)) volume (-h) h := hc3.intervalIntegrable
  have hi3 : IntervalIntegrable f3 volume (-h) h :=
    (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hc3)).intervalIntegrable
  -- a.e. identity of the integrand
  have hae : ∀ᵐ v : ℝ ∂volume, v ∈ Ι (-h) h → (h - |v|) * (Av y v L).re = f1 v + f2 v - f3 v := by
    have hne : ∀ᵐ v : ℝ ∂volume, v ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hne] with v hv hvI
    have hvI' : |v| ≤ 1 := by
      rw [uIoc_of_le (by linarith)] at hvI
      exact abs_le.2 ⟨by linarith [hvI.1], by linarith [hvI.2]⟩
    have hS : Sv y v = (F0 : ℂ) + (v : ℂ) * dslope F 0 v := by
      rw [← hFS v hvI', ← hF0real, mul_dslope]; ring
    rw [re_Av_eq y hv L F0 (dslope F 0 v) hS, ← hFS v hvI']
    simp only [hf1, hf2, hf3]
    have : ((((h - |v|) : ℝ) : ℂ) * (cexp (-((v * L : ℝ) : ℂ) * I) * dslope F 0 v)).im =
        (h - |v|) * (cexp (-((v * L : ℝ) : ℂ) * I) * dslope F 0 v).im := by
      rw [Complex.im_ofReal_mul]
    rw [this]; ring
  rw [integral_congr_ae hae, intervalIntegral.integral_sub (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2]
  have hhh : -h ≤ h := by linarith
  -- piece 1
  have b1 : |∫ v in (-h)..h, f1 v| ≤ 2 * |GoodSecondTerm.gammaD| * h ^ 2 * M₁ := by
    have := norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := |GoodSecondTerm.gammaD| * (h * M₁))
      (f := f1) (fun v hv => by
        rw [uIoc_of_le hhh] at hv
        have hvI' : |v| ≤ h := abs_le.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩
        have hv1 : |v| ≤ 1 := hvI'.trans hh1
        have hz : (v : ℂ) ∈ [[-h, h]] ×ℂ [[-δ₀, 0]] := by
          rw [mem_reProdIm]; simp only [ofReal_re, ofReal_im]
          rw [uIcc_of_le hhh, uIcc_of_le (by linarith)]
          exact ⟨⟨by linarith [hv.1], hv.2⟩, by linarith, le_refl _⟩
        have hFv := hbd _ hz
        simp only [ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one] at hFv
        simp only [hf1, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (by linarith : 0 ≤ h - |v|)]
        have hE : ‖cexp (-((v * L : ℝ) : ℂ) * I) * F v‖ ≤ M₁ := by
          rw [norm_mul, show (-((v * L : ℝ) : ℂ) * I) = (((-(v * L)) : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, one_mul]
          exact hFv
        have hM1 : 0 ≤ M₁ := hM₀0.trans hM
        calc (h - |v|) * |(cexp (-((v * L : ℝ) : ℂ) * I) * F v).re|
            ≤ h * M₁ := mul_le_mul (by linarith [abs_nonneg v]) ((abs_re_le_norm _).trans hE)
              (abs_nonneg _) hh.le)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [show h - -h = 2 * h by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * h)]; ring
  -- piece 2
  have b2 : |∫ v in (-h)..h, f2 v| ≤ 4 * |HafnerBridge.r0| * M₀ * h * Real.log (1 + h * L) := by
    have hg : Continuous fun v : ℝ => |HafnerBridge.r0| * M₀ * h * (2 * (L / (1 + |v| * L))) := by
      refine continuous_const.mul (continuous_const.mul (Continuous.div continuous_const (by fun_prop)
        fun v => ?_))
      have := abs_nonneg v; positivity
    have := norm_integral_le_of_norm_le (f := f2)
      (g := fun v : ℝ => |HafnerBridge.r0| * M₀ * h * (2 * (L / (1 + |v| * L)))) hhh
      (Filter.Eventually.of_forall fun v hv => by
        have hvI' : |v| ≤ h := abs_le.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩
        simp only [hf2, Real.norm_eq_abs, abs_mul]
        have hs : |L| * |Real.sinc (v * L)| ≤ 2 * (L / (1 + |v| * L)) := by
          have := abs_sinc_le (v * L)
          rw [abs_mul, abs_of_nonneg hL] at this
          rw [abs_of_nonneg hL]
          calc L * |Real.sinc (v * L)| ≤ L * (2 / (1 + |v| * L)) := by gcongr
            _ = 2 * (L / (1 + |v| * L)) := by ring
        rw [abs_of_nonneg (by linarith : 0 ≤ h - |v|)]
        have hhv : h - |v| ≤ h := by linarith [abs_nonneg v]
        calc |HafnerBridge.r0| * |F0| * ((h - |v|) * (|L| * |Real.sinc (v * L)|))
            ≤ |HafnerBridge.r0| * M₀ * (h * (2 * (L / (1 + |v| * L)))) := by
              have h0 : 0 ≤ (h - |v|) * (|L| * |Real.sinc (v * L)|) := by
                have := abs_nonneg v; have : 0 ≤ h - |v| := by linarith
                positivity
              have h1 : (h - |v|) * (|L| * |Real.sinc (v * L)|) ≤ h * (2 * (L / (1 + |v| * L))) :=
                mul_le_mul hhv hs (by positivity) hh.le
              have h2 : |HafnerBridge.r0| * |F0| ≤ |HafnerBridge.r0| * M₀ :=
                mul_le_mul_of_nonneg_left hF0abs (abs_nonneg _)
              exact mul_le_mul h2 h1 h0 (by positivity)
          _ = |HafnerBridge.r0| * M₀ * h * (2 * (L / (1 + |v| * L))) := by ring)
      (hg.intervalIntegrable (μ := volume) _ _)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have := integral_inv_one_add_le hh.le hL
    have hpos : 0 ≤ |HafnerBridge.r0| * M₀ * h := by positivity
    nlinarith
  -- piece 3
  have b3 : |∫ v in (-h)..h, f3 v| ≤ |HafnerBridge.r0| *
      (4 * h * (h + δ₀) * M₁ * Real.exp (-((L - a) * δ₀)) / δ₀ + 16 * M₁ / (h * (L - a) ^ 2) +
        4 * M₀ / (L - a)) := by
    simp only [hf3]
    rw [intervalIntegral.integral_const_mul, abs_mul]
    gcongr
    have e := intervalIntegral.intervalIntegral_im hi3c
    simp only [RCLike.im_to_complex] at e
    rw [e]
    exact (abs_im_le_norm _).trans hcont
  calc |(∫ v in (-h)..h, f1 v) + (∫ v in (-h)..h, f2 v) - ∫ v in (-h)..h, f3 v|
      ≤ |∫ v in (-h)..h, f1 v| + |∫ v in (-h)..h, f2 v| + |∫ v in (-h)..h, f3 v| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        rw [hM₁, hM₀, ha] at *
        gcongr

end RamanujanTau.SKQFProof
