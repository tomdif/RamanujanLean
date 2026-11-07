/-
# The contour lemma behind `SKQFHyp` (ii) (level 1)

For `F` holomorphic near the rectangle `R = [−h, h] × [−δ, 0]` and `G = dslope F 0`
(`G(z) = (F(z) − F(0))/z`), the Fejér-weighted oscillatory integral

    A = ∫_{−h}^{h} (h − |x|) e^{−ixL} G(x) dx

is moved to the lower half-plane, where `e^{−izL}` decays: Cauchy on the two rectangles
`[0,h] × [−δ,0]` (integrand `(h − z)e^{−izL}G`) and `[−h,0] × [−δ,0]` (integrand `(h + z)e^{−izL}G`).
On the common vertical side `Re z = 0` the two integrands combine to `2z e^{−izL}G = 2e^{−izL}(F(z) − F(0))`
(no `1/z`), on the outer sides the weight `h ∓ z = ∓iy` vanishes at the real axis, and the
bottom carries `e^{−δL}`.  Result (`contour_bound`), with `b = L − a > 0`:

    ‖A‖ ≤ 4h(h+δ)M₁e^{−bδ}/δ + 16M₁/(h b²) + 4M₀/b

if `‖F z‖ ≤ M₁e^{a|Im z|}` on `R`, `‖F(iy)‖ ≤ M₀e^{a|y|}`, `‖F 0‖ ≤ M₀ ≤ M₁`.
-/
import RamanujanTau.SKQFProof.Elem

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

open Complex MeasureTheory intervalIntegral Set
open scoped Interval

lemma norm_cexp_rot (z : ℂ) (L : ℝ) : ‖cexp (-(z * L) * I)‖ = Real.exp (L * z.im) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring

lemma mul_dslope (F : ℂ → ℂ) (z : ℂ) : z * dslope F 0 z = F z - F 0 := by
  have := sub_smul_dslope F 0 z; simpa using this

lemma norm_dslope_le (F : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖dslope F 0 z‖ ≤ (‖F z‖ + ‖F 0‖) / ‖z‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [le_div_iff₀ hz', mul_comm, ← norm_mul, mul_dslope]
  exact norm_sub_le _ _

lemma mem_rect {h δ x y : ℝ} (hx : x ∈ uIcc (-h) h) (hy : y ∈ uIcc (-δ) 0) :
    (x : ℂ) + y * I ∈ [[-h, h]] ×ℂ [[-δ, 0]] := by
  rw [mem_reProdIm]; simp [hx, hy]

theorem contour_bound (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hFd : DifferentiableOn ℂ F U)
    {h δ L a M₀ M₁ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hb : 0 < L - a) (ha : 0 ≤ a)
    (hR : [[-h, h]] ×ℂ [[-δ, 0]] ⊆ U) (hM₀ : 0 ≤ M₀) (hM : M₀ ≤ M₁)
    (hbd : ∀ z ∈ [[-h, h]] ×ℂ [[-δ, 0]], ‖F z‖ ≤ M₁ * Real.exp (-(a * z.im)))
    (hbd0 : ∀ y : ℝ, -δ ≤ y → y ≤ 0 → ‖F (y * I)‖ ≤ M₀ * Real.exp (-(a * y)))
    (hF0 : ‖F 0‖ ≤ M₀) :
    ‖∫ x in (-h)..h, (((h - |x|) : ℝ) : ℂ) * (cexp (-((x * L : ℝ) : ℂ) * I) * dslope F 0 x)‖ ≤
      4 * h * (h + δ) * M₁ * Real.exp (-((L - a) * δ)) / δ + 16 * M₁ / (h * (L - a) ^ 2) +
        4 * M₀ / (L - a) := by
  set b := L - a with hbdef
  set G := dslope F 0 with hG
  set R := [[-h, h]] ×ℂ [[-δ, 0]] with hRdef
  have h0R : (0 : ℂ) ∈ R := by
    have := mem_rect (h := h) (δ := δ) (x := 0) (y := 0) (by simp [uIcc_of_le, hh.le])
      (by simp [uIcc_of_le, hδ.le]); simpa using this
  have hGd : DifferentiableOn ℂ G U := (differentiableOn_dslope (hU.mem_nhds (hR h0R))).2 hFd
  set fp : ℂ → ℂ := fun z => ((h : ℂ) - z) * (cexp (-(z * L) * I) * G z) with hfp
  set fm : ℂ → ℂ := fun z => ((h : ℂ) + z) * (cexp (-(z * L) * I) * G z) with hfm
  have hfpd : DifferentiableOn ℂ fp U := by
    refine (differentiableOn_const _ |>.sub differentiableOn_id).mul ?_
    exact (((differentiableOn_id.mul (differentiableOn_const _)).neg.mul
      (differentiableOn_const _)).cexp).mul hGd
  have hfmd : DifferentiableOn ℂ fm U := by
    refine (differentiableOn_const _ |>.add differentiableOn_id).mul ?_
    exact (((differentiableOn_id.mul (differentiableOn_const _)).neg.mul
      (differentiableOn_const _)).cexp).mul hGd
  -- rectangles
  have hsub1 : [[(0:ℝ), h]] ×ℂ [[-δ, 0]] ⊆ U := fun z hz => hR (by
    rw [mem_reProdIm] at hz ⊢
    refine ⟨?_, hz.2⟩
    have := hz.1; rw [uIcc_of_le hh.le] at this; rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [this.1], this.2⟩)
  have hsub2 : [[-h, (0:ℝ)]] ×ℂ [[-δ, 0]] ⊆ U := fun z hz => hR (by
    rw [mem_reProdIm] at hz ⊢
    refine ⟨?_, hz.2⟩
    have := hz.1; rw [uIcc_of_le (by linarith)] at this; rw [uIcc_of_le (by linarith)]
    exact ⟨this.1, by linarith [this.2]⟩)
  have r1 := integral_boundary_rect_eq_zero_of_differentiableOn fp ⟨0, -δ⟩ ⟨h, 0⟩
    (hfpd.mono (by simpa using hsub1))
  have r2 := integral_boundary_rect_eq_zero_of_differentiableOn fm ⟨-h, -δ⟩ ⟨0, 0⟩
    (hfmd.mono (by simpa using hsub2))
  simp only [ofReal_zero, zero_mul, add_zero, zero_add, smul_eq_mul, ofReal_neg] at r1 r2
  -- continuity facts
  have hGc : ContinuousOn G R := (hGd.mono hR).continuousOn
  have hFc : ContinuousOn F R := (hFd.mono hR).continuousOn
  -- the real-axis integral, split
  have hreal_cont : ContinuousOn (fun x : ℝ => (((h - |x|) : ℝ) : ℂ) *
      (cexp (-((x * L : ℝ) : ℂ) * I) * G x)) (uIcc (-h) h) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_)
    refine hGc.comp (by fun_prop) fun x hx => ?_
    have := mem_rect (δ := δ) (y := 0) hx (by simp [uIcc_of_le, hδ.le]); simpa using this
  have hii : ∀ c d : ℝ, c ∈ uIcc (-h) h → d ∈ uIcc (-h) h →
      IntervalIntegrable (fun x : ℝ => (((h - |x|) : ℝ) : ℂ) *
        (cexp (-((x * L : ℝ) : ℂ) * I) * G x)) volume c d := fun c d hc hd =>
    (hreal_cont.mono (uIcc_subset_uIcc hc hd)).intervalIntegrable
  have hmem0 : (0:ℝ) ∈ uIcc (-h) h := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hmemh : h ∈ uIcc (-h) h := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hmemmh : -h ∈ uIcc (-h) h := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  rw [← integral_add_adjacent_intervals (hii _ _ hmemmh hmem0) (hii _ _ hmem0 hmemh)]
  have e1 : ∫ x in (0:ℝ)..h, (((h - |x|) : ℝ) : ℂ) * (cexp (-((x * L : ℝ) : ℂ) * I) * G x) =
      ∫ x in (0:ℝ)..h, fp x := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le hh.le] at hx
    simp only [hfp, abs_of_nonneg hx.1]; push_cast; ring
  have e2 : ∫ x in (-h)..0, (((h - |x|) : ℝ) : ℂ) * (cexp (-((x * L : ℝ) : ℂ) * I) * G x) =
      ∫ x in (-h)..0, fm x := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    simp only [hfm, abs_of_nonpos hx.2]; push_cast; ring
  rw [e1, e2]
  -- the pieces
  set Bp := ∫ x in (0:ℝ)..h, fp (x + -(δ : ℂ) * I) with hBp
  set Bm := ∫ x in (-h)..0, fm (x + -(δ : ℂ) * I) with hBm
  set Sp := ∫ y in (-δ)..0, fp (h + y * I) with hSp
  set Sm := ∫ y in (-δ)..0, fm (-(h : ℂ) + y * I) with hSm
  set Mp := ∫ y in (-δ)..0, fp (y * I) with hMp
  set Mm := ∫ y in (-δ)..0, fm (y * I) with hMm
  have hp : ∫ x in (0:ℝ)..h, fp x = Bp + I * Sp - I * Mp := by
    linear_combination -r1
  have hm : ∫ x in (-h)..0, fm x = Bm + I * Mm - I * Sm := by
    linear_combination -r2
  rw [hm, hp]
  have hvert_cont : ∀ (c : ℝ), c ∈ uIcc (-h) h → ∀ f : ℂ → ℂ, ContinuousOn f R →
      IntervalIntegrable (fun y : ℝ => f (c + y * I)) volume (-δ) 0 := by
    intro c hc f hf
    refine (hf.comp (by fun_prop) fun y hy => mem_rect hc hy).intervalIntegrable
  have hfpc : ContinuousOn fp R := (hfpd.mono hR).continuousOn
  have hfmc : ContinuousOn fm R := (hfmd.mono hR).continuousOn
  have hMid : Mm - Mp = ∫ y in (-δ)..0, (fm (y * I) - fp (y * I)) := by
    rw [intervalIntegral.integral_sub]
    · have := hvert_cont 0 hmem0 fm hfmc; simpa using this
    · have := hvert_cont 0 hmem0 fp hfpc; simpa using this
  have hsplit : Bm + I * Mm - I * Sm + (Bp + I * Sp - I * Mp) =
      Bm + Bp + I * Sp - I * Sm + I * (Mm - Mp) := by ring
  rw [hsplit, hMid]
  -- pointwise bounds
  have hF0' : ‖F 0‖ ≤ M₁ := hF0.trans hM
  have hδle : -δ ≤ (0:ℝ) := by linarith
  -- the core pointwise bound
  have hcore : ∀ z ∈ R, z ≠ 0 → ‖cexp (-(z * L) * I) * G z‖ ≤ 2 * M₁ * Real.exp (b * z.im) / ‖z‖ := by
    intro z hz hz0
    have him : z.im ≤ 0 := by
      have := (mem_reProdIm.1 hz).2; rw [uIcc_of_le hδle] at this; exact this.2
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_mul, norm_cexp_rot]
    have hGz := norm_dslope_le F hz0
    rw [← hG] at hGz
    have hFz := hbd z hz
    have he1 : 1 ≤ Real.exp (-(a * z.im)) := Real.one_le_exp (by nlinarith)
    have hnum : ‖F z‖ + ‖F 0‖ ≤ 2 * M₁ * Real.exp (-(a * z.im)) := by nlinarith
    calc Real.exp (L * z.im) * ‖G z‖ ≤ Real.exp (L * z.im) * ((‖F z‖ + ‖F 0‖) / ‖z‖) :=
          mul_le_mul_of_nonneg_left hGz (Real.exp_pos _).le
      _ ≤ Real.exp (L * z.im) * (2 * M₁ * Real.exp (-(a * z.im)) / ‖z‖) := by gcongr
      _ = 2 * M₁ * Real.exp (b * z.im) / ‖z‖ := by
          rw [show b * z.im = L * z.im + -(a * z.im) by rw [hbdef]; ring, Real.exp_add]; ring
  have hM1 : 0 ≤ M₁ := hM₀.trans hM
  -- bottom pieces
  set Cb := 2 * (h + δ) * M₁ * Real.exp (-(b * δ)) / δ with hCb
  have hbotpt : ∀ x : ℝ, x ∈ uIcc (-h) h → ∀ c : ℂ, ‖c‖ ≤ h + δ →
      ‖c * (cexp (-(((x : ℂ) + -(δ : ℂ) * I) * L) * I) * G ((x : ℂ) + -(δ : ℂ) * I))‖ ≤ Cb := by
    intro x hx c hc
    have hz : (x : ℂ) + -(δ : ℂ) * I ∈ R := by
      have := mem_rect (y := -δ) hx left_mem_uIcc; simpa using this
    have him : ((x : ℂ) + -(δ : ℂ) * I).im = -δ := by simp
    have hnz : (x : ℂ) + -(δ : ℂ) * I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; rw [him] at this; simp at this; linarith
    have hnorm : δ ≤ ‖(x : ℂ) + -(δ : ℂ) * I‖ := by
      have := abs_im_le_norm ((x : ℂ) + -(δ : ℂ) * I); rw [him, abs_neg, abs_of_pos hδ] at this
      exact this
    have h1 := hcore _ hz hnz
    rw [him] at h1
    rw [norm_mul]
    calc ‖c‖ * ‖cexp (-(((x : ℂ) + -(δ : ℂ) * I) * L) * I) * G ((x : ℂ) + -(δ : ℂ) * I)‖
        ≤ (h + δ) * (2 * M₁ * Real.exp (b * -δ) / δ) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = Cb := by rw [hCb]; ring_nf
  have hBp_le : ‖Bp‖ ≤ Cb * h := by
    have := norm_integral_le_of_norm_le_const (a := 0) (b := h) (C := Cb)
      (f := fun x : ℝ => fp ((x : ℂ) + -(δ : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le hh.le] at hx
        have hx' : x ∈ uIcc (-h) h := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith [hx.1, hx.2]
        refine hbotpt x hx' _ ?_
        have := norm_le_abs_re_add_abs_im ((h : ℂ) - ((x : ℂ) + -(δ : ℂ) * I))
        simp only [sub_re, add_re, ofReal_re, mul_re, neg_re, I_re, mul_zero, ofReal_im, neg_im,
          I_im, mul_one, sub_im, add_im, mul_im] at this
        have h2 : |h - x| ≤ h := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc _ ≤ _ := this
          _ ≤ h + δ := by simp [abs_of_pos hδ]; linarith)
    rw [sub_zero, abs_of_pos hh] at this; exact this
  have hBm_le : ‖Bm‖ ≤ Cb * h := by
    have := norm_integral_le_of_norm_le_const (a := -h) (b := 0) (C := Cb)
      (f := fun x : ℝ => fm ((x : ℂ) + -(δ : ℂ) * I)) (fun x hx => by
        rw [uIoc_of_le (by linarith)] at hx
        have hx' : x ∈ uIcc (-h) h := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith [hx.1, hx.2]
        refine hbotpt x hx' _ ?_
        have := norm_le_abs_re_add_abs_im ((h : ℂ) + ((x : ℂ) + -(δ : ℂ) * I))
        simp only [add_re, ofReal_re, mul_re, neg_re, I_re, mul_zero, ofReal_im, neg_im,
          I_im, mul_one, add_im, mul_im] at this
        have h2 : |h + x| ≤ h := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc _ ≤ _ := this
          _ ≤ h + δ := by simp [abs_of_pos hδ]; linarith)
    rw [sub_neg_eq_add, zero_add, abs_of_pos hh] at this; exact this
  -- side pieces
  have hsidept : ∀ (s : ℝ), (s = h ∨ s = -h) → ∀ y : ℝ, y ∈ Ioc (-δ) 0 → ∀ c : ℂ, ‖c‖ = -y →
      ‖c * (cexp (-(((s : ℂ) + y * I) * L) * I) * G ((s : ℂ) + y * I))‖ ≤
        2 * M₁ / h * (-y * Real.exp (b * y)) := by
    intro s hs y hy c hc
    have hsm : s ∈ uIcc (-h) h := by
      rw [uIcc_of_le (by linarith)]; rcases hs with rfl | rfl <;> constructor <;> linarith
    have hz : (s : ℂ) + y * I ∈ R := mem_rect hsm (by rw [uIcc_of_le hδle]; exact ⟨hy.1.le, hy.2⟩)
    have hre : |((s : ℂ) + y * I).re| = h := by
      simp; rcases hs with rfl | rfl <;> simp [abs_of_pos hh]
    have hnorm : h ≤ ‖(s : ℂ) + y * I‖ := by
      have := abs_re_le_norm ((s : ℂ) + y * I); rwa [hre] at this
    have hnz : (s : ℂ) + y * I ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; linarith
    have h1 := hcore _ hz hnz
    have him : ((s : ℂ) + y * I).im = y := by simp
    rw [him] at h1
    rw [norm_mul, hc]
    have hy0 : 0 ≤ -y := by linarith [hy.2]
    calc -y * ‖cexp (-(((s : ℂ) + y * I) * L) * I) * G ((s : ℂ) + y * I)‖
        ≤ -y * (2 * M₁ * Real.exp (b * y) / h) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 * M₁ / h * (-y * Real.exp (b * y)) := by ring
  have hside_int : ∫ y in (-δ)..0, 2 * M₁ / h * (-y * Real.exp (b * y)) ≤ 2 * M₁ / h * (4 / b ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
    gcongr
    exact integral_neg_mul_exp_le hb hδ.le
  have hcont_side : Continuous fun y : ℝ => 2 * M₁ / h * (-y * Real.exp (b * y)) := by fun_prop
  have hSp_le : ‖Sp‖ ≤ 2 * M₁ / h * (4 / b ^ 2) := by
    refine (norm_integral_le_of_norm_le hδle (Filter.Eventually.of_forall fun y hy => ?_)
      (hcont_side.intervalIntegrable _ _)).trans hside_int
    refine hsidept h (Or.inl rfl) y hy _ ?_
    rw [show (h : ℂ) - ((h : ℂ) + y * I) = -(y * I) by ring, norm_neg, norm_mul, norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hy.2]
  have hSm_le : ‖Sm‖ ≤ 2 * M₁ / h * (4 / b ^ 2) := by
    refine (norm_integral_le_of_norm_le hδle (Filter.Eventually.of_forall fun y hy => ?_)
      (hcont_side.intervalIntegrable _ _)).trans hside_int
    have := hsidept (-h) (Or.inr rfl) y hy (y * I) (by
      rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hy.2])
    simp only [hfm]
    rw [show (h : ℂ) + (-(h : ℂ) + y * I) = y * I by ring]
    simpa using this
  -- middle
  have hmidpt : ∀ y : ℝ, y ∈ Ioc (-δ) 0 → ‖fm (y * I) - fp (y * I)‖ ≤ 4 * M₀ * Real.exp (b * y) := by
    intro y hy
    have e : fm (y * I) - fp (y * I) = 2 * cexp (-((y * I) * L) * I) * (F (y * I) - F 0) := by
      simp only [hfm, hfp]
      rw [← mul_dslope F (y * I), ← hG]; ring
    rw [e, norm_mul, norm_mul, norm_cexp_rot]
    have him : ((y : ℂ) * I).im = y := by simp
    rw [him]
    have hF1 := hbd0 y hy.1.le hy.2
    have he1 : 1 ≤ Real.exp (-(a * y)) := Real.one_le_exp (by nlinarith [hy.2])
    have hsum : ‖F (y * I) - F 0‖ ≤ 2 * M₀ * Real.exp (-(a * y)) := by
      have := norm_sub_le (F (y * I)) (F 0); nlinarith
    calc ‖(2 : ℂ)‖ * Real.exp (L * y) * ‖F (y * I) - F 0‖
        ≤ 2 * Real.exp (L * y) * (2 * M₀ * Real.exp (-(a * y))) := by
          rw [show ‖(2 : ℂ)‖ = 2 by simp]; gcongr
      _ = 4 * M₀ * Real.exp (b * y) := by
          rw [hbdef]; rw [show 2 * Real.exp (L * y) * (2 * M₀ * Real.exp (-(a * y))) =
            4 * M₀ * (Real.exp (L * y) * Real.exp (-(a * y))) by ring, ← Real.exp_add]; ring_nf
  have hMid_le : ‖∫ y in (-δ)..0, (fm (y * I) - fp (y * I))‖ ≤ 4 * M₀ * (1 / b) := by
    refine (norm_integral_le_of_norm_le hδle (Filter.Eventually.of_forall fun y hy => hmidpt y hy)
      ((by fun_prop : Continuous fun y : ℝ => 4 * M₀ * Real.exp (b * y)).intervalIntegrable _ _)).trans ?_
    rw [intervalIntegral.integral_const_mul]
    gcongr
    exact integral_exp_le hb hδ.le
  -- assemble
  calc ‖Bm + Bp + I * Sp - I * Sm + I * ∫ y in (-δ)..0, (fm (y * I) - fp (y * I))‖
      ≤ ‖Bm‖ + ‖Bp‖ + ‖Sp‖ + ‖Sm‖ + ‖∫ y in (-δ)..0, (fm (y * I) - fp (y * I))‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans ?_) (by rw [norm_mul, norm_I, one_mul])
        refine add_le_add ((norm_add_le _ _).trans ?_) (by rw [norm_mul, norm_I, one_mul])
        refine add_le_add (norm_add_le _ _) (by rw [norm_mul, norm_I, one_mul])
    _ ≤ Cb * h + Cb * h + 2 * M₁ / h * (4 / b ^ 2) + 2 * M₁ / h * (4 / b ^ 2) + 4 * M₀ * (1 / b) := by
        gcongr
    _ = 4 * h * (h + δ) * M₁ * Real.exp (-(b * δ)) / δ + 16 * M₁ / (h * b ^ 2) + 4 * M₀ / b := by
        rw [hCb]; field_simp; ring

end RamanujanTau.SKQFProof
