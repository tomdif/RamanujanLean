/-
# Shifting a line integral across a horizontal strip

`integral_shift`: if `G` is holomorphic on the closed horizontal strip `0 ≤ Im ≤ c` (or `c ≤ Im ≤ 0`), is
uniformly small on the vertical edges far out (`‖G(x + yi)‖ ≤ B(x)`, `B → 0` at `±∞`), and is integrable on
both boundary lines, then `∫_ℝ G(x) dx = ∫_ℝ G(x + ci) dx`.

This is the rectangle Cauchy–Goursat theorem plus a limit, as in Mathlib's `GaussianFourier`.
-/
import Mathlib

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set intervalIntegral
open scoped Topology Real

theorem integral_shift {G : ℂ → ℂ} {c : ℝ}
    (hd : ∀ x y : ℝ, y ∈ uIcc 0 c → DifferentiableAt ℂ G (x + y * I))
    (B : ℝ → ℝ) (hBt : Tendsto B atTop (𝓝 0)) (hBb : Tendsto B atBot (𝓝 0))
    (hB : ∀ x y : ℝ, y ∈ uIcc 0 c → ‖G (x + y * I)‖ ≤ B x)
    (h0 : Integrable (fun x : ℝ => G x)) (hc : Integrable (fun x : ℝ => G (x + c * I))) :
    ∫ x : ℝ, G x = ∫ x : ℝ, G (x + c * I) := by
  -- vertical edge integrals
  set V : ℝ → ℂ := fun T => ∫ y : ℝ in (0 : ℝ)..c, G (T + y * I) with hV
  have hVle : ∀ T, ‖V T‖ ≤ B T * |c - 0| := by
    intro T
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hB T y ?_
    exact uIoc_subset_uIcc hy
  have hVt : ∀ {l : Filter ℝ}, Tendsto B l (𝓝 0) → Tendsto V l (𝓝 0) := by
    intro l hl
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun T => B T * |c - 0|) l (𝓝 0) := by simpa using hl.mul_const |c - 0|
    exact squeeze_zero (fun _ => norm_nonneg _) hVle this
  -- the rectangle identity
  have hrect : ∀ T : ℝ, (∫ x : ℝ in -T..T, G x) - (∫ x : ℝ in -T..T, G (x + c * I)) =
      I * V (-T) - I * V T := by
    intro T
    have H := integral_boundary_rect_eq_zero_of_differentiableOn G (-T : ℂ) (T + c * I) (by
      intro w hw
      rw [mem_reProdIm] at hw
      have hw' : w = (w.re : ℂ) + (w.im : ℂ) * I := (re_add_im w).symm
      have him : w.im ∈ uIcc 0 c := by simpa using hw.2
      rw [hw']
      exact (hd w.re w.im him).differentiableWithinAt)
    simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, mul_re, I_re, I_im,
      mul_zero, sub_zero, add_im, mul_im, mul_one, zero_add, add_zero, ofReal_zero, zero_mul,
      smul_eq_mul, ofReal_neg] at H
    rw [hV]
    simp only [ofReal_neg]
    linear_combination H
  -- pass to the limit
  have hL : Tendsto (fun T : ℝ => (∫ x : ℝ in -T..T, G x) - (∫ x : ℝ in -T..T, G (x + c * I))) atTop
      (𝓝 ((∫ x : ℝ, G x) - ∫ x : ℝ, G (x + c * I))) :=
    (intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id)
  have hR : Tendsto (fun T : ℝ => I * V (-T) - I * V T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => V (-T)) atTop (𝓝 0) :=
      (hVt hBb).comp tendsto_neg_atTop_atBot
    have h2 : Tendsto V atTop (𝓝 0) := hVt hBt
    simpa using (h1.const_mul I).sub (h2.const_mul I)
  have := tendsto_nhds_unique hL (by simpa only [hrect] using hR)
  exact sub_eq_zero.mp this

end MockCusp
