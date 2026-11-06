/-
# Digamma differences on vertical lines

* `norm_digamma_sub_log_le`: `‖ψ(z) − log z‖ ≤ 40/(Re z − 1 + |Im z|)` for `Re z ≥ 2`
  (generalizes `ZeroCountRvM.norm_digamma_six_sub_log_le`);
* `norm_shift_ge`: `1 + |t| ≤ 2 (1+|y|) ‖6+it + x+iy‖` for `x ≥ −1`;
* **`norm_digamma_diff_le`**: for `x ≥ −1`,
  `‖ψ(6+it + x+iy) − ψ(6+it)‖ ≤ C_x (1+|y|)² / (1+|t|)`, uniformly in `t, y`.
  This is the `1/t` saving behind `∂_t V_t = O(1/t)`.
-/
import RamanujanTau.HeckeAFE.Main
import RamanujanTau.ZeroCountRvM.DigammaAsymp

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE2

open Complex Set RamanujanTau.HeckeAFE RamanujanTau.ZeroCountRvM
open scoped Real

theorem norm_digamma_sub_log_le {z : ℂ} (hz : 2 ≤ z.re) :
    ‖digamma z - log z‖ ≤ 40 / (z.re - 1 + |z.im|) := by
  have hs : 0 < z.re := by linarith
  rw [digamma_eq_log_add hs, add_sub_cancel_left]
  set a : ℝ := z.re + |z.im| with ha
  have ha1 : 1 < a := by have := abs_nonneg z.im; linarith
  have hb : ∀ j : ℕ, ‖et z j‖ ≤ 40 * (1 / (a + j) ^ 2) := by
    intro j
    refine (norm_et_le hs j).trans ?_
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hn2 : ‖z + j‖ ^ 2 = (z.re + j) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [norm_div, norm_one, div_pow, one_pow, hn2]
    have hyy : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    have hkey : (a + j) ^ 2 ≤ 2 * ((z.re + j) ^ 2 + z.im ^ 2) := by
      rw [ha]; nlinarith [sq_nonneg (z.re + j - |z.im|), abs_nonneg z.im]
    have hrj : 0 < z.re + (j : ℝ) := by linarith
    have hp1 : 0 < (z.re + (j : ℝ)) ^ 2 + z.im ^ 2 := by positivity
    have hp2 : 0 < (a + j) ^ 2 := by positivity
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ hp1 hp2]
    nlinarith
  obtain ⟨hsum, hle⟩ := tsum_inv_sq_le ha1
  have := tsum_of_norm_bounded (hsum.mul_left 40) hb
  calc ‖∑' j, et z j‖ ≤ 40 * ∑' j : ℕ, 1 / (a + j) ^ 2 := this
    _ ≤ 40 * (1 / (a - 1)) := by gcongr
    _ = _ := by rw [ha]; ring_nf

lemma norm_shift_ge (t x y : ℝ) (hx : -1 ≤ x) :
    1 + |t| ≤ 2 * (1 + |y|) * ‖(6 + t * I) + ((x : ℂ) + y * I)‖ := by
  set z : ℂ := (6 + t * I) + ((x : ℂ) + y * I)
  have hre : z.re = 6 + x := by simp [z]
  have him : z.im = t + y := by simp [z]
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  rw [hre, abs_of_pos (by linarith)] at h1
  rw [him] at h2
  have h3 : |t| ≤ |t + y| + |y| := by
    calc |t| = |(t + y) - y| := by ring_nf
      _ ≤ |t + y| + |y| := abs_sub _ _
  have hy := abs_nonneg y
  have hty := abs_nonneg (t + y)
  nlinarith

lemma norm_inv_shift_le (t x y : ℝ) (hx : -1 ≤ x) :
    ‖((6 + t * I) + ((x : ℂ) + y * I))⁻¹‖ ≤ 2 * (1 + |y|) / (1 + |t|) := by
  have h := norm_shift_ge t x y hx
  have h1t : 0 < 1 + |t| := by positivity
  have hpos : 0 < ‖(6 + t * I) + ((x : ℂ) + y * I)‖ := by
    have : 0 < 2 * (1 + |y|) := by positivity
    by_contra hc; push Not at hc
    have := norm_nonneg ((6 + t * I) + ((x : ℂ) + y * I))
    nlinarith
  rw [norm_inv, le_div_iff₀ h1t]
  calc ‖(6 + t * I) + ((x : ℂ) + y * I)‖⁻¹ * (1 + |t|)
      ≤ ‖(6 + t * I) + ((x : ℂ) + y * I)‖⁻¹ *
          (2 * (1 + |y|) * ‖(6 + t * I) + ((x : ℂ) + y * I)‖) := by gcongr
    _ = 2 * (1 + |y|) := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]

lemma norm_digamma_sub_log_shift (t x y : ℝ) (hx : -1 ≤ x) :
    ‖digamma ((6 + t * I) + ((x : ℂ) + y * I)) - log ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤
      100 * (1 + |y|) / (1 + |t|) := by
  set z : ℂ := (6 + t * I) + ((x : ℂ) + y * I)
  have hre : z.re = 6 + x := by simp [z]
  have h := norm_digamma_sub_log_le (z := z) (by rw [hre]; linarith)
  have hn : ‖z‖ ≤ z.re + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rwa [abs_of_pos (by rw [hre]; linarith)] at this
  have hz5 : 5 ≤ z.re := by rw [hre]; linarith
  have hden : 4 / 5 * ‖z‖ ≤ z.re - 1 + |z.im| := by
    have := abs_nonneg z.im; nlinarith
  have hpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) ((Complex.re_le_norm z).trans' hz5)
  have hi := norm_inv_shift_le t x y hx
  rw [norm_inv] at hi
  have h1t : 0 < 1 + |t| := by positivity
  calc ‖digamma z - log z‖ ≤ 40 / (z.re - 1 + |z.im|) := h
    _ ≤ 40 / (4 / 5 * ‖z‖) := by gcongr
    _ = 50 * ‖z‖⁻¹ := by field_simp; ring
    _ ≤ 50 * (2 * (1 + |y|) / (1 + |t|)) := by gcongr
    _ = _ := by ring

lemma norm_log_shift_sub_le (t x y : ℝ) (hx : -1 ≤ x) :
    ‖log ((6 + t * I) + ((x : ℂ) + y * I)) - log (6 + t * I)‖ ≤
      2 * (1 + |y|) / (1 + |t|) * ‖(x : ℂ) + y * I‖ := by
  set s : ℂ := 6 + t * I
  set u : ℂ := (x : ℂ) + y * I
  have hseg : ∀ w ∈ segment ℝ s (s + u), ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      w = (6 + t * I) + (((θ * x : ℝ) : ℂ) + ((θ * y : ℝ) : ℂ) * I) := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hw
    refine ⟨θ, h0, h1, ?_⟩
    simp only [s, u, Complex.real_smul]; push_cast; ring
  have hdiff : ∀ w ∈ segment ℝ s (s + u), DifferentiableAt ℂ log w := by
    intro w hw
    obtain ⟨θ, h0, h1, rfl⟩ := hseg w hw
    refine (hasDerivAt_log (mem_slitPlane_iff.2 (Or.inl ?_))).differentiableAt
    simp; nlinarith
  have hbd : ∀ w ∈ segment ℝ s (s + u), ‖deriv log w‖ ≤ 2 * (1 + |y|) / (1 + |t|) := by
    intro w hw
    obtain ⟨θ, h0, h1, rfl⟩ := hseg w hw
    have hre : 0 < ((6 + t * I) + (((θ * x : ℝ) : ℂ) + ((θ * y : ℝ) : ℂ) * I)).re := by
      simp; nlinarith
    rw [(hasDerivAt_log (mem_slitPlane_iff.2 (Or.inl hre))).deriv]
    refine (norm_inv_shift_le t (θ * x) (θ * y) (by nlinarith)).trans ?_
    have : |θ * y| ≤ |y| := by
      rw [abs_mul, abs_of_nonneg h0]; nlinarith [abs_nonneg y]
    gcongr
  have := (convex_segment s (s + u)).norm_image_sub_le_of_norm_deriv_le hdiff hbd
    (left_mem_segment ℝ s (s + u)) (right_mem_segment ℝ s (s + u))
  rwa [add_sub_cancel_left] at this

/-- **Digamma difference bound**: for `x ≥ −1`,
`‖ψ(6+it + x+iy) − ψ(6+it)‖ ≤ C (1+|y|)²/(1+|t|)` uniformly in `t, y ∈ ℝ`. -/
theorem norm_digamma_diff_le {x : ℝ} (hx : -1 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ,
      ‖digamma ((6 + t * I) + ((x : ℂ) + y * I)) - digamma (6 + t * I)‖ ≤
        C * (1 + |y|) ^ 2 / (1 + |t|) := by
  refine ⟨2 * (1 + |x|) + 200, by positivity, fun t y => ?_⟩
  have h1 := norm_digamma_sub_log_shift t x y hx
  have h2 := norm_digamma_sub_log_shift t 0 0 (by norm_num)
  have h3 := norm_log_shift_sub_le t x y hx
  have e0 : (6 + t * I) + (((0:ℝ) : ℂ) + ((0:ℝ) : ℂ) * I) = 6 + t * I := by simp
  rw [e0] at h2
  simp only [abs_zero, add_zero] at h2
  have hu : ‖(x : ℂ) + y * I‖ ≤ (1 + |x|) * (1 + |y|) := by
    have := Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + y * I)
    simp at this; nlinarith [abs_nonneg x, abs_nonneg y]
  have h1t : 0 < 1 + |t| := by positivity
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  set z : ℂ := (6 + t * I) + ((x : ℂ) + y * I)
  have e : digamma z - digamma (6 + t * I) = (log z - log (6 + t * I)) +
      (digamma z - log z) - (digamma (6 + t * I) - log (6 + t * I)) := by ring
  rw [e]
  have hA := norm_sub_le (log z - log (6 + t * I) + (digamma z - log z))
    (digamma (6 + t * I) - log (6 + t * I))
  have hB := norm_add_le (log z - log (6 + t * I)) (digamma z - log z)
  have h3' : ‖log z - log (6 + t * I)‖ ≤ 2 * (1 + |y|) / (1 + |t|) * ((1 + |x|) * (1 + |y|)) :=
    h3.trans (by gcongr)
  rw [div_mul_eq_mul_div] at h3'
  have key : 2 * (1 + |y|) * ((1 + |x|) * (1 + |y|)) + 100 * (1 + |y|) + 100 * 1 ≤
      (2 * (1 + |x|) + 200) * (1 + |y|) ^ 2 := by nlinarith [abs_nonneg x]
  calc _ ≤ 2 * (1 + |y|) * ((1 + |x|) * (1 + |y|)) / (1 + |t|) + 100 * (1 + |y|) / (1 + |t|) +
        100 * 1 / (1 + |t|) := by rw [mul_one]; linarith [h1, h2, h3']
    _ = (2 * (1 + |y|) * ((1 + |x|) * (1 + |y|)) + 100 * (1 + |y|) + 100 * 1) / (1 + |t|) := by
        ring
    _ ≤ _ := by gcongr

end RamanujanTau.HeckeAFE2
