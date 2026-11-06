/-
# The Gaussian window: `∫ e^{−((t−T)/H)²} cos(l t) dt = H √π e^{−(Hl)²/4} cos(lT)`
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Complex MeasureTheory

/-- The Gaussian window `w(t) = e^{−((t−T)/H)²}`. -/
noncomputable def gw (H T t : ℝ) : ℝ := Real.exp (-((t - T) / H) ^ 2)

lemma gw_pos (H T t : ℝ) : 0 < gw H T t := Real.exp_pos _

private lemma quad_eq {H T l : ℝ} (hH : H ≠ 0) (t : ℝ) :
    (cexp ((-(1 / (H : ℂ) ^ 2)) * (t : ℂ) ^ 2 + (2 * T / (H : ℂ) ^ 2 + l * I) * t +
      (-(T : ℂ) ^ 2 / (H : ℂ) ^ 2))).re = gw H T t * Real.cos (l * t) := by
  have e : (-(1 / (H : ℂ) ^ 2)) * (t : ℂ) ^ 2 + (2 * T / (H : ℂ) ^ 2 + l * I) * t +
      (-(T : ℂ) ^ 2 / (H : ℂ) ^ 2) = ((-((t - T) / H) ^ 2 : ℝ) : ℂ) + ((l * t : ℝ) : ℂ) * I := by
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH
    push_cast; field_simp; ring
  rw [e, Complex.exp_re, add_re, add_im, ofReal_re, ofReal_im, re_ofReal_mul, im_ofReal_mul,
    I_re, I_im]
  simp [gw]

lemma integrable_gw_cos {H : ℝ} (hH : 0 < H) (T l : ℝ) :
    Integrable fun t : ℝ => gw H T t * Real.cos (l * t) := by
  have hb : (-(1 / (H : ℂ) ^ 2)).re < 0 := by
    have : (-(1 / (H : ℂ) ^ 2)) = ((-(1 / H ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, ofReal_re]; have : 0 < 1 / H ^ 2 := by positivity
    linarith
  have hi := (integrable_cexp_quadratic' hb (2 * T / (H : ℂ) ^ 2 + l * I)
    (-(T : ℂ) ^ 2 / (H : ℂ) ^ 2)).re
  refine hi.congr (Filter.Eventually.of_forall fun t => ?_)
  exact quad_eq hH.ne' t

/-- **Gaussian cosine integral.** -/
theorem integral_gw_cos {H : ℝ} (hH : 0 < H) (T l : ℝ) :
    ∫ t : ℝ, gw H T t * Real.cos (l * t) =
      H * Real.sqrt π * Real.exp (-(H * l) ^ 2 / 4) * Real.cos (l * T) := by
  have hb : (-(1 / (H : ℂ) ^ 2)).re < 0 := by
    have : (-(1 / (H : ℂ) ^ 2)) = ((-(1 / H ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, ofReal_re]; have : 0 < 1 / H ^ 2 := by positivity
    linarith
  set c : ℂ := 2 * T / (H : ℂ) ^ 2 + l * I
  set d : ℂ := -(T : ℂ) ^ 2 / (H : ℂ) ^ 2
  have hint := integrable_cexp_quadratic' hb c d
  have e1 : (fun t : ℝ => gw H T t * Real.cos (l * t)) =
      fun t : ℝ => (cexp ((-(1 / (H : ℂ) ^ 2)) * (t : ℂ) ^ 2 + c * t + d)).re :=
    funext fun t => (quad_eq hH.ne' t).symm
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [e1, hre, integral_cexp_quadratic hb c d]
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have e2 : (π : ℂ) / -(-(1 / (H : ℂ) ^ 2)) = ((π * H ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  have e3 : ((π * H ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((H * Real.sqrt π : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hH.le, mul_comm]
  have e4 : d - c ^ 2 / (4 * -(1 / (H : ℂ) ^ 2)) =
      ((-(H * l) ^ 2 / 4 : ℝ) : ℂ) + ((l * T : ℝ) : ℂ) * I := by
    simp only [c, d]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e2, e3, e4, re_ofReal_mul, Complex.exp_re]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  ring

end RamanujanTau.SubconvexityCond
