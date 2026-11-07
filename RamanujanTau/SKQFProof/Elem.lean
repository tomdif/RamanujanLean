/-
# Elementary integrals and inequalities used in the `SKQFHyp` contour argument (level 1)
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

open MeasureTheory intervalIntegral
open scoped Interval

/-- `∫_{−δ}^0 e^{by} dy ≤ 1/b`. -/
lemma integral_exp_le {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) :
    ∫ y in (-δ)..0, Real.exp (b * y) ≤ 1 / b := by
  have hd : ∀ y ∈ Set.uIcc (-δ) 0, HasDerivAt (fun y => Real.exp (b * y) / b) (Real.exp (b * y)) y := by
    intro y _
    have h1 := ((hasDerivAt_id y).const_mul b).exp.div_const b
    simp only [id] at h1
    convert h1 using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun y => Real.exp (b * y)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  have : 0 ≤ Real.exp (b * -δ) / b := by positivity
  linarith

/-- `x e^{−bx/2} ≤ 2/b` in the form `(−y) e^{by} ≤ (2/b) e^{by/2}` for `y ≤ 0`. -/
lemma neg_mul_exp_le {b y : ℝ} (hb : 0 < b) :
    -y * Real.exp (b * y) ≤ 2 / b * Real.exp (b / 2 * y) := by
  have hx : -(b / 2 * y) ≤ Real.exp (-(b / 2 * y)) := by
    have := Real.add_one_le_exp (-(b / 2 * y)); linarith
  have e : Real.exp (b * y) = Real.exp (b / 2 * y) * Real.exp (b / 2 * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (b / 2 * y)
  have key : -y * Real.exp (b / 2 * y) ≤ 2 / b := by
    have : -y = 2 / b * (-(b / 2 * y)) := by field_simp
    rw [this, mul_assoc]
    have h2 : -(b / 2 * y) * Real.exp (b / 2 * y) ≤ 1 := by
      calc -(b / 2 * y) * Real.exp (b / 2 * y) ≤ Real.exp (-(b / 2 * y)) * Real.exp (b / 2 * y) :=
            mul_le_mul_of_nonneg_right hx hpos.le
        _ = 1 := by rw [← Real.exp_add]; simp
    have : 0 < 2 / b := by positivity
    nlinarith
  calc -y * (Real.exp (b / 2 * y) * Real.exp (b / 2 * y))
      = (-y * Real.exp (b / 2 * y)) * Real.exp (b / 2 * y) := by ring
    _ ≤ 2 / b * Real.exp (b / 2 * y) := mul_le_mul_of_nonneg_right key hpos.le

/-- `∫_{−δ}^0 (−y) e^{by} dy ≤ 4/b²`. -/
lemma integral_neg_mul_exp_le {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) :
    ∫ y in (-δ)..0, -y * Real.exp (b * y) ≤ 4 / b ^ 2 := by
  have hle : -δ ≤ 0 := by linarith
  calc ∫ y in (-δ)..0, -y * Real.exp (b * y)
      ≤ ∫ y in (-δ)..0, 2 / b * Real.exp (b / 2 * y) := by
        refine integral_mono_on hle ((by fun_prop : Continuous fun y : ℝ => -y * Real.exp (b * y)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun y : ℝ => 2 / b * Real.exp (b / 2 * y)).intervalIntegrable _ _)
          fun y _ => neg_mul_exp_le hb
    _ = 2 / b * ∫ y in (-δ)..0, Real.exp (b / 2 * y) := by rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 / b * (1 / (b / 2)) := by
        gcongr
        exact integral_exp_le (by positivity) hδ
    _ = 4 / b ^ 2 := by field_simp; ring

/-- `|sinc x| ≤ 2/(1+|x|)`. -/
lemma abs_sinc_le (x : ℝ) : |Real.sinc x| ≤ 2 / (1 + |x|) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |x| 1 with hx | hx
  · have := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x)]
  · have hx0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
    rw [Real.sinc_of_ne_zero hx0, abs_div]
    have hs := Real.abs_sin_le_one x
    have hpos : 0 < |x| := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [abs_nonneg (Real.sin x)]

/-- `∫_{−h}^{h} L/(1+|v|L) dv = 2 log(1+hL)`, as an upper bound. -/
lemma integral_inv_one_add_le {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) :
    ∫ v in (-h)..h, L / (1 + |v| * L) ≤ 2 * Real.log (1 + h * L) := by
  have hc : Continuous fun v : ℝ => L / (1 + |v| * L) := by
    refine Continuous.div continuous_const (by fun_prop) fun v => ?_
    have := abs_nonneg v; positivity
  have half : ∫ v in (0:ℝ)..h, L / (1 + |v| * L) = Real.log (1 + h * L) := by
    have hd : ∀ v ∈ Set.uIcc 0 h, HasDerivAt (fun v => Real.log (1 + v * L)) (L / (1 + |v| * L)) v := by
      intro v hv
      rw [Set.uIcc_of_le hh] at hv
      have hv0 : 0 ≤ v := hv.1
      have hpos : 0 < 1 + v * L := by positivity
      have h1 := ((((hasDerivAt_id v).mul_const L).const_add 1)).log hpos.ne'
      rw [abs_of_nonneg hv0]
      convert h1 using 1
      simp
    rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
    simp
  have neg : ∫ v in (-h)..0, L / (1 + |v| * L) = ∫ v in (0:ℝ)..h, L / (1 + |v| * L) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := h) (fun v : ℝ => L / (1 + |v| * L))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), neg, half]
  linarith

end RamanujanTau.SKQFProof
