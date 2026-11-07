/-
# The Bessel weight of the Andrews–Dragonette series

`k · M_{2k}(n) = A √k sinh(B/k)` with `A = √24/√(24n−1)`, `B = π√(24n−1)/12` (`Andrews66.MK_two`).
For real `x ≥ 1`, `w(x) = A√x sinh(B/x)` satisfies
* `|w(x)| ≤ A B cosh B · x^{−1/2}` (`w_le`),
* `|w(x+1) − w(x)| ≤ 2 A B cosh B · x^{−3/2}` (`w_sub_le`).
-/
import Mathlib

set_option autoImplicit false

namespace AndrewsDragonette
open Real

lemma sinh_lip {B u v : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) (hv0 : 0 ≤ v) (hvB : v ≤ B) :
    |sinh u - sinh v| ≤ cosh B * |u - v| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.sinh) (s := Set.Icc 0 B)
    (C := cosh B) (fun x _ => Real.differentiable_sinh x) (fun x hx => ?_) (convex_Icc 0 B)
    ⟨hv0, hvB⟩ ⟨hu0, huB⟩
  · simpa [Real.norm_eq_abs] using this
  · rw [Real.deriv_sinh, Real.norm_eq_abs, abs_of_pos (cosh_pos x)]
    rw [cosh_le_cosh, abs_of_nonneg hx.1, abs_of_nonneg (hx.1.trans hx.2)]
    exact hx.2

/-- The weight `w(x) = A √x sinh(B/x)`. -/
noncomputable def wt (A B x : ℝ) : ℝ := A * √x * sinh (B / x)

lemma sinh_div_le {B x : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) : |sinh (B / x)| ≤ cosh B * (B / x) := by
  have hx0 : 0 < x := by linarith
  have h1 : B / x ≤ B := div_le_self hB hx
  have h0 : 0 ≤ B / x := div_nonneg hB hx0.le
  have := sinh_lip h0 h1 (le_refl 0) hB
  simpa [abs_of_nonneg h0] using this

lemma rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = 1 / √x := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]; simp only [one_div]

lemma rpow_neg_three_half {x : ℝ} (hx : 0 < x) : x ^ (-(3 / 2 : ℝ)) = 1 / (x * √x) := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, one_div, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one]

lemma w_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 1 ≤ x) :
    |wt A B x| ≤ A * B * cosh B * x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  rw [rpow_neg_half hx0, wt, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hs.le]
  have := sinh_div_le hB hx
  calc A * √x * |sinh (B / x)| ≤ A * √x * (cosh B * (B / x)) := by gcongr
    _ = A * B * cosh B * (1 / √x) := by
        rw [show B / x = B / (√x * √x) by rw [Real.mul_self_sqrt hx0.le]]
        field_simp

lemma w_sub_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 1 ≤ x) :
    |wt A B (x + 1) - wt A B x| ≤ 2 * (A * B * cosh B) * x ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x + 1 := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hs1 : 0 < √(x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hss : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hcB : 0 < cosh B := cosh_pos B
  -- split
  have hsplit : wt A B (x + 1) - wt A B x =
      A * ((√(x + 1) - √x) * sinh (B / x) + √(x + 1) * (sinh (B / (x + 1)) - sinh (B / x))) := by
    unfold wt; ring
  -- |√(x+1) − √x| ≤ 1/√x
  have hd : |√(x + 1) - √x| ≤ 1 / √x := by
    rw [abs_of_nonneg (by linarith)]
    have hprod : (√(x + 1) - √x) * (√(x + 1) + √x) = 1 := by
      have e1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)
      have e2 := Real.mul_self_sqrt hx0.le
      nlinarith
    rw [le_div_iff₀ hs]
    nlinarith
  have h1 : B / (x + 1) ≤ B := div_le_self hB hx1
  have h0 : B / x ≤ B := div_le_self hB hx
  have hl := sinh_lip (div_nonneg hB (by linarith)) h1 (div_nonneg hB hx0.le) h0
  have hdiff : |B / (x + 1) - B / x| = B / (x * (x + 1)) := by
    rw [show B / (x + 1) - B / x = -(B / (x * (x + 1))) by field_simp; ring, abs_neg,
      abs_of_nonneg (by positivity)]
  rw [hdiff] at hl
  have hsd := sinh_div_le hB hx
  rw [hsplit, abs_mul, abs_of_nonneg hA, rpow_neg_three_half hx0]
  have key : |(√(x + 1) - √x) * sinh (B / x) + √(x + 1) * (sinh (B / (x + 1)) - sinh (B / x))| ≤
      2 * (B * cosh B) * (1 / (x * √x)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hs1.le]
    have t1 : |√(x + 1) - √x| * |sinh (B / x)| ≤ (1 / √x) * (cosh B * (B / x)) :=
      mul_le_mul hd hsd (abs_nonneg _) (by positivity)
    have t2 : √(x + 1) * |sinh (B / (x + 1)) - sinh (B / x)| ≤
        √(x + 1) * (cosh B * (B / (x * (x + 1)))) := by gcongr
    have e1 : (1 / √x) * (cosh B * (B / x)) = B * cosh B * (1 / (x * √x)) := by
      field_simp
    have e2 : √(x + 1) * (cosh B * (B / (x * (x + 1)))) ≤ B * cosh B * (1 / (x * √x)) := by
      have ex1 : x * (x + 1) = x * (√(x + 1) * √(x + 1)) := by
        rw [Real.mul_self_sqrt (by linarith)]
      have : √(x + 1) * (cosh B * (B / (x * (x + 1)))) = B * cosh B * (1 / (x * √(x + 1))) := by
        rw [ex1]; field_simp
      rw [this]
      gcongr
    linarith
  calc A * |(√(x + 1) - √x) * sinh (B / x) + √(x + 1) * (sinh (B / (x + 1)) - sinh (B / x))|
      ≤ A * (2 * (B * cosh B) * (1 / (x * √x))) := by gcongr
    _ = 2 * (A * B * cosh B) * (1 / (x * √x)) := by ring

end AndrewsDragonette
