import RamanujanTau.Velu.Infinity

/-!
# Vélu's formulas: main theorems

* `Velu.Kernel.velu_equation`: for `(x, y)` on `E : y² = x³ + Ax + B` with `x ≠ x_Q` for all
  `Q ∈ S`, the point `(X(x), Y(x,y))` lies on `E' : y² = x³ + (A - 5t)x + (B - 7w)`.
* `Velu.Kernel.velu_equation_point`: the same for points `P ∈ E(K) ∖ G`.
* `Velu.Kernel.N1_eq_derivative`, `X_eq_div`, `Xd_eq_div`: `X = N/D²` and `X' = N₁/D³` with
  `N₁ = N' D - 2 N D'`, i.e. `Xd` is the `x`-derivative of `X`; with `Y_eq : Y = y · Xd` this gives
  `dX/(2Y) = dx/(2y)`.
* `Velu.Kernel.curve_Δ`: `Δ(E') = -16 (4 (A - 5t)³ + 27 (B - 7w)²)`.
-/

namespace Velu

open Polynomial WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

lemma eval_D_ne {x : K} (hx : ∀ Q ∈ κ.S, x ≠ xc Q) : κ.D.eval x ≠ 0 := by
  rw [D, eval_prod]
  exact Finset.prod_ne_zero_iff.2 fun Q hQ => by
    simp only [vp, eval_sub, eval_X, eval_C]; exact sub_ne_zero.2 (hx Q hQ)

lemma eval_Dq {x : K} {Q : (short A B).Point} (hQ : Q ∈ κ.S) (hx : x ≠ xc Q) :
    (κ.Dq Q).eval x = κ.D.eval x / (x - xc Q) := by
  rw [κ.D_eq hQ, eval_mul]
  simp only [vp, eval_sub, eval_X, eval_C]
  field_simp [sub_ne_zero.2 hx]

/-- `X(x) = N(x) / D(x)²`. -/
lemma X_eq_div {x : K} (hx : ∀ Q ∈ κ.S, x ≠ xc Q) :
    κ.X x = κ.N.eval x / κ.D.eval x ^ 2 := by
  have hD := κ.eval_D_ne hx
  rw [eq_div_iff (pow_ne_zero 2 hD), X, N, eval_add, eval_mul, eval_X, eval_pow, eval_finsetSum,
    add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hxQ : x - xc Q ≠ 0 := sub_ne_zero.2 (hx Q hQ)
  rw [eval_mul, eval_pow, κ.eval_Dq hQ (hx Q hQ)]
  simp only [vp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  field_simp

/-- `X'(x) = N₁(x) / D(x)³`. -/
lemma Xd_eq_div {x : K} (hx : ∀ Q ∈ κ.S, x ≠ xc Q) :
    κ.Xd x = κ.N1.eval x / κ.D.eval x ^ 3 := by
  have hD := κ.eval_D_ne hx
  rw [eq_div_iff (pow_ne_zero 3 hD), Xd, N1, eval_sub, eval_pow, eval_finsetSum,
    sub_mul, Finset.sum_mul, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hxQ : x - xc Q ≠ 0 := sub_ne_zero.2 (hx Q hQ)
  rw [eval_mul, eval_pow, κ.eval_Dq hQ (hx Q hQ)]
  simp only [vp, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_ofNat]
  field_simp

/-- `N₁ = N' D - 2 N D'`: `N₁/D³` is the derivative of `N/D²` (quotient rule), so `Xd = dX/dx`. -/
theorem N1_eq_derivative : κ.N1 = derivative κ.N * κ.D - 2 * κ.N * derivative κ.D := by
  have key : ∀ Q ∈ κ.S, derivative ((C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2) * κ.D -
      2 * ((C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2) * derivative κ.D =
      -((C (tQ Q) * vp Q + 2 * C (uQ Q)) * κ.Dq Q ^ 3) := by
    intro Q hQ
    rw [κ.D_eq hQ]
    simp only [vp, derivative_mul, derivative_add, derivative_sub, derivative_C, derivative_X,
      derivative_pow, map_ofNat, Nat.cast_ofNat]
    ring
  have key0 : derivative (Polynomial.X * κ.D ^ 2) * κ.D -
      2 * (Polynomial.X * κ.D ^ 2) * derivative κ.D = κ.D ^ 3 := by
    simp only [derivative_mul, derivative_X, derivative_pow, map_ofNat, Nat.cast_ofNat]
    ring
  rw [N1, N, derivative_add]
  have hs : derivative (∑ Q ∈ κ.S, (C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2) * κ.D -
      2 * (∑ Q ∈ κ.S, (C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2) * derivative κ.D =
      -∑ Q ∈ κ.S, (C (tQ Q) * vp Q + 2 * C (uQ Q)) * κ.Dq Q ^ 3 := by
    rw [map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl key
  linear_combination -key0 - hs

/-- The invariant differential is preserved: `dX / (2Y) = dx / (2y)`, i.e.
`X'(x) / (2 Y) = 1 / (2 y)` where `X' = Xd` is the `x`-derivative of `X`. -/
theorem invariant_differential {x y : K} (hy : y ≠ 0) (hXd : κ.Xd x ≠ 0) :
    κ.Xd x / (2 * κ.Y x y) = 1 / (2 * y) := by
  rw [Y_eq]
  by_cases h2 : (2 : K) = 0
  · simp [h2]
  · field_simp

/-- **Vélu's theorem (curve equation)**: for `(x, y) ∈ E` with `x ∉ {x_Q : Q ∈ S}`,
`(X(x), Y(x, y))` lies on the Vélu curve `y² = x³ + (A - 5t) x + (B - 7w)`. -/
theorem velu_equation (h2 : (2 : K) ≠ 0) {x y : K} (hxy : y ^ 2 = x ^ 3 + A * x + B)
    (hx : ∀ Q ∈ κ.S, x ≠ xc Q) : κ.curve.Equation (κ.X x) (κ.Y x y) := by
  rw [curve, short_equation_iff, Y_eq]
  have hD := κ.eval_D_ne hx
  have hP := congrArg (eval x) (κ.Pv_eq_zero h2)
  rw [Pv, fpoly] at hP
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_zero] at hP
  rw [κ.X_eq_div hx, κ.Xd_eq_div hx]
  field_simp
  linear_combination (κ.N1.eval x) ^ 2 * hxy + hP

/-- Vélu's theorem for points: `P ∈ E(K) ∖ G` maps to a point of the Vélu curve. -/
theorem velu_equation_point (h2 : (2 : K) ≠ 0) {P : (short A B).Point} (hP0 : P ≠ 0)
    (hP : P ∉ κ.G) : κ.curve.Equation (κ.X (xc P)) (κ.Y (xc P) (yc P)) :=
  κ.velu_equation h2 (equation_xc_yc hP0) fun _ hQ => κ.xc_ne_of_not_mem_G hP0 hP hQ

end Kernel

end Velu
