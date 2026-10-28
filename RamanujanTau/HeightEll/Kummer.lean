/-
# Kummer-line formulas on Mathlib's point group

For a Weierstrass curve over a field and affine points `A = (x₁, y₁)`, `B = (x₂, y₂)` with `x₁ ≠ x₂`:
  `(x₁ - x₂)² (x(A+B) + x(A-B)) = kS(x₁, x₂)`,  `(x₁ - x₂)² x(A+B) x(A-B) = kQ(x₁, x₂)`.
Doubling: if `2A ≠ 0` then `kPsi(x₁) ≠ 0` and `kPsi(x₁) · x(2A) = kPhi(x₁)`.
-/
import Mathlib

set_option autoImplicit false

namespace HeightEll

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- `x(A+B) + x(A-B)` numerator. -/
def kS {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₁ x₂ : R) : R :=
  2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆

/-- `x(A+B) x(A-B)` numerator. -/
def kQ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₁ x₂ : R) : R :=
  x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈

/-- the `2`-division polynomial `4x³ + b₂x² + 2b₄x + b₆`. -/
def kPsi {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x : R) : R :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- `x⁴ - b₄x² - 2b₆x - b₈`. -/
def kPhi {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x : R) : R :=
  x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

/-- the `x`-coordinate (junk `0` at the origin). -/
def xc : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

@[simp] lemma xc_zero : xc W 0 = 0 := rfl
@[simp] lemma xc_some {x y : F} (h : W.toAffine.Nonsingular x y) : xc W (.some x y h) = x := rfl

lemma xc_neg (P : W.toAffine.Point) : xc W (-P) = xc W P := by
  cases P with
  | zero => rfl
  | some x y h => rw [neg_some]; rfl

lemma eq_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ x y, ∃ h : W.toAffine.Nonsingular x y, P = .some x y h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨x, y, h, rfl⟩

lemma eq_or_eq_neg_of_xc_eq {P Q : W.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : xc W P = xc W Q) : P = Q ∨ P = -Q := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ := eq_some_of_ne_zero W hP
  obtain ⟨x₂, y₂, h₂, rfl⟩ := eq_some_of_ne_zero W hQ
  exact (X_eq_iff (h₁ := h₁) (h₂ := h₂)).1 h

lemma eqn {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
  (equation_iff' _ _).1 h.1

/-- **the Kummer formulas**. -/
theorem kummer {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (Point.some _ _ h₁ + Point.some _ _ h₂ ≠ 0) ∧ (Point.some _ _ h₁ - Point.some _ _ h₂ ≠ 0) ∧
    (x₁ - x₂) ^ 2 * (xc W (Point.some _ _ h₁ + Point.some _ _ h₂) +
      xc W (Point.some _ _ h₁ - Point.some _ _ h₂)) = kS W x₁ x₂ ∧
    (x₁ - x₂) ^ 2 * (xc W (Point.some _ _ h₁ + Point.some _ _ h₂) *
      xc W (Point.some _ _ h₁ - Point.some _ _ h₂)) = kQ W x₁ x₂ := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  rw [sub_eq_add_neg, neg_some, add_of_X_ne hx, add_of_X_ne hx]
  refine ⟨some_ne_zero _, some_ne_zero _, ?_, ?_⟩ <;> simp only [xc_some]
  all_goals
    rw [slope_of_X_ne hx, slope_of_X_ne hx]
    set l := (y₁ - y₂) / (x₁ - x₂) with hl0
    set l' := (y₁ - W.toAffine.negY x₂ y₂) / (x₁ - x₂) with hl0'
    have hl : l * (x₁ - x₂) = y₁ - y₂ := by rw [hl0]; field_simp
    have hl' : l' * (x₁ - x₂) = y₁ + y₂ + W.a₁ * x₂ + W.a₃ := by
      rw [hl0', negY]; field_simp; ring
    have E1 := eqn W h₁
    have E2 := eqn W h₂
    have hX3 : (x₁ - x₂) ^ 2 * W.toAffine.addX x₁ x₂ l = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      rw [addX]; linear_combination (l * (x₁ - x₂) + (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * hl
    have hX4 : (x₁ - x₂) ^ 2 * W.toAffine.addX x₁ x₂ l' =
        (y₁ + y₂ + W.a₁ * x₂ + W.a₃) ^ 2 + W.a₁ * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      rw [addX]
      linear_combination (l' * (x₁ - x₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂)) * hl'
  · rw [mul_add, hX3, hX4, kS, b₂, b₄, b₆]
    linear_combination 2 * E1 + 2 * E2
  · apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    rw [← mul_assoc, show (x₁ - x₂) ^ 2 * (x₁ - x₂) ^ 2 * (W.toAffine.addX x₁ x₂ l * W.toAffine.addX x₁ x₂ l') =
      ((x₁ - x₂) ^ 2 * W.toAffine.addX x₁ x₂ l) * ((x₁ - x₂) ^ 2 * W.toAffine.addX x₁ x₂ l') by ring,
      hX3, hX4, kQ, b₄, b₆, b₈]
    linear_combination
      (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ - W.a₁ * W.a₃ * x₂ + W.a₁ * x₁ * y₁ -
        2 * W.a₁ * x₂ * y₂ - W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - 2 * W.a₂ * x₂ ^ 2 + W.a₃ * y₁ -
        2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆ - x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 +
        y₁ ^ 2 - 2 * y₂ ^ 2) * E1 +
      (-W.a₁ ^ 2 * x₁ ^ 2 + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ + W.a₁ * W.a₃ * x₂ + W.a₁ * x₂ * y₂ -
        4 * W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2 + W.a₃ * y₂ - 2 * W.a₄ * x₁ + W.a₄ * x₂ -
        W.a₆ - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * E2

/-- `(2y + a₁x + a₃)² = kPsi(x)` on the curve. -/
lemma sq_eq_kPsi {x y : F} (h : W.toAffine.Nonsingular x y) :
    (y - W.toAffine.negY x y) ^ 2 = kPsi W x := by
  have E := eqn W h
  rw [negY, kPsi, b₂, b₄, b₆]; linear_combination 4 * E

/-- **doubling**. -/
theorem doubling {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : Point.some _ _ h + Point.some _ _ h ≠ 0) :
    kPsi W x ≠ 0 ∧ kPsi W x * xc W (Point.some _ _ h + Point.some _ _ h) = kPhi W x := by
  have hy : y ≠ W.toAffine.negY x y := fun hy => h2 (add_self_of_Y_eq hy)
  have hd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.2 hy
  refine ⟨by rw [← sq_eq_kPsi W h]; exact pow_ne_zero 2 hd, ?_⟩
  rw [add_self_of_Y_ne hy, xc_some, slope_of_Y_ne rfl hy, ← sq_eq_kPsi W h]
  set l := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - W.toAffine.negY x y) with hl0
  have hl : l * (y - W.toAffine.negY x y) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hl0]; field_simp
  have E := eqn W h
  rw [addX, kPhi, b₄, b₆, b₈]
  rw [negY] at hl ⊢
  linear_combination (l * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
    W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl + (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x) * E

end HeightEll
