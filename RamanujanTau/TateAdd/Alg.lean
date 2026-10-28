/-
# Algebraic core of the Tate addition theorem

Short Weierstrass curve `Y² = X³ + A X + B`. A derivation `D` acting on a point `P₁ = (X₁, Y₁)` as the
invariant vector field (`DX₁ = 2Y₁`, `DY₁ = 3X₁² + A`) and on a second point
`P₂ = (x₂/t², y₂/t³)` as minus the invariant vector field (written for the pole-cleared coordinates
`x₂ = t² X₂`, `y₂ = t³ Y₂`, with `Dt` arbitrary) leaves the chord sum `P₁ + P₂` fixed
(translation invariance of the invariant differential). We record this with all derivatives as
explicit field elements (`invX`, `invY`); certificates found by computer algebra.

`chord_reg`: if `x₂ = (1+t) + t²/12 + t⁴e`, `y₂ = (−(1+t)(2+t) + t⁴f)/2` (a point near the origin
`O`), the chord numerator is divisible by `t³` (the sum `P₁ + P₂` is regular at `t = 0`).
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Basic

set_option autoImplicit false

namespace TateAdd

variable {F : Type*} [CommRing F] [IsDomain F]

/-- **Translation invariance, `x`-coordinate.** -/
theorem invX (t dt X1 Y1 x2 y2 A B Xc dX1 dY1 dx2 dy2 dXc : F)
    (hdX1 : dX1 = 2 * Y1) (hdY1 : dY1 = 3 * X1 ^ 2 + A)
    (hdx2 : t * dx2 = 2 * dt * x2 - 2 * y2)
    (hdy2 : t * dy2 = 3 * dt * y2 - 3 * x2 ^ 2 - A * t ^ 4)
    (hC1 : Y1 ^ 2 = X1 ^ 3 + A * X1 + B) (hC2 : y2 ^ 2 = x2 ^ 3 + A * t ^ 4 * x2 + B * t ^ 6)
    (hE : t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * Xc =
      (y2 - t ^ 3 * Y1) ^ 2 - t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * X1 - (x2 - t ^ 2 * X1) ^ 2 * x2)
    (hDE : 2 * t * dt * (x2 - t ^ 2 * X1) ^ 2 * Xc +
        t ^ 2 * (2 * (x2 - t ^ 2 * X1) * (dx2 - 2 * t * dt * X1 - t ^ 2 * dX1)) * Xc +
        t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * dXc =
      2 * (y2 - t ^ 3 * Y1) * (dy2 - 3 * t ^ 2 * dt * Y1 - t ^ 3 * dY1) -
        (2 * t * dt * (x2 - t ^ 2 * X1) ^ 2 * X1 +
          t ^ 2 * (2 * (x2 - t ^ 2 * X1) * (dx2 - 2 * t * dt * X1 - t ^ 2 * dX1)) * X1 +
          t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * dX1) -
        (2 * (x2 - t ^ 2 * X1) * (dx2 - 2 * t * dt * X1 - t ^ 2 * dX1) * x2 +
          (x2 - t ^ 2 * X1) ^ 2 * dx2))
    (ht : t ≠ 0) (hDl : x2 - t ^ 2 * X1 ≠ 0) : dXc = 0 := by
  have key : t ^ 5 * (x2 - t ^ 2 * X1) ^ 4 * dXc = 0 := by
    linear_combination (t^5*(-X1*t^2 + x2)^3*(3*X1*t^2 + 2*Xc*t^2 + x2)) * hdX1 +
      (-2*t^6*(-X1*t^2 + x2)^2*(-Y1*t^3 + y2)) * hdY1 +
      (-t^2*(-X1*t^2 + x2)^3*(X1*t^2 + 2*Xc*t^2 + 3*x2)) * hdx2 +
      (2*t^2*(-X1*t^2 + x2)^2*(-Y1*t^3 + y2)) * hdy2 +
      (-2*t^2*(-X1*t^2 + x2)*(-3*X1*dt*t^2 - 2*Y1*t^3 + 3*dt*x2 - 2*y2)) * hE +
      (-4*t^8*(-X1*t^2 + x2)*(-Y1*t^3 + y2)) * hC1 +
      (4*t^2*(-X1*t^2 + x2)*(-Y1*t^3 + y2)) * hC2 + (t^3*(-X1*t^2 + x2)^2) * hDE
  simpa [ht, hDl] using key

/-- **Translation invariance, `y`-coordinate** (given `D Xc = 0`). -/
theorem invY (t dt X1 Y1 x2 y2 A B Xc Yc dX1 dY1 dx2 dy2 dYc : F)
    (hdX1 : dX1 = 2 * Y1) (hdY1 : dY1 = 3 * X1 ^ 2 + A)
    (hdx2 : t * dx2 = 2 * dt * x2 - 2 * y2)
    (hdy2 : t * dy2 = 3 * dt * y2 - 3 * x2 ^ 2 - A * t ^ 4)
    (hC1 : Y1 ^ 2 = X1 ^ 3 + A * X1 + B) (hC2 : y2 ^ 2 = x2 ^ 3 + A * t ^ 4 * x2 + B * t ^ 6)
    (hE : t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * Xc =
      (y2 - t ^ 3 * Y1) ^ 2 - t ^ 2 * (x2 - t ^ 2 * X1) ^ 2 * X1 - (x2 - t ^ 2 * X1) ^ 2 * x2)
    (hF : t * (x2 - t ^ 2 * X1) * (Yc + Y1) + (y2 - t ^ 3 * Y1) * (Xc - X1) = 0)
    (hDF : dt * (x2 - t ^ 2 * X1) * (Yc + Y1) +
        t * (dx2 - 2 * t * dt * X1 - t ^ 2 * dX1) * (Yc + Y1) +
        t * (x2 - t ^ 2 * X1) * (dYc + dY1) +
        (dy2 - 3 * t ^ 2 * dt * Y1 - t ^ 3 * dY1) * (Xc - X1) + (y2 - t ^ 3 * Y1) * (0 - dX1) = 0)
    (ht : t ≠ 0) (hDl : x2 - t ^ 2 * X1 ≠ 0) : dYc = 0 := by
  have key : t ^ 5 * (x2 - t ^ 2 * X1) ^ 4 * dYc = 0 := by
    linear_combination (t^4*(-X1*t^2 + x2)^3*(Yc*t^3 + y2)) * hdX1 +
      (-t^5*(-X1*t^2 + x2)^3*(-Xc*t^2 + x2)) * hdY1 +
      (-t^4*(Y1 + Yc)*(-X1*t^2 + x2)^3) * hdx2 + (t^3*(X1 - Xc)*(-X1*t^2 + x2)^3) * hdy2 +
      (-t^3*(-X1*t^2 + x2)^2*(-3*X1*dt*t^2 - 2*Y1*t^3 + 3*dt*x2 - 2*y2)) * hF +
      (t*(-2*A*X1*t^6 + 2*A*t^4*x2 - 3*X1^3*t^6 + 3*X1^2*t^4*x2 - 3*X1*t^2*x2^2 + 2*Y1^2*t^6 +
        3*x2^3 - 2*y2^2)) * hE +
      (-t^7*(-2*A*t^4*x2 - 2*B*t^6 + 3*X1^3*t^6 - 3*X1^2*t^4*x2 - 3*X1*t^2*x2^2 - 2*Y1^2*t^6 +
        4*Y1*t^3*y2 + x2^3)) * hC1 +
      (t*(-2*A*X1*t^6 - 2*B*t^6 + X1^3*t^6 - 3*X1^2*t^4*x2 - 3*X1*t^2*x2^2 + 4*Y1*t^3*y2 +
        3*x2^3 - 2*y2^2)) * hC2 + (t^4*(-X1*t^2 + x2)^3) * hDF
  simpa [ht, hDl] using key

/-- the regular part of the chord numerator (model scaled by `u = 6`). -/
def Rt {R : Type*} [CommRing R] (t X1 Y1 e f : R) : R :=
  -2*X1^3*t^3 + 108*X1^2*e*t^5 + 9*X1^2*t^3 + 108*X1^2*t^2 + 108*X1^2*t + Y1^2*t^3 -
    216*Y1*f*t^4 + 216*Y1*t^2 + 648*Y1*t + 432*Y1 - 46656*e^3*t^9 - 11664*e^2*t^7 -
    139968*e^2*t^6 - 139968*e^2*t^5 - 972*e*t^5 - 23328*e*t^4 - 163296*e*t^3 - 279936*e*t^2 -
    139968*e*t + 11664*f^2*t^5 - 23328*f*t^3 - 69984*f*t^2 - 46656*f*t - 27*t^3 - 972*t^2 - 972*t

/-- `Rt` at `t = 0`. -/
lemma Rt_zero {R : Type*} [CommRing R] (X1 Y1 e f : R) : Rt 0 X1 Y1 e f = 432 * Y1 := by
  simp [Rt]

/-- **Regularity of the chord sum at the origin** (scaled model: `x₂ = 36(1+t) + 3t² + 36t⁴e`,
`y₂ = 108(−(1+t)(2+t) + t⁴f)`). -/
theorem chord_reg {R : Type*} [CommRing R] (t X1 Y1 e f : R) :
    (108 * (-((1 + t) * (2 + t)) + t ^ 4 * f) - t ^ 3 * Y1) ^ 2 -
      2 * t ^ 2 * (36 * (1 + t) + 3 * t ^ 2 + 36 * t ^ 4 * e - t ^ 2 * X1) ^ 2 * X1 -
      (36 * (1 + t) + 3 * t ^ 2 + 36 * t ^ 4 * e - t ^ 2 * X1) ^ 2 *
        (36 * (1 + t) + 3 * t ^ 2 + 36 * t ^ 4 * e) = t ^ 3 * Rt t X1 Y1 e f := by
  simp only [Rt]
  ring

end TateAdd
