import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Basic

/-!
# Vélu: the local identity at a kernel point

Let `s` be nilpotent with `s⁶ = 0` (the local parameter `x - x₀` modulo `(x - x₀)⁶`).
Write Vélu's `X = φ₀ + R` near `x₀ = x(Q₀)` with `φ₀ = t₀/s + u₀/s²` and let
`R ≡ R₀ + R₁ s + R₂ s² + R₃ s³`. Then `s⁶ (f X'² - X³ - A' X - B')` vanishes modulo `s⁶`
as soon as the four scalar identities `h2 … h5` hold (`local_vanish`). These are verified for
the explicit values of `R₀ … R₃` forced by the group structure (`local_scalar_identities`).
-/

namespace Velu

/-- Abstract local vanishing in any commutative ring. -/
theorem local_vanish {𝔸 : Type*} [CommRing 𝔸] (x0 y0 A t R0 R1 R2 R3 Bp s : 𝔸)
    (hs : s ^ 6 = 0)
    (h2 : A^2 + 6*A*x0^2 + 4*R0*y0^2 + 9*x0^4 - 16*x0*y0^2 = 0)
    (h3 : A^3 + 9*A^2*x0^2 + 12*A*R0*y0^2 + 27*A*x0^4 - 24*A*x0*y0^2 + 36*R0*x0^2*y0^2 + 16*R1*y0^4 + 27*x0^6 - 72*x0^3*y0^2 - 16*y0^4 = 0)
    (h4 : -3*A^2*R0 + 3*A^2*x0 - 18*A*R0*x0^2 - 17*A*R1*y0^2 + 18*A*x0^3 + 7*A*y0^2 - 3*R0^2*y0^2 - 27*R0*x0^4 - 51*R1*x0^2*y0^2 - 20*R2*y0^4 + 5*t*y0^2 + 27*x0^5 + 24*x0^2*y0^2 = 0)
    (h5 : 8*A^2*R1 - A^2 + 3*A*R0^2 + 48*A*R1*x0^2 + 44*A*R2*y0^2 - 5*A*t - 9*A*x0^2 + 9*R0^2*x0^2 + 12*R0*R1*y0^2 + 72*R1*x0^4 + 24*R1*x0*y0^2 + 132*R2*x0^2*y0^2 + 48*R3*y0^4 - 15*t*x0^2 - 18*x0^4 = 0) :
    (y0 ^ 2 + (3 * x0 ^ 2 + A) * s + 3 * x0 * s ^ 2 + s ^ 3) *
        (-(2 * (3 * x0 ^ 2 + A) * s + 2 * (4 * y0 ^ 2)) +
          s ^ 3 * (R1 + 2 * R2 * s + 3 * R3 * s ^ 2)) ^ 2 -
      (2 * (3 * x0 ^ 2 + A) * s + 4 * y0 ^ 2 + s ^ 2 * (R0 + R1 * s + R2 * s ^ 2 + R3 * s ^ 3)) ^ 3 -
      (A - 5 * t) * s ^ 4 *
        (2 * (3 * x0 ^ 2 + A) * s + 4 * y0 ^ 2 + s ^ 2 * (R0 + R1 * s + R2 * s ^ 2 + R3 * s ^ 3)) -
      Bp * s ^ 6 = 0 := by
  linear_combination (-12*y0^2) * s^2 * h2 + (-4) * s^3 * h3 + (4) * s^4 * h4 + (-2) * s^5 * h5 + (-20*A^2*R2 - 24*A^2*R3*s - 12*A*R0*R1 - 12*A*R0*R2*s - 12*A*R0*R3*s^2 - A*R0 - 5*A*R1^2*s - 8*A*R1*R2*s^2 - 6*A*R1*R3*s^3 - 5*A*R1*s - 12*A*R1*x0 - 2*A*R2^2*s^3 - 9*A*R2*s^2 - 24*A*R2*s*x0 - 120*A*R2*x0^2 + 3*A*R3^2*s^5 - 13*A*R3*s^3 - 36*A*R3*s^2*x0 - 144*A*R3*s*x0^2 - 108*A*R3*y0^2 - Bp - R0^3 - 3*R0^2*R1*s - 3*R0^2*R2*s^2 - 3*R0^2*R3*s^3 - 3*R0*R1^2*s^2 - 6*R0*R1*R2*s^3 - 6*R0*R1*R3*s^4 - 36*R0*R1*x0^2 - 3*R0*R2^2*s^4 - 6*R0*R2*R3*s^5 - 36*R0*R2*s*x0^2 - 24*R0*R2*y0^2 - 3*R0*R3^2*s^6 - 36*R0*R3*s^2*x0^2 - 24*R0*R3*s*y0^2 + 5*R0*t - R1^3*s^3 - 3*R1^2*R2*s^4 - 3*R1^2*R3*s^5 + R1^2*s^3 + 3*R1^2*s^2*x0 - 15*R1^2*s*x0^2 - 11*R1^2*y0^2 - 3*R1*R2^2*s^5 - 6*R1*R2*R3*s^6 + 4*R1*R2*s^4 + 12*R1*R2*s^3*x0 - 24*R1*R2*s^2*x0^2 - 20*R1*R2*s*y0^2 - 3*R1*R3^2*s^7 + 6*R1*R3*s^5 + 18*R1*R3*s^4*x0 - 18*R1*R3*s^3*x0^2 - 18*R1*R3*s^2*y0^2 + 5*R1*s*t - 12*R1*s*x0^2 - 36*R1*x0^3 - 16*R1*y0^2 - R2^3*s^6 - 3*R2^2*R3*s^7 + 4*R2^2*s^5 + 12*R2^2*s^4*x0 - 6*R2^2*s^3*x0^2 - 8*R2^2*s^2*y0^2 - 3*R2*R3^2*s^8 + 12*R2*R3*s^6 + 36*R2*R3*s^5*x0 - 12*R2*R3*s^3*y0^2 + 5*R2*s^2*t - 24*R2*s^2*x0^2 - 72*R2*s*x0^3 - 32*R2*s*y0^2 - 180*R2*x0^4 - 96*R2*x0*y0^2 - R3^3*s^9 + 9*R3^2*s^7 + 27*R3^2*s^6*x0 + 9*R3^2*s^5*x0^2 - 3*R3^2*s^4*y0^2 + 5*R3*s^3*t - 36*R3*s^3*x0^2 - 108*R3*s^2*x0^3 - 48*R3*s^2*y0^2 - 216*R3*s*x0^4 - 144*R3*s*x0*y0^2 - 324*R3*x0^2*y0^2) * hs

/-- The scalar identities hold for the values of `R₀,…,R₃` forced by the group law:
with `λ = (3x₀² + A)/(2y₀)`, `x₂ = x(2Q₀)`, `y₂ = y(2Q₀)`. -/
theorem local_scalar_identities {K : Type*} [Field K] (x0 y0 A t R0 R1 R2 R3 x2 y2 : K)
    (hy : y0 ≠ 0) (h2 : (2 : K) ≠ 0)
    (hx2 : x2 = ((3 * x0 ^ 2 + A) / (2 * y0)) ^ 2 - 2 * x0)
    (hy2 : y2 = -(((3 * x0 ^ 2 + A) / (2 * y0)) * (x2 - x0) + y0))
    (hR0 : R0 = 2 * x0 - x2) (hR1 : R1 = -(y2 / y0))
    (hR2 : R2 = (t - (3 * x2 ^ 2 + A)) / (4 * y0 ^ 2) + y2 * (3 * x0 ^ 2 + A) / (4 * y0 ^ 3))
    (hR3 : R3 = -(t * (3 * x0 ^ 2 + A)) / (8 * y0 ^ 4) -
      (x2 * y2 / (2 * y0 ^ 3) - (3 * x2 ^ 2 + A) * (3 * x0 ^ 2 + A) / (8 * y0 ^ 4)
        - y2 * x0 / (2 * y0 ^ 3) + y2 * (3 * x0 ^ 2 + A) ^ 2 / (8 * y0 ^ 5))) :
    (A^2 + 6*A*x0^2 + 4*R0*y0^2 + 9*x0^4 - 16*x0*y0^2 = 0) ∧
    (A^3 + 9*A^2*x0^2 + 12*A*R0*y0^2 + 27*A*x0^4 - 24*A*x0*y0^2 + 36*R0*x0^2*y0^2 + 16*R1*y0^4 + 27*x0^6 - 72*x0^3*y0^2 - 16*y0^4 = 0) ∧
    (-3*A^2*R0 + 3*A^2*x0 - 18*A*R0*x0^2 - 17*A*R1*y0^2 + 18*A*x0^3 + 7*A*y0^2 - 3*R0^2*y0^2 - 27*R0*x0^4 - 51*R1*x0^2*y0^2 - 20*R2*y0^4 + 5*t*y0^2 + 27*x0^5 + 24*x0^2*y0^2 = 0) ∧
    (8*A^2*R1 - A^2 + 3*A*R0^2 + 48*A*R1*x0^2 + 44*A*R2*y0^2 - 5*A*t - 9*A*x0^2 + 9*R0^2*x0^2 + 12*R0*R1*y0^2 + 72*R1*x0^4 + 24*R1*x0*y0^2 + 132*R2*x0^2*y0^2 + 48*R3*y0^4 - 15*t*x0^2 - 18*x0^4 = 0) := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h2 h4
  subst hR0 hR1 hR2 hR3
  subst hy2
  subst hx2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (field_simp; ring)

end Velu
