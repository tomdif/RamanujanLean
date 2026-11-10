/-
# Entry 3.28(ii): the algebraic glue of Yesilyurt's (3.1)–(3.6), in an abstract integral domain

Same variables as `E28d.lean` (`c = a1a2 = χ(−q²)`, `d = b1b2 = χ(−Q²)`, `c4 = e1c = χ(−q⁴)`, `d4 = e2d`,
`c8 = g1c4 = χ(−q⁸)`, `d8 = g2d4`, `g1 = χ(q⁴)`, `g2 = χ(Q⁴)`). Every certificate below is checked by sympy in
`scripts/forty/round9/glue.py`.
-/
import Mathlib

set_option autoImplicit false

namespace Forty

variable {R : Type*} [CommRing R] [IsDomain R]

/-- (3.13) + (1.4) ⟹ (3.1): `c d b2 U = b1 d − q² a1 c`. -/
theorem glue1 (q a1 a2 b1 b2 U V : R) (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0)
    (hA : a2 ^ 2 * (a1 * a2) * b2 * (b1 * b2) * V = a2 * (b1 * b2) ^ 2 - q ^ 2 * b2 * (a1 * a2) ^ 2)
    (h14 : U * b2 = V * a2) :
    a1 * a2 * (b1 * b2) * b2 * U = b1 * (b1 * b2) - q ^ 2 * a1 * (a1 * a2) := by
  apply mul_left_cancel₀ (mul_ne_zero ha2 hb2)
  linear_combination (a2 * b2 * (a1 * a2) * (b1 * b2)) * h14 + hA

/-- (3.15) + (3.13) at `±q` + (1.4) at `q²` ⟹ (3.2): `2q V(q²) = d (a1 b2 − a2 b1)`. -/
theorem glue2 (q a1 a2 b1 b2 V Vm Uq Vq : R) (hc : a1 * a2 ≠ 0) (hd : b1 * b2 ≠ 0)
    (hA : a2 ^ 2 * (a1 * a2) * b2 * (b1 * b2) * V = a2 * (b1 * b2) ^ 2 - q ^ 2 * b2 * (a1 * a2) ^ 2)
    (hAm : a1 ^ 2 * (a1 * a2) * b1 * (b1 * b2) * Vm = a1 * (b1 * b2) ^ 2 - q ^ 2 * b1 * (a1 * a2) ^ 2)
    (h15 : 2 * q * Uq = (a1 * a2) ^ 2 * (Vm * a1 ^ 2 - V * a2 ^ 2))
    (h14q : Uq * (b1 * b2) = Vq * (a1 * a2)) :
    2 * q * Vq = b1 * b2 * (a1 * b2 - a2 * b1) := by
  apply mul_left_cancel₀ (mul_ne_zero hc (pow_ne_zero 2 hd))
  linear_combination (-2 * q * (b1 * b2) ^ 2) * h14q + (b1 * b2) ^ 3 * h15 + ((a1 * a2) * (b1 * b2) * b2) * hAm
    - ((a1 * a2) * (b1 * b2) * b1) * hA

/-- (3.21) + (1.4) ⟹ (3.3): `d U(q)U(−q) c4 d4 = e2 d4 + q⁴ e1 c4`. -/
theorem glue3 (q a1 a2 b1 b2 e1 e2 U Um V Vm : R) (hc : a1 * a2 ≠ 0) (hd : b1 * b2 ≠ 0)
    (hB : (a1 * a2) ^ 2 * (e1 * (a1 * a2)) * (b1 * b2) * (e2 * (b1 * b2)) * (V * Vm) =
      a1 * a2 * (e2 * (b1 * b2)) ^ 2 + q ^ 4 * (b1 * b2) * (e1 * (a1 * a2)) ^ 2)
    (h14 : U * b2 = V * a2) (h14m : Um * b1 = Vm * a1) :
    b1 * b2 * U * Um * (e1 * (a1 * a2)) * (e2 * (b1 * b2)) = e2 * (e2 * (b1 * b2)) + q ^ 4 * e1 * (e1 * (a1 * a2)) := by
  apply mul_left_cancel₀ (mul_ne_zero hc hd)
  linear_combination ((a1 * a2) * (b1 * b2) * (e1 * (a1 * a2)) * (e2 * (b1 * b2))) * ((Um * b1) * h14 + (V * a2) * h14m)
    + hB

/-- (3.3) + (3.1) at `q²` ⟹ (3.5): `(S(q)S(−q) − S(q²)) T(q²) = 4q⁴`. -/
theorem alg5 (q a1 a2 b1 b2 e1 e2 U Um V Vm Uq Vq : R) (hc : a1 * a2 ≠ 0) (hd : b1 * b2 ≠ 0)
    (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (h14 : U * b2 = V * a2) (h14m : Um * b1 = Vm * a1) (h14q : Uq * (b1 * b2) = Vq * (a1 * a2))
    (h3 : b1 * b2 * U * Um * (e1 * (a1 * a2)) * (e2 * (b1 * b2)) = e2 * (e2 * (b1 * b2)) + q ^ 4 * e1 * (e1 * (a1 * a2)))
    (h1q2 : e1 * (a1 * a2) * (e2 * (b1 * b2)) * (b1 * b2) * Uq = e2 * (e2 * (b1 * b2)) - q ^ 4 * e1 * (e1 * (a1 * a2))) :
    (U * V * (Um * Vm) - Uq * Vq) * (a1 * a2 * (b1 * b2)) ^ 2 = 4 * q ^ 4 := by
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc hd) (mul_ne_zero (pow_ne_zero 2 he1) (pow_ne_zero 2 he2)))
  linear_combination (b1 * b2 * U * Um * (e1 * (a1 * a2)) * (e2 * (b1 * b2)) + e2 * (e2 * (b1 * b2))
      + q ^ 4 * e1 * (e1 * (a1 * a2))) * h3
    - (e1 * (a1 * a2) * (e2 * (b1 * b2)) * (b1 * b2) * Uq + e2 * (e2 * (b1 * b2)) - q ^ 4 * e1 * (e1 * (a1 * a2))) * h1q2
    + (b1 * b2) * (e1 * (a1 * a2)) ^ 2 * (e2 * (b1 * b2)) ^ 2 * (-(U * Um) * ((Um * b1) * h14 + (V * a2) * h14m) + Uq * h14q)

/-- (3.2) + (3.4) ⟹ the product of (3.27) and its `q ↦ −q` image (his (3.28)): `W² − q²V(q²)² = d³c`. -/
theorem alg27 (q a1 a2 b1 b2 Vq W : R) (h4ne : (4 : R) ≠ 0)
    (h2 : 2 * q * Vq = b1 * b2 * (a1 * b2 - a2 * b1)) (h4 : 2 * W = b1 * b2 * (a1 * b2 + a2 * b1)) :
    W ^ 2 - q ^ 2 * Vq ^ 2 = (b1 * b2) ^ 3 * (a1 * a2) := by
  apply mul_left_cancel₀ h4ne
  linear_combination (2 * W - 2 * q * Vq) * (h4 + h2) + 2 * (b1 * b2) * a1 * b2 * (h4 - h2)

/-- (3.28) pulled back + (1.4) ⟹ (3.6): `S(−q)S(q²) − qS(q) = χ²(−q)χ²(−Q)`. -/
theorem alg6 (q a1 a2 b1 b2 U Um V Vm Uq Vq : R) (ha1 : a1 ≠ 0) (hb2 : b2 ≠ 0) (hd : b1 * b2 ≠ 0)
    (h14 : U * b2 = V * a2) (h14m : Um * b1 = Vm * a1) (h14q : Uq * (b1 * b2) = Vq * (a1 * a2))
    (P28 : (Um * Vq) ^ 2 - q * V ^ 2 = b2 ^ 3 * a2) :
    Um * Vm * (Uq * Vq) - q * (U * V) = a2 ^ 2 * b2 ^ 2 := by
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero ha1 hb2) hd)
  linear_combination (a1 * a2 * (b1 * b2)) * P28 + b2 * Um * Vq * (-(Uq * (b1 * b2)) * h14m + Um * b1 * h14q)
    - a1 * (b1 * b2) * q * V * h14

/-- (3.3) at `q²`, (3.1) at `q⁴`, (3.23) at `q` and `Q`, (3.2), (1.4) ⟹ (3.4): `2U(−q²)V(q⁴) = d(a1b2 + a2b1)`. -/
theorem alg4 (q a1 a2 b1 b2 e1 e2 g1 g2 Uq Vq Um2 U4 V4 : R) (hq : q ≠ 0) (hc : a1 * a2 ≠ 0)
    (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (hd : b1 * b2 ≠ 0) (hVq : Vq ≠ 0) (h2ne : (2 : R) ≠ 0)
    (h3q2 : e2 * (b1 * b2) * Uq * Um2 * (g1 * (e1 * (a1 * a2))) * (g2 * (e2 * (b1 * b2))) =
      g2 * (g2 * (e2 * (b1 * b2))) + q ^ 8 * g1 * (g1 * (e1 * (a1 * a2))))
    (h1q4 : g1 * (e1 * (a1 * a2)) * (g2 * (e2 * (b1 * b2))) * (e2 * (b1 * b2)) * U4 =
      g2 * (g2 * (e2 * (b1 * b2))) - q ^ 8 * g1 * (g1 * (e1 * (a1 * a2))))
    (j1 : 2 * g1 ^ 2 = a1 * a2 * (e1 * (a1 * a2)) * (a1 ^ 2 + a2 ^ 2))
    (j2 : 4 * q = a1 * a2 * (e1 * (a1 * a2)) * (g1 * (e1 * (a1 * a2))) ^ 2 * (a1 ^ 2 - a2 ^ 2))
    (j3 : 2 * g2 ^ 2 = b1 * b2 * (e2 * (b1 * b2)) * (b1 ^ 2 + b2 ^ 2))
    (j4 : 4 * q ^ 17 = b1 * b2 * (e2 * (b1 * b2)) * (g2 * (e2 * (b1 * b2))) ^ 2 * (b1 ^ 2 - b2 ^ 2))
    (h14q : Uq * (b1 * b2) = Vq * (a1 * a2)) (h14q4 : U4 * (e2 * (b1 * b2)) = V4 * (e1 * (a1 * a2)))
    (h2 : 2 * q * Vq = b1 * b2 * (a1 * b2 - a2 * b1)) :
    2 * (Um2 * V4) = b1 * b2 * (a1 * b2 + a2 * b1) := by
  have P0 : (e2 * (b1 * b2)) ^ 2 * (g1 * (e1 * (a1 * a2))) ^ 2 * (g2 * (e2 * (b1 * b2))) ^ 2 * (Uq * Um2 * U4) =
      g2 ^ 2 * (g2 * (e2 * (b1 * b2))) ^ 2 - q ^ 16 * g1 ^ 2 * (g1 * (e1 * (a1 * a2))) ^ 2 := by
    linear_combination (g1 * (e1 * (a1 * a2)) * (g2 * (e2 * (b1 * b2))) * (e2 * (b1 * b2)) * U4) * h3q2
      + (g2 * (g2 * (e2 * (b1 * b2))) + q ^ 8 * g1 * (g1 * (e1 * (a1 * a2)))) * h1q4
  have h8 : (8 : R) ≠ 0 := by
    have : (8 : R) = 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2ne h2ne) h2ne
  have K1 : 4 * q * (e2 * (b1 * b2)) * (Uq * Um2 * U4) =
      a1 * a2 * (e1 * (a1 * a2)) * (b1 * b2) * (a1 ^ 2 * b2 ^ 2 - a2 ^ 2 * b1 ^ 2) := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h8 (pow_ne_zero 17 hq)) (mul_ne_zero he2 hd))
    linear_combination 2 * ((a1 * a2) * (e1 * (a1 * a2)) * (a1 ^ 2 - a2 ^ 2)) * ((b1 * b2) * (e2 * (b1 * b2)) * (b1 ^ 2 - b2 ^ 2)) * P0
      + 2 * (e2 * (b1 * b2)) ^ 2 * (Uq * Um2 * U4) * (((b1 * b2) * (e2 * (b1 * b2)) * (g2 * (e2 * (b1 * b2))) ^ 2 * (b1 ^ 2 - b2 ^ 2)) * j2 + 4 * q * j4)
      - 2 * g2 ^ 2 * ((a1 * a2) * (e1 * (a1 * a2)) * (a1 ^ 2 - a2 ^ 2)) * j4
      + 2 * q ^ 16 * g1 ^ 2 * ((b1 * b2) * (e2 * (b1 * b2)) * (b1 ^ 2 - b2 ^ 2)) * j2
      + 4 * q ^ 17 * ((a1 * a2) * (e1 * (a1 * a2)) * (a1 ^ 2 - a2 ^ 2)) * j3
      - 4 * q ^ 17 * ((b1 * b2) * (e2 * (b1 * b2)) * (b1 ^ 2 - b2 ^ 2)) * j1
  have K2 : 4 * q * Vq * (Um2 * V4) = (b1 * b2) ^ 2 * (a1 * b2 - a2 * b1) * (a1 * b2 + a2 * b1) := by
    apply mul_left_cancel₀ (mul_ne_zero hc (mul_ne_zero he1 hc))
    linear_combination (b1 * b2) * K1 - 4 * q * Um2 * (U4 * (e2 * (b1 * b2))) * h14q
      - 4 * q * Um2 * Vq * (a1 * a2) * h14q4
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h2ne hq) hVq)
  linear_combination K2 - (b1 * b2) * (a1 * b2 + a2 * b1) * h2

end Forty
