/-
# Entry 3.15(ii): the algebra (abstract commutative-ring lemmas)

Notation (in the application, `q = X`, `p k = χ(q^k)`, `m k = χ(−q^k)`, and `χ(−q^{2k}) = p k · m k`):
`L = G(q⁶)G(q¹⁴) + q⁴H(q⁶)H(q¹⁴)` is Entry 3.15's bracket at `q²`.

* `cramer1`/`cramer2` (Entries 3.8, 3.7 at `q²`, 3.10, 3.9 at `q²`, 3.2, at `q` and `−q`): the systems for `G(q⁶)`,
  `H(q⁶)` and `G(q¹⁴)`, `H(q¹⁴)` share the coefficient vectors, with determinant Entry 3.2, so
  `χ²(±q) L(q²)` is a sum of two eta quotients (`F1`, `F2`).
* `cramer3`/`cramer4`: the same for `L₂(q²) = G(q⁴²)H(q²) − q⁸G(q²)H(q⁴²)` (Entries 3.8 at `q⁷`, 3.7 at `q¹⁴`, 3.9,
  3.10 at `q²`, 3.2 at `q⁷`, at `q` and `−q`), with determinant Entry 3.2 at `±q⁷` (`F3`, `F4`).
* `cramer7` (Entries 3.10 and 3.2 at `±q`, 3.20, 3.9 at `q²`): the degree-7 equation
  `χ(q)χ(q⁷) − χ(−q)χ(−q⁷) = 2q/(χ(−q²)χ(−q¹⁴))` (`M7`).
* `alg15ii`: `F1`–`F4` and `M7` give `t·g·mo = 0` for the target `t = A(q) − A(−q) − 2qL`,
  `g = χ(−q³)χ³(−q⁷) − χ³(−q)χ(−q²¹)` and a monomial `mo` (certificate: Singular `lift`,
  `scripts/forty/round11/cert15b.sing`, emitted by `gen_alg.py`). The target alone is not in the ideal (dimension 5),
  so `g` is needed; it is nonzero because its coefficient of `q` is `3`.
-/
import Mathlib.Tactic

set_option autoImplicit false

namespace Forty

section Alg
variable {R : Type*} [CommRing R]

/-- Cramer at `q`: `L χ²(q) = bc + q a d`. -/
lemma cramer1 (q L G1 H1 G4 H4 G6 H6 G14 H14 p1 m1 p3 m3 p7 m7 : R)
    (hL : L = G6 * G14 + q ^ 4 * H6 * H14)
    (h8 : (G6 * H1 - q * G1 * H6) * m3 = m1)
    (h7 : (G4 * G6 + q ^ 2 * H4 * H6) * (p1 * m1) = p3 * m3)
    (h10 : (G1 * G14 + q ^ 3 * H1 * H14) * m1 = m7)
    (h9 : (G14 * H4 - q ^ 2 * G4 * H14) * (p7 * m7) = p1 * m1)
    (h2 : G1 * G4 + q * H1 * H4 = p1 ^ 2) :
    L * m1 ^ 2 * m3 * m7 * p1 ^ 3 * p7 - m1 ^ 4 * p1 ^ 2 * q - m3 ^ 2 * m7 ^ 2 * p3 * p7 = 0 := by
  subst hL
  linear_combination (-(G6 * G14 + q ^ 4 * H6 * H14) * (m1 * (p1 * m1) * m3 * (p7 * m7))) * h2
    + ((G1 * G14 + q ^ 3 * H1 * H14) * m1 * m3 * (p7 * m7)) * h7 + (p3 * m3 * m3 * (p7 * m7)) * h10
    + (q * (G14 * H4 - q ^ 2 * G4 * H14) * (p7 * m7) * m1 * (p1 * m1)) * h8 + (q * m1 * m1 * (p1 * m1)) * h9

/-- Cramer at `−q`: `L χ²(−q) = b c̃ − q ã d`. -/
lemma cramer2 (q L G1 H1 G4 H4 G6 H6 G14 H14 p1 m1 p3 m3 p7 m7 : R)
    (hL : L = G6 * G14 + q ^ 4 * H6 * H14)
    (h8 : (G6 * H1 + q * G1 * H6) * p3 = p1)
    (h7 : (G4 * G6 + q ^ 2 * H4 * H6) * (p1 * m1) = p3 * m3)
    (h10 : (G1 * G14 - q ^ 3 * H1 * H14) * p1 = p7)
    (h9 : (G14 * H4 - q ^ 2 * G4 * H14) * (p7 * m7) = p1 * m1)
    (h2 : G1 * G4 - q * H1 * H4 = m1 ^ 2) :
    L * m1 ^ 3 * m7 * p1 ^ 2 * p3 * p7 + m1 ^ 2 * p1 ^ 4 * q - m3 * m7 * p3 ^ 2 * p7 ^ 2 = 0 := by
  subst hL
  linear_combination (-(G6 * G14 + q ^ 4 * H6 * H14) * (p1 * (p1 * m1) * p3 * (p7 * m7))) * h2
    + ((G1 * G14 - q ^ 3 * H1 * H14) * p1 * p3 * (p7 * m7)) * h7 + (p3 * m3 * p3 * (p7 * m7)) * h10
    - (q * (G14 * H4 - q ^ 2 * G4 * H14) * (p7 * m7) * p1 * (p1 * m1)) * h8 - (q * p1 * p1 * (p1 * m1)) * h9

/-- Cramer for `L₂(q²)` at `q`. -/
lemma cramer3 (q L G2 H2 G7 H7 G28 H28 G42 H42 p1 m1 p7 m7 p21 m21 : R)
    (hL : L = G42 * H2 - q ^ 8 * G2 * H42)
    (h8 : (G42 * H7 - q ^ 7 * G7 * H42) * m21 = m7)
    (h7 : (G28 * G42 + q ^ 14 * H28 * H42) * (p7 * m7) = p21 * m21)
    (h9 : (G7 * H2 - q * G2 * H7) * m7 = m1)
    (h10 : (G2 * G28 + q ^ 6 * H2 * H28) * (p1 * m1) = p7 * m7)
    (h2 : G7 * G28 + q ^ 7 * H7 * H28 = p7 ^ 2) :
    L * m1 * m21 * m7 ^ 2 * p1 * p7 ^ 3 - m1 ^ 2 * m21 ^ 2 * p1 * p21 - m7 ^ 4 * p7 ^ 2 * q = 0 := by
  subst hL
  linear_combination (-(G42 * H2 - q ^ 8 * G2 * H42) * ((p7 * m7) * m7 * m21 * (p1 * m1))) * h2
    + ((G7 * H2 - q * G2 * H7) * m7 * m21 * (p1 * m1)) * h7 + (p21 * m21 * m21 * (p1 * m1)) * h9
    + (q * (G2 * G28 + q ^ 6 * H2 * H28) * (p1 * m1) * (p7 * m7) * m7) * h8 + (q * m7 * (p7 * m7) * m7) * h10

/-- Cramer for `L₂(q²)` at `−q`. -/
lemma cramer4 (q L G2 H2 G7 H7 G28 H28 G42 H42 p1 m1 p7 m7 p21 m21 : R)
    (hL : L = G42 * H2 - q ^ 8 * G2 * H42)
    (h8 : (G42 * H7 + q ^ 7 * G7 * H42) * p21 = p7)
    (h7 : (G28 * G42 + q ^ 14 * H28 * H42) * (p7 * m7) = p21 * m21)
    (h9 : (G7 * H2 + q * G2 * H7) * p7 = p1)
    (h10 : (G2 * G28 + q ^ 6 * H2 * H28) * (p1 * m1) = p7 * m7)
    (h2 : G7 * G28 - q ^ 7 * H7 * H28 = m7 ^ 2) :
    L * m1 * m7 ^ 3 * p1 * p21 * p7 ^ 2 - m1 * m21 * p1 ^ 2 * p21 ^ 2 + m7 ^ 2 * p7 ^ 4 * q = 0 := by
  subst hL
  linear_combination (-(G42 * H2 - q ^ 8 * G2 * H42) * ((p7 * m7) * p7 * p21 * (p1 * m1))) * h2
    + ((G7 * H2 + q * G2 * H7) * p7 * p21 * (p1 * m1)) * h7 + (p21 * m21 * p21 * (p1 * m1)) * h9
    - (q * (G2 * G28 + q ^ 6 * H2 * H28) * (p1 * m1) * (p7 * m7) * p7) * h8 - (q * p7 * (p7 * m7) * p7) * h10

/-- The degree-7 equation from Entries 3.10, 3.2 (at `±q`), 3.20 and 3.9 at `q²`. -/
lemma cramer7 (q G1 H1 Gn1 Hn1 G4 H4 G14 H14 p1 m1 p7 m7 : R)
    (h10 : (G1 * G14 + q ^ 3 * H1 * H14) * m1 = m7)
    (h10n : (Gn1 * G14 - q ^ 3 * Hn1 * H14) * p1 = p7)
    (h2 : G1 * G4 + q * H1 * H4 = p1 ^ 2)
    (h2n : Gn1 * G4 - q * Hn1 * H4 = m1 ^ 2)
    (h20 : (G1 * Hn1 + Gn1 * H1) * (p1 * m1) ^ 2 = 2)
    (h9 : (G14 * H4 - q ^ 2 * G4 * H14) * (p7 * m7) = p1 * m1) :
    -m1 ^ 2 * m7 ^ 2 * p1 * p7 + m1 * m7 * p1 ^ 2 * p7 ^ 2 - 2 * q = 0 := by
  linear_combination (-(p1 * m1 * p7 * m7) * p1) * h10n - (p1 * m1 * p7 * m7 * (Gn1 * G14 - q ^ 3 * Hn1 * H14)) * h2
    + (p1 * m1 * p7 * m7 * m1) * h10 + (p1 * m1 * p7 * m7 * (G1 * G14 + q ^ 3 * H1 * H14)) * h2n
    + (q * (G1 * Hn1 + Gn1 * H1) * (p1 * m1)) * h9 + q * h20

/-- The final elimination: `F1`–`F4` and `M7` force `t·g·mo = 0`. -/
lemma alg15ii (L p1 m1 p3 m3 p7 m7 p21 m21 q : R)
    (hF1 : L * m1 ^ 2 * m3 * m7 * p1 ^ 3 * p7 - m1 ^ 4 * p1 ^ 2 * q - m3 ^ 2 * m7 ^ 2 * p3 * p7 = 0)
    (hF2 : L * m1 ^ 3 * m7 * p1 ^ 2 * p3 * p7 + m1 ^ 2 * p1 ^ 4 * q - m3 * m7 * p3 ^ 2 * p7 ^ 2 = 0)
    (hF3 : L * m1 * m21 * m7 ^ 2 * p1 * p7 ^ 3 - m1 ^ 2 * m21 ^ 2 * p1 * p21 - m7 ^ 4 * p7 ^ 2 * q = 0)
    (hF4 : L * m1 * m7 ^ 3 * p1 * p21 * p7 ^ 2 - m1 * m21 * p1 ^ 2 * p21 ^ 2 + m7 ^ 2 * p7 ^ 4 * q = 0)
    (hM7 : -m1 ^ 2 * m7 ^ 2 * p1 * p7 + m1 * m7 * p1 ^ 2 * p7 ^ 2 - 2 * q = 0) :
    2 * ((-2 * L * q - m1 * m7 * p21 * p3 + m21 * m3 * p1 * p7) * (m3 * m7 ^ 3 - m1 ^ 3 * m21) *
      (p1 * m1 * p3 * m3 * p7 * m7 * p21 * m21 * q)) = 0 := by
  linear_combination
      (4*L^2*m21*m7*p1*p21*p3*p7^3*q - 2*L*m1*m21^2*m3*m7^2*p1*p21*p3*p7^3 + 2*L*m1*m7^5*p1*p21*p3*p7^3*q + 2*L*m21^2*m3*m7*p1^2*p21*p3*p7^4 + 4*L*m21*m7*p1^2*p21*p7*q^2 - 2*L*m7^4*p1^2*p21*p3*p7^4*q + 2*m1^3*m21^2*m7*p21*p3*p7^2*q - 2*m1^2*m21^3*m3*p1*p21^2*p3 - 2*m1^2*m21^2*p1*p21*p3*p7^3*q - m1^2*m21*m3*m7^6*p1*p21*p3*p7^3 + 2*m1^2*m21*m7^3*p1*p21^2*p3*q - 2*m1*m21^2*m3*m7^2*p1^2*p21*p7*q + 2*m1*m21*m3*m7^5*p1^2*p21*p3*p7^4 - 2*m1*m21*m7^2*p1^2*p21^2*p3*p7*q + 2*m1*m7^5*p1^2*p21*p7*q^2 - 2*m21^2*m3*m7*p21^2*p3^2*p7^2 - 2*m21^2*m3*m7*p3*p7^5*q - m21*m3*m7^4*p1^3*p21*p3*p7^5 - 4*m21*m3*m7^4*p21*p3*p7^2*q - 2*m7^4*p1^3*p21*p7^2*q^2) * hF1 +
      (-4*L^2*m21*m3*m7^2*p1*p21*p7^2*q + 4*L*m1^2*m21*m7*p21*p7*q^2 + 2*L*m1*m21^2*m3^2*m7^3*p1*p21*p7^2 - 2*L*m1*m3*m7^6*p1*p21*p7^2*q - 2*L*m21^2*m3^2*m7^2*p1^2*p21*p7^3 + 2*L*m3*m7^5*p1^2*p21*p7^3*q - 2*m1^3*m21^2*m3*m7^2*p21*p7*q + 2*m1^3*m7^5*p21*p7*q^2 + m1^2*m21*m3^2*m7^7*p1*p21*p7^2 - 2*m1^2*m7^4*p1*p21*p7^2*q^2 + 2*m1*m21^3*m3^2*p1^2*p21^2 - 2*m1*m21*m3^2*m7^6*p1^2*p21*p7^3 + 2*m21^2*m3^2*m7^2*p21^2*p3*p7 + m21*m3^2*m7^5*p1^3*p21*p7^4 + 2*m21*m3^2*m7^5*p21*p7*q) * hF2 +
      (-4*L^2*m1*m3*p1^3*p21*p3*p7*q - 2*L*m1^5*m7*p1^3*p21*p3*p7*q + 2*L*m1^4*p1^4*p21*p3*p7^2*q + 2*L*m1^2*m21*m3^2*m7*p1^3*p21*p3*p7 - 2*L*m1*m21*m3^2*p1^4*p21*p3*p7^2 - 4*L*m1*m3*p1*p3*p7^2*q^2 + m1^6*m21*m3*m7^2*p1^3*p21*p3*p7 - 2*m1^5*m21*m3*m7*p1^4*p21*p3*p7^2 - 2*m1^5*m7*p1*p3*p7^2*q^2 + m1^4*m21*m3*p1^5*p21*p3*p7^3 + 4*m1^4*m21*m3*p1^2*p21*p3*q + 2*m1^4*p1^2*p3*p7^3*q^2 - 2*m1^3*m3*m7^2*p21*p3^2*p7*q + 2*m1^2*m21*m3^2*m7*p1*p3*p7^2*q + 2*m1^2*m3*m7*p1*p21*p3^2*p7^2*q + 2*m1*m21*m3^2*p1^5*p21*q + 2*m1*m21*m3^2*p1^2*p21^2*p3^2 - 2*m1*m3^2*m7^3*p1^2*p21*p3*q + 2*m21*m3^3*m7^2*p21*p3^2*p7 + 2*m3^2*m7^2*p1^3*p21*p3*p7*q) * hF3 +
      (4*L^2*m1^2*m21*m3*p1^2*p3*p7*q + 2*L*m1^6*m21*m7*p1^2*p3*p7*q - 2*L*m1^5*m21*p1^3*p3*p7^2*q - 2*L*m1^3*m21^2*m3^2*m7*p1^2*p3*p7 + 2*L*m1^2*m21^2*m3^2*p1^3*p3*p7^2 - 4*L*m1*m3*m7^2*p1*p3*q^2 - m1^7*m21^2*m3*m7^2*p1^2*p3*p7 + 2*m1^6*m21^2*m3*m7*p1^3*p3*p7^2 - m1^5*m21^2*m3*p1^4*p3*p7^3 - 2*m1^5*m21^2*m3*p1*p3*q - 2*m1^5*m7^3*p1*p3*q^2 + 2*m1^4*m7^2*p1^2*p3*p7*q^2 - 2*m1^2*m21^2*m3^2*p1*p21*p3^2 + 2*m1^2*m21*m3^2*m7^3*p1*p3*q - 2*m21^2*m3^3*m7*p3^2*p7^2) * hF4 +
      (2*L^2*m1^5*m21*m7^2*p1^2*p21*p3*p7^2*q - 2*L^2*m1^4*m21*m7*p1^3*p21*p3*p7^3*q - 2*L^2*m1^2*m3*m7^5*p1^2*p21*p3*p7^2*q + 2*L^2*m1*m3*m7^4*p1^3*p21*p3*p7^3*q - L*m1^6*m21^2*m3*m7^3*p1^2*p21*p3*p7^2 + 2*L*m1^5*m21^2*m3*m7^2*p1^3*p21*p3*p7^3 - L*m1^4*m21^2*m3*m7*p1^4*p21*p3*p7^4 - 2*L*m1^4*m21^2*m3*m7*p1*p21*p3*p7*q + 2*L*m1^3*m21^2*m3*p1^2*p21*p3*p7^2*q + L*m1^3*m21*m3^2*m7^6*p1^2*p21*p3*p7^2 - 2*L*m1^2*m21*m3^2*m7^5*p1^3*p21*p3*p7^3 + 2*L*m1^2*m21*m3*m7^2*p1^3*p21^2*p3*q - 2*L*m1^2*m21*m3*m7^2*p21*p3^2*p7^3*q + L*m1*m21*m3^2*m7^4*p1^4*p21*p3*p7^4 + 2*L*m1*m21*m3^2*m7^4*p1*p21*p3*p7*q - 2*L*m21*m3^2*m7^3*p1^2*p21*p3*p7^2*q - m1^5*m21^2*m3*m7^2*p1*p3*p7^4*q + m1^4*m21^2*m3*m7*p1^2*p3*p7^5*q + m1^2*m21*m3^2*m7^5*p1^4*p21*p7*q - m1*m21*m3^2*m7^4*p1^5*p21*p7^2*q) * hM7

end Alg

end Forty
