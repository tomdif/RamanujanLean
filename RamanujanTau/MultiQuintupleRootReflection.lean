/-
# Short projective roots and reflective ternary lattices

Let `v = (i,j,k)` be isotropic modulo an odd modulus `p`, and let

  L_v = {x in Z^3 : v dot x = 0 (mod p)}.

Suppose that an integral vector `w` is a projective lift of `v` modulo `p` and has
square norm `e*p`, where `e` is `1` or `2`.  Then the Householder reflection in `w`
is integral on `L_v`: its coefficient is `c=2/e`, and `w congruent lambda*v (mod p)`
forces `p | x dot w` for every `x in L_v`.

This file proves that construction over `Z` without division.  It is the arithmetic
mechanism behind all reflective sparse-triple classes found in the exact census through
`p <= 401`.  The converse classification remains a conjecture; the implication proved
here is completely general and uses no primality assumption.
-/
import RamanujanTau.MultiQuintupleVanishing

namespace Ramanujan.MultiQuintuple

/-- Dot product on three integral coordinates. -/
def ternaryDot (a1 a2 a3 b1 b2 b3 : ℤ) : ℤ :=
  a1 * b1 + a2 * b2 + a3 * b3

/-- Euclidean square norm on three integral coordinates. -/
def ternaryNorm (a1 a2 a3 : ℤ) : ℤ :=
  a1 ^ 2 + a2 ^ 2 + a3 ^ 2

/-- One coordinate of the division-free Householder reflection.  If
`x dot w = p*t`, `w dot w = e*p`, and `c*e=2`, this is
`x - 2 (x dot w)/(w dot w) w`. -/
def shortRootReflectCoord (c t w x : ℤ) : ℤ :=
  x - c * t * w

/-- A projective lift turns every dot product with `w` into the corresponding
dot product with `v`, up to an explicit multiple of `p`. -/
theorem projectiveLift_dot
    (p lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 x1 x2 x3 : ℤ)
    (hw1 : w1 = lambda * v1 + p * a1)
    (hw2 : w2 = lambda * v2 + p * a2)
    (hw3 : w3 = lambda * v3 + p * a3) :
    ternaryDot x1 x2 x3 w1 w2 w3
      = lambda * ternaryDot x1 x2 x3 v1 v2 v3
          + p * ternaryDot x1 x2 x3 a1 a2 a3 := by
  simp only [ternaryDot]
  rw [hw1, hw2, hw3]
  ring

/-- Hence a projective lift has dot product divisible by `p` against every
point of the congruence lattice `L_v`. -/
theorem projectiveLift_dot_multiple
    (p lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 x1 x2 x3 s : ℤ)
    (hw1 : w1 = lambda * v1 + p * a1)
    (hw2 : w2 = lambda * v2 + p * a2)
    (hw3 : w3 = lambda * v3 + p * a3)
    (hx : ternaryDot x1 x2 x3 v1 v2 v3 = p * s) :
    ternaryDot x1 x2 x3 w1 w2 w3
      = p * (lambda * s + ternaryDot x1 x2 x3 a1 a2 a3) := by
  rw [projectiveLift_dot p lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 x1 x2 x3
    hw1 hw2 hw3, hx]
  ring

/-- If `v` is isotropic modulo `p`, then its projective lift `w` is itself in
the congruence lattice `L_v`. -/
theorem projectiveLift_is_in_lattice
    (p lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 h : ℤ)
    (hw1 : w1 = lambda * v1 + p * a1)
    (hw2 : w2 = lambda * v2 + p * a2)
    (hw3 : w3 = lambda * v3 + p * a3)
    (hisotropic : ternaryNorm v1 v2 v3 = p * h) :
    ternaryDot v1 v2 v3 w1 w2 w3
      = p * (lambda * h + ternaryDot v1 v2 v3 a1 a2 a3) := by
  rw [projectiveLift_dot p lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 v1 v2 v3
    hw1 hw2 hw3]
  have hsquares : v1 * v1 + v2 * v2 + v3 * v3 = p * h := by
    simpa only [ternaryNorm, pow_two] using hisotropic
  simp only [ternaryDot]
  rw [hsquares]
  ring

/-- The division-free Householder map preserves the Euclidean norm. -/
theorem shortRootReflect_preserves_norm
    (p e c t w1 w2 w3 x1 x2 x3 : ℤ)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hmultiple : ternaryDot x1 x2 x3 w1 w2 w3 = p * t)
    (hcoefficient : c * e = 2) :
    ternaryNorm
        (shortRootReflectCoord c t w1 x1)
        (shortRootReflectCoord c t w2 x2)
        (shortRootReflectCoord c t w3 x3)
      = ternaryNorm x1 x2 x3 := by
  have hzero :
      ternaryNorm
          (shortRootReflectCoord c t w1 x1)
          (shortRootReflectCoord c t w2 x2)
          (shortRootReflectCoord c t w3 x3)
        - ternaryNorm x1 x2 x3 = 0 := by
    calc
      ternaryNorm
          (shortRootReflectCoord c t w1 x1)
          (shortRootReflectCoord c t w2 x2)
          (shortRootReflectCoord c t w3 x3)
          - ternaryNorm x1 x2 x3
          = -2 * c * t * ternaryDot x1 x2 x3 w1 w2 w3
              + (c * t) ^ 2 * ternaryNorm w1 w2 w3 := by
                simp only [ternaryNorm, ternaryDot, shortRootReflectCoord]
                ring
      _ = -2 * c * t * (p * t) + (c * t) ^ 2 * (e * p) := by
            rw [hmultiple, hroot]
      _ = c * t ^ 2 * p * (-2 + c * e) := by ring
      _ = 0 := by rw [hcoefficient]; ring
  exact sub_eq_zero.mp hzero

/-- The reflected point has root pairing `-p*t`; this is the involutivity mechanism. -/
theorem shortRootReflect_flips_pairing
    (p e c t w1 w2 w3 x1 x2 x3 : ℤ)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hmultiple : ternaryDot x1 x2 x3 w1 w2 w3 = p * t)
    (hcoefficient : c * e = 2) :
    ternaryDot
        (shortRootReflectCoord c t w1 x1)
        (shortRootReflectCoord c t w2 x2)
        (shortRootReflectCoord c t w3 x3) w1 w2 w3 = -p * t := by
  calc
    ternaryDot
        (shortRootReflectCoord c t w1 x1)
        (shortRootReflectCoord c t w2 x2)
        (shortRootReflectCoord c t w3 x3) w1 w2 w3
        = ternaryDot x1 x2 x3 w1 w2 w3 - c * t * ternaryNorm w1 w2 w3 := by
            simp only [ternaryNorm, ternaryDot, shortRootReflectCoord]
            ring
    _ = p * t - c * t * (e * p) := by rw [hmultiple, hroot]
    _ = p * t * (1 - c * e) := by ring
    _ = -p * t := by rw [hcoefficient]; ring

/-- Applying the same reflection a second time (whose quotient is now `-t`) returns
each coordinate exactly. -/
theorem shortRootReflect_involutive (c t w x : ℤ) :
    shortRootReflectCoord c (-t) w (shortRootReflectCoord c t w x) = x := by
  simp [shortRootReflectCoord]

/-- The reflection preserves the defining congruence lattice.  The hypotheses expose
the two exact integer quotients, so no integer-division API is needed. -/
theorem shortRootReflect_preserves_lattice
    (p c t u s v1 v2 v3 w1 w2 w3 x1 x2 x3 : ℤ)
    (hx : ternaryDot v1 v2 v3 x1 x2 x3 = p * s)
    (hvw : ternaryDot v1 v2 v3 w1 w2 w3 = p * u) :
    ternaryDot v1 v2 v3
        (shortRootReflectCoord c t w1 x1)
        (shortRootReflectCoord c t w2 x2)
        (shortRootReflectCoord c t w3 x3)
      = p * (s - c * t * u) := by
  calc
    ternaryDot v1 v2 v3
        (shortRootReflectCoord c t w1 x1)
        (shortRootReflectCoord c t w2 x2)
        (shortRootReflectCoord c t w3 x3)
        = ternaryDot v1 v2 v3 x1 x2 x3
            - c * t * ternaryDot v1 v2 v3 w1 w2 w3 := by
              simp only [ternaryDot, shortRootReflectCoord]
              ring
    _ = p * s - c * t * (p * u) := by rw [hx, hvw]
    _ = p * (s - c * t * u) := by ring

/-- **Short-projective-root reflection theorem.**

An isotropic vector `v`, a projective lift `w`, and the short-root equation
`||w||^2=e*p` produce an integral, norm-preserving involution of `L_v`.  Taking
`(e,c)=(1,2)` or `(2,1)` gives the two root norms seen in the census. -/
theorem shortProjectiveRoot_reflection
    (p e c lambda v1 v2 v3 w1 w2 w3 a1 a2 a3 h
      x1 x2 x3 s : ℤ)
    (hw1 : w1 = lambda * v1 + p * a1)
    (hw2 : w2 = lambda * v2 + p * a2)
    (hw3 : w3 = lambda * v3 + p * a3)
    (hisotropic : ternaryNorm v1 v2 v3 = p * h)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hx : ternaryDot v1 v2 v3 x1 x2 x3 = p * s) :
    let t := lambda * s + ternaryDot x1 x2 x3 a1 a2 a3
    let u := lambda * h + ternaryDot v1 v2 v3 a1 a2 a3
    (ternaryDot x1 x2 x3 w1 w2 w3 = p * t)
      ∧ (ternaryDot v1 v2 v3 w1 w2 w3 = p * u)
      ∧ (ternaryNorm
          (shortRootReflectCoord c t w1 x1)
          (shortRootReflectCoord c t w2 x2)
          (shortRootReflectCoord c t w3 x3) = ternaryNorm x1 x2 x3)
      ∧ (ternaryDot v1 v2 v3
          (shortRootReflectCoord c t w1 x1)
          (shortRootReflectCoord c t w2 x2)
          (shortRootReflectCoord c t w3 x3) = p * (s - c * t * u))
      ∧ (ternaryDot
          (shortRootReflectCoord c t w1 x1)
          (shortRootReflectCoord c t w2 x2)
          (shortRootReflectCoord c t w3 x3) w1 w2 w3 = -p * t) := by
  dsimp only
  have hx' : ternaryDot x1 x2 x3 v1 v2 v3 = p * s := by
    simpa only [ternaryDot, mul_comm] using hx
  have hxt := projectiveLift_dot_multiple p lambda v1 v2 v3 w1 w2 w3
    a1 a2 a3 x1 x2 x3 s hw1 hw2 hw3 hx'
  have hvw := projectiveLift_is_in_lattice p lambda v1 v2 v3 w1 w2 w3
    a1 a2 a3 h hw1 hw2 hw3 hisotropic
  exact ⟨hxt, hvw,
    shortRootReflect_preserves_norm p e c
      (lambda * s + ternaryDot x1 x2 x3 a1 a2 a3) w1 w2 w3 x1 x2 x3
      hroot hxt hcoefficient,
    shortRootReflect_preserves_lattice p c
      (lambda * s + ternaryDot x1 x2 x3 a1 a2 a3)
      (lambda * h + ternaryDot v1 v2 v3 a1 a2 a3) s
      v1 v2 v3 w1 w2 w3 x1 x2 x3 hx hvw,
    shortRootReflect_flips_pairing p e c
      (lambda * s + ternaryDot x1 x2 x3 a1 a2 a3) w1 w2 w3 x1 x2 x3
      hroot hxt hcoefficient⟩

end Ramanujan.MultiQuintuple
