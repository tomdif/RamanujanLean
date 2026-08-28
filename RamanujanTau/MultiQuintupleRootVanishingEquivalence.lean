/-
# The projective-root interface for Root--Vanishing Equivalence

The direct-root cancellation theorem uses the same vector both as the three
quintuple indices and as the Householder normal.  A genuinely projective root
has instead

  `w = lambda * v + p * a`.

This file proves the missing arithmetic transport law.  For a branch point in
coefficient residue `r`, its completed-square pairing with `w` is governed by

  `2*lambda*r - sum(w) + 6*(v dot w / p)`.

That expression gives the uniform target residue for a projective root.  It
specializes to the old direct-root formula when `w=v`, `lambda=1`, and
`v dot w / p=e`.

The file closes the forward Root--Vanishing direction for arbitrary projective
short roots.  It constructs all eight target branches in both mod-three norm
classes, lifts them to sign-reversing involutions of the actual finite
coefficient support, and proves the resulting full coefficient progressions
zero.  The converse assertion that every bare coefficient vanishing must arise
from a reflective mechanism is deliberately not asserted: accidental or
non-Householder cancellation must first be excluded by a separate rigidity
theorem.
-/
import RamanujanTau.MultiQuintupleProjectiveCancellation

namespace Ramanujan.MultiQuintuple
open PowerSeries

set_option maxRecDepth 10000

/-- The correction contributed by the integral displacement in a projective
lift, evaluated on one bilateral branch point. -/
def projectiveLiftBranchCorrection
    (b1 b2 b3 : Bool) (a1 a2 a3 n1 n2 n3 : ℤ) : ℤ :=
  tripleLinearResidue b1 b2 b3 a1 a2 a3 n1 n2 n3

/-- **Uniform projective-root quotient law.**

If `w=lambda*v+p*a` and `v dot w=p*u`, the completed-square pairing with
`w` is `p` times an explicit affine expression.  Unlike the direct-root law,
the distinguished residue depends on the projective scalar and on `u`. -/
theorem projectiveRoot_reflection_quotient
    (b1 b2 b3 : Bool)
    (p lambda i j k w1 w2 w3 a1 a2 a3 u n1 n2 n3 r q : ℤ)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hvw : ternaryDot i j k w1 w2 w3 = p * u)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) w1 w2 w3
      = p * (2 * lambda * r - (w1 + w2 + w3) + 6 * u
          + p * (2 * lambda * q
            + 2 * projectiveLiftBranchCorrection b1 b2 b3 a1 a2 a3 n1 n2 n3)) := by
  subst w1
  subst w2
  subst w3
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [ternaryDot, tripleLinearResidue, quintLatticeCoord,
      projectiveLiftBranchCorrection] at hvw hresidue ⊢ <;>
    linear_combination 6 * hvw + 2 * p * lambda * hresidue

/-- The positive signed reflection is integral on completed-square branch
coordinates when the projective target expression is a multiple of `p`.
The resulting pairing is a multiple of `p^2`, exactly as required by the
uniform eight-branch construction. -/
theorem projectiveRoot_positive_target_pairing
    (b1 b2 b3 : Bool)
    (p lambda i j k w1 w2 w3 a1 a2 a3 u n1 n2 n3 r q h : ℤ)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hvw : ternaryDot i j k w1 w2 w3 = p * u)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * lambda * r = w1 + w2 + w3 - 6 * u + p * h) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) w1 w2 w3
      = p ^ 2 * (h + 2 * lambda * q
          + 2 * projectiveLiftBranchCorrection b1 b2 b3 a1 a2 a3 n1 n2 n3) := by
  rw [projectiveRoot_reflection_quotient b1 b2 b3 p lambda i j k w1 w2 w3
    a1 a2 a3 u n1 n2 n3 r q hw1 hw2 hw3 hvw hresidue, htarget]
  ring

/-- In the negative signed-reflection case, the scalar target congruence
`c*lambda*base = 12 (mod p)` implies all three coordinate congruences at once.
This is the projective replacement for the direct-root identity
`c*e*6=12`. -/
theorem projectiveRoot_negative_coordinate_offsets
    (p c lambda base i j k w1 w2 w3 a1 a2 a3 h : ℤ)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (htarget : c * lambda * base = 12 + p * h) :
    c * base * w1 = 12 * i + p * (h * i + c * base * a1)
      ∧ c * base * w2 = 12 * j + p * (h * j + c * base * a2)
      ∧ c * base * w3 = 12 * k + p * (h * k + c * base * a3) := by
  constructor
  · rw [hw1]
    linear_combination i * htarget
  constructor
  · rw [hw2]
    linear_combination j * htarget
  · rw [hw3]
    linear_combination k * htarget

/-! ### Necessity of the two projective target laws -/

/-- **Positive target necessity from one closed coordinate.**

The congruence used to close the positive projective reflection is not an
ad-hoc sufficient hypothesis.  If even one reflected quintuple coordinate
lands in a quintuple branch with the same index `i`, then `p` divides the
affine base, provided the visible scalar `c * lambda * i` is invertible modulo
`p`.  The Bezout hypothesis records that invertibility without requiring a
primality API. -/
theorem projectiveRoot_positive_target_necessary_of_coordinate_closure
    (b b' : Bool)
    (p c lambda base i w a m n n' bp bv : ℤ)
    (hw : w = lambda * i + p * a)
    (hunit : bp * p + bv * (c * lambda * i) = 1)
    (hclosure :
      quintLatticeCoord b' p i n' =
        shortRootReflectCoord c (base + p * m) w
          (quintLatticeCoord b p i n)) :
    ∃ h : ℤ, base = p * h := by
  have hdiv : p ∣ c * lambda * i * base := by
    refine ⟨6 * (n - n') + branchSign b - branchSign b'
      - c * a * base - c * m * lambda * i - c * p * m * a, ?_⟩
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign,
      hw] at hclosure
    dsimp [shortRootReflectCoord] at hclosure
    linear_combination hclosure
  rcases hdiv with ⟨q, hq⟩
  refine ⟨bp * base + bv * q, ?_⟩
  linear_combination -base * hunit + bv * hq

/-- **Negative target necessity from one closed coordinate.**

For the sign-corrected reflection, branch closure forces the exact offset
`c * lambda * base = 12 (mod p)`.  Again the only cancellation hypothesis is
an explicit Bezout inverse, now for the quintuple index `i` modulo `p`. -/
theorem projectiveRoot_negative_target_necessary_of_coordinate_closure
    (b b' : Bool)
    (p c lambda base i w a m n n' bp bi : ℤ)
    (hw : w = lambda * i + p * a)
    (hunit : bp * p + bi * i = 1)
    (hclosure :
      quintLatticeCoord b' p i n' =
        -shortRootReflectCoord c (base + p * m) w
          (quintLatticeCoord b p i n)) :
    ∃ h : ℤ, c * lambda * base = 12 + p * h := by
  have hdiv : p ∣ i * (c * lambda * base - 12) := by
    refine ⟨6 * n' + branchSign b' + (6 * n + branchSign b)
      - c * a * base - c * m * lambda * i - c * p * m * a, ?_⟩
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign,
      hw] at hclosure
    dsimp [shortRootReflectCoord] at hclosure
    linear_combination -hclosure
  rcases hdiv with ⟨q, hq⟩
  refine ⟨bp * (c * lambda * base - 12) + bi * q, ?_⟩
  linear_combination -(c * lambda * base - 12) * hunit + bi * hq

/-! ### Uniform positive branch closure -/

/-- Finite mod-3 data for a short-root branch reflection. -/
structure ShortRootPositiveMod3Input where
  epc : ZMod 3 × ZMod 3 × ZMod 3
  root : ZMod 3 × ZMod 3 × ZMod 3
  m : ZMod 3
  bits : Bool × Bool × Bool
  deriving DecidableEq, Fintype

namespace ShortRootPositiveMod3Input
def e (x : ShortRootPositiveMod3Input) := x.epc.1
def p (x : ShortRootPositiveMod3Input) := x.epc.2.1
def c (x : ShortRootPositiveMod3Input) := x.epc.2.2
def w1 (x : ShortRootPositiveMod3Input) := x.root.1
def w2 (x : ShortRootPositiveMod3Input) := x.root.2.1
def w3 (x : ShortRootPositiveMod3Input) := x.root.2.2
def b1 (x : ShortRootPositiveMod3Input) := x.bits.1
def b2 (x : ShortRootPositiveMod3Input) := x.bits.2.1
def b3 (x : ShortRootPositiveMod3Input) := x.bits.2.2
end ShortRootPositiveMod3Input

/-- Modulo three, a positive short-root reflection whose pairing is a multiple
of `p^2` sends the sign cube to itself and reverses the product of its signs.
This is an exhaustive theorem over the finite field `ZMod 3`. -/
theorem shortRoot_positive_mod3 :
    ∀ input : ShortRootPositiveMod3Input,
      input.e * input.p = 1 →
      input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2 = input.e * input.p →
      input.c * input.e = 2 →
      input.p * (branchSign3 input.b1 * input.w1
          + branchSign3 input.b2 * input.w2
          + branchSign3 input.b3 * input.w3) = input.p ^ 2 * input.m →
      let u1 := branchSign3 input.b1 - input.c * input.m * input.w1
      let u2 := branchSign3 input.b2 - input.c * input.m * input.w2
      let u3 := branchSign3 input.b3 - input.c * input.m * input.w3
      u1 ≠ 0 ∧ u2 ≠ 0 ∧ u3 ≠ 0
        ∧ u1 * u2 * u3
          = -(branchSign3 input.b1 * branchSign3 input.b2 * branchSign3 input.b3) := by
  set_option maxRecDepth 100000 in
    decide

/-- Integer hypotheses cast into the finite positive-branch theorem. -/
lemma shortRoot_positive_integral_mod3
    (b1 b2 b3 : Bool) (p e c w1 w2 w3 m x1 x2 x3 : ℤ)
    (hep : ((e * p : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hx1 : (x1 : ZMod 3) = (p : ZMod 3) * branchSign3 b1)
    (hx2 : (x2 : ZMod 3) = (p : ZMod 3) * branchSign3 b2)
    (hx3 : (x3 : ZMod 3) = (p : ZMod 3) * branchSign3 b3)
    (hpair : ternaryDot x1 x2 x3 w1 w2 w3 = p ^ 2 * m) :
    let u1 := branchSign b1 - c * m * w1
    let u2 := branchSign b2 - c * m * w2
    let u3 := branchSign b3 - c * m * w3
    ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) := by
  let input : ShortRootPositiveMod3Input :=
    ⟨(e, p, c), (w1, w2, w3), m, (b1, b2, b3)⟩
  have hfinite := shortRoot_positive_mod3 input
  have hep' : input.e * input.p = 1 := by
    simpa [input, ShortRootPositiveMod3Input.e, ShortRootPositiveMod3Input.p] using hep
  have hroot' : input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2
      = input.e * input.p := by
    simpa [input, ShortRootPositiveMod3Input.w1, ShortRootPositiveMod3Input.w2,
      ShortRootPositiveMod3Input.w3, ShortRootPositiveMod3Input.e,
      ShortRootPositiveMod3Input.p, ternaryNorm]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hroot
  have hc' : input.c * input.e = 2 := by
    simpa [input, ShortRootPositiveMod3Input.c, ShortRootPositiveMod3Input.e]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hcoefficient
  have hpairCast := congrArg (fun x : ℤ => (x : ZMod 3)) hpair
  have hpair' : input.p * (branchSign3 input.b1 * input.w1
        + branchSign3 input.b2 * input.w2 + branchSign3 input.b3 * input.w3)
      = input.p ^ 2 * input.m := by
    simp only [ternaryDot, Int.cast_add, Int.cast_mul, Int.cast_pow] at hpairCast
    rw [mul_add, mul_add]
    simpa [input, ShortRootPositiveMod3Input.p, ShortRootPositiveMod3Input.w1,
      ShortRootPositiveMod3Input.w2, ShortRootPositiveMod3Input.w3,
      ShortRootPositiveMod3Input.m, ShortRootPositiveMod3Input.b1,
      ShortRootPositiveMod3Input.b2, ShortRootPositiveMod3Input.b3,
      hx1, hx2, hx3, mul_assoc, mul_left_comm, mul_comm] using hpairCast
  simpa [input, ShortRootPositiveMod3Input.e, ShortRootPositiveMod3Input.p,
    ShortRootPositiveMod3Input.c, ShortRootPositiveMod3Input.w1,
    ShortRootPositiveMod3Input.w2, ShortRootPositiveMod3Input.w3,
    ShortRootPositiveMod3Input.m, ShortRootPositiveMod3Input.b1,
    ShortRootPositiveMod3Input.b2, ShortRootPositiveMod3Input.b3,
    branchSign3, branchSign]
    using hfinite hep' hroot' hc' hpair'

/-- A completed-square coordinate is odd when `p` is odd. -/
lemma quintLatticeCoord_odd_of_odd
    (b : Bool) (p i n : ℤ) (hpodd : Odd p) :
    Odd (quintLatticeCoord b p i n) := by
  obtain ⟨d, hd⟩ := hpodd
  cases b <;> simp [quintLatticeCoord] <;>
    refine ⟨?_, ?_⟩
  · exact 6 * d * n + 3 * n + 3 * i - d - 1
  · rw [hd]
    ring
  · exact 6 * d * n + 3 * n + 3 * i + d
  · rw [hd]
    ring

/-- The three positive-reflection output residues are odd.  The norm-`p`
case is immediate because `c=2`; in the norm-`2p` case, the root has even
coordinate sum and the pairing identity forces `m` even. -/
lemma shortRoot_positive_output_odd
    (b : Bool) (w p e c w1 w2 w3 m x1 x2 x3 : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hx1odd : Odd x1) (hx2odd : Odd x2) (hx3odd : Odd x3)
    (hpair : ternaryDot x1 x2 x3 w1 w2 w3 = p ^ 2 * m) :
    Odd (branchSign b - c * m * w) := by
  obtain ⟨d, hd⟩ := branchSign_odd b
  rcases he with rfl | rfl
  · have hc : c = 2 := by omega
    refine ⟨d - m * w, ?_⟩
    rw [hc, hd]
    ring
  · have hc : c = 1 := by omega
    have hsum := directRoot_sum_even_of_norm_two_mul p w1 w2 w3 (by simpa using hroot)
    have hpone : (p : ZMod 2) = 1 := by
      obtain ⟨a, ha⟩ := hpodd
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [ha]
      simp [htwo]
    have hxone (x : ℤ) (hx : Odd x) : (x : ZMod 2) = 1 := by
      obtain ⟨a, ha⟩ := hx
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [ha]
      simp [htwo]
    have hsumzero : ((w1 + w2 + w3 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (w1 + w2 + w3) 2).mpr hsum.two_dvd
    have hpairCast := congrArg (fun x : ℤ => (x : ZMod 2)) hpair
    have hmEq : (w1 : ZMod 2) + (w2 : ZMod 2) + (w3 : ZMod 2) = (m : ZMod 2) := by
      simpa [ternaryDot, hxone x1 hx1odd, hxone x2 hx2odd, hxone x3 hx3odd,
        hpone, pow_two] using hpairCast
    have hmzero : (m : ZMod 2) = 0 := by
      calc
        (m : ZMod 2) = (w1 : ZMod 2) + (w2 : ZMod 2) + (w3 : ZMod 2) := hmEq.symm
        _ = 0 := by simpa using hsumzero
    have hmeven : Even m := even_iff_two_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd m 2).mp hmzero)
    obtain ⟨v, hv⟩ := hmeven
    refine ⟨d - v * w, ?_⟩
    rw [hc, hd, hv]
    ring

/-- **Uniform positive eight-branch matching for a projective short root.**

Once the projective target law makes the completed-coordinate pairing equal
to `p^2*m`, the positive Householder reflection closes on all eight bilateral
branches.  It reverses branch weight, preserves the exponent, and carries its
own coordinatewise inverse certificate. -/
theorem shortRoot_positive_eight_branch_matching
    (b1 b2 b3 : Bool)
    (p e c i j k w1 w2 w3 m n1 n2 n3 : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hep : ((e * p : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hpair : ternaryDot
      (quintLatticeCoord b1 p i n1)
      (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) w1 w2 w3 = p ^ 2 * m) :
    ∃ b1' b2' b3' : Bool, ∃ z1 z2 z3 : ℤ,
      branchSign b1 - c * m * w1 = branchSign b1' + 6 * z1
        ∧ branchSign b2 - c * m * w2 = branchSign b2' + 6 * z2
        ∧ branchSign b3 - c * m * w3 = branchSign b3' + 6 * z3
        ∧ branchSign b1' * branchSign b2' * branchSign b3'
          = -(branchSign b1 * branchSign b2 * branchSign b3)
        ∧ quintLatticeCoord b1' p i (n1 + z1)
          = shortRootReflectCoord c (p * m) w1 (quintLatticeCoord b1 p i n1)
        ∧ quintLatticeCoord b2' p j (n2 + z2)
          = shortRootReflectCoord c (p * m) w2 (quintLatticeCoord b2 p j n2)
        ∧ quintLatticeCoord b3' p k (n3 + z3)
          = shortRootReflectCoord c (p * m) w3 (quintLatticeCoord b3 p k n3)
        ∧ tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
          = tripleQuintExp2 b1' b2' b3' p i j k (n1 + z1) (n2 + z2) (n3 + z3)
        ∧ shortRootReflectCoord c (-(p * m)) w1
            (quintLatticeCoord b1' p i (n1 + z1)) = quintLatticeCoord b1 p i n1
        ∧ shortRootReflectCoord c (-(p * m)) w2
            (quintLatticeCoord b2' p j (n2 + z2)) = quintLatticeCoord b2 p j n2
        ∧ shortRootReflectCoord c (-(p * m)) w3
            (quintLatticeCoord b3' p k (n3 + z3)) = quintLatticeCoord b3 p k n3 := by
  let x1 := quintLatticeCoord b1 p i n1
  let x2 := quintLatticeCoord b2 p j n2
  let x3 := quintLatticeCoord b3 p k n3
  let u1 := branchSign b1 - c * m * w1
  let u2 := branchSign b2 - c * m * w2
  let u3 := branchSign b3 - c * m * w3
  have hsix : (6 : ZMod 3) = 0 := by decide
  have hx1mod : (x1 : ZMod 3) = (p : ZMod 3) * branchSign3 b1 := by
    cases b1 <;> simp [x1, quintLatticeCoord, branchSign3, hsix]
  have hx2mod : (x2 : ZMod 3) = (p : ZMod 3) * branchSign3 b2 := by
    cases b2 <;> simp [x2, quintLatticeCoord, branchSign3, hsix]
  have hx3mod : (x3 : ZMod 3) = (p : ZMod 3) * branchSign3 b3 := by
    cases b3 <;> simp [x3, quintLatticeCoord, branchSign3, hsix]
  have hmod := shortRoot_positive_integral_mod3 b1 b2 b3 p e c w1 w2 w3 m
    x1 x2 x3 hep hroot hcoefficient hx1mod hx2mod hx3mod (by simpa [x1, x2, x3] using hpair)
  change ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) at hmod
  have hx1odd := quintLatticeCoord_odd_of_odd b1 p i n1 hpodd
  have hx2odd := quintLatticeCoord_odd_of_odd b2 p j n2 hpodd
  have hx3odd := quintLatticeCoord_odd_of_odd b3 p k n3 hpodd
  have hu1odd : Odd u1 := shortRoot_positive_output_odd b1 w1 p e c w1 w2 w3 m
    x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd (by simpa [x1, x2, x3] using hpair)
  have hu2odd : Odd u2 := shortRoot_positive_output_odd b2 w2 p e c w1 w2 w3 m
    x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd (by simpa [x1, x2, x3] using hpair)
  have hu3odd : Odd u3 := shortRoot_positive_output_odd b3 w3 p e c w1 w2 w3 m
    x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd (by simpa [x1, x2, x3] using hpair)
  obtain ⟨b1', z1, hz1⟩ := exists_branch_of_odd_of_mod3_ne_zero u1 hu1odd hmod.1
  obtain ⟨b2', z2, hz2⟩ := exists_branch_of_odd_of_mod3_ne_zero u2 hu2odd hmod.2.1
  obtain ⟨b3', z3, hz3⟩ := exists_branch_of_odd_of_mod3_ne_zero u3 hu3odd hmod.2.2.1
  have hproduct3 : branchSign3 b1' * branchSign3 b2' * branchSign3 b3'
      = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) := by
    simpa [branchSign3, branchSign, hz1, hz2, hz3, hsix] using hmod.2.2.2
  have hproduct := branchSign_product_eq_of_mod3 b1' b2' b3' b1 b2 b3 hproduct3
  have hcoord1 : quintLatticeCoord b1' p i (n1 + z1)
      = shortRootReflectCoord c (p * m) w1 (quintLatticeCoord b1 p i n1) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u1] at hz1 ⊢
    linear_combination -p * hz1
  have hcoord2 : quintLatticeCoord b2' p j (n2 + z2)
      = shortRootReflectCoord c (p * m) w2 (quintLatticeCoord b2 p j n2) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u2] at hz2 ⊢
    linear_combination -p * hz2
  have hcoord3 : quintLatticeCoord b3' p k (n3 + z3)
      = shortRootReflectCoord c (p * m) w3 (quintLatticeCoord b3 p k n3) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u3] at hz3 ⊢
    linear_combination -p * hz3
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hpair' : ternaryDot
      (quintLatticeCoord b1 p i n1) (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) w1 w2 w3 = p * (p * m) := by
    simpa [pow_two, mul_assoc] using hpair
  have hexponent := shortRoot_preserves_tripleQuintExp2 b1 b2 b3 b1' b2' b3'
    p e c 1 i j k w1 w2 w3 (p * m) n1 n2 n3 (n1 + z1) (n2 + z2) (n3 + z3)
    hpne hroot hcoefficient (by norm_num) hpair'
    (by simpa using hcoord1) (by simpa using hcoord2) (by simpa using hcoord3)
  refine ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
    hcoord1, hcoord2, hcoord3, hexponent, ?_, ?_, ?_⟩
  · rw [hcoord1]
    exact shortRootReflect_involutive c (p * m) w1 _
  · rw [hcoord2]
    exact shortRootReflect_involutive c (p * m) w2 _
  · rw [hcoord3]
    exact shortRootReflect_involutive c (p * m) w3 _

/-! ### Uniform negative branch closure -/

/-- Finite mod-3 data for the sign-corrected negative reflection. -/
structure ShortRootNegativeMod3Input where
  epc : ZMod 3 × ZMod 3 × ZMod 3
  root : ZMod 3 × ZMod 3 × ZMod 3
  quotient : ZMod 3 × ZMod 3
  bits : Bool × Bool × Bool
  deriving DecidableEq, Fintype

namespace ShortRootNegativeMod3Input
def e (x : ShortRootNegativeMod3Input) := x.epc.1
def p (x : ShortRootNegativeMod3Input) := x.epc.2.1
def c (x : ShortRootNegativeMod3Input) := x.epc.2.2
def w1 (x : ShortRootNegativeMod3Input) := x.root.1
def w2 (x : ShortRootNegativeMod3Input) := x.root.2.1
def w3 (x : ShortRootNegativeMod3Input) := x.root.2.2
def t0 (x : ShortRootNegativeMod3Input) := x.quotient.1
def m (x : ShortRootNegativeMod3Input) := x.quotient.2
def b1 (x : ShortRootNegativeMod3Input) := x.bits.1
def b2 (x : ShortRootNegativeMod3Input) := x.bits.2.1
def b3 (x : ShortRootNegativeMod3Input) := x.bits.2.2
end ShortRootNegativeMod3Input

/-- The norm-two sign-cube calculation after all affine quotient data have
been eliminated.  This has only `3^3 * 2^3 = 216` finite inputs. -/
theorem shortRoot_negative_signCube_mod3 :
    ∀ (w1 w2 w3 : ZMod 3) (b1 b2 b3 : Bool),
      w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = 2 →
      let A := branchSign3 b1 * w1 + branchSign3 b2 * w2 + branchSign3 b3 * w3
      let u1 := -(branchSign3 b1 - A * w1)
      let u2 := -(branchSign3 b2 - A * w2)
      let u3 := -(branchSign3 b3 - A * w3)
      u1 ≠ 0 ∧ u2 ≠ 0 ∧ u3 ≠ 0 ∧
        u1 * u2 * u3 =
          -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) := by
  set_option maxRecDepth 100000 in
    decide

/-- When `e*p=2 (mod 3)`, the sign-corrected reflection of the sign cube
closes and reverses sign product.  The effective quotient is
`s=p*t0+m`; this is `p⁻¹*t0+m` because every nonzero element of `ZMod 3`
is its own inverse. -/
theorem shortRoot_negative_mod3 :
    ∀ input : ShortRootNegativeMod3Input,
      input.e * input.p = 2 →
      input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2 = input.e * input.p →
      input.c * input.e = 2 →
      input.p * (branchSign3 input.b1 * input.w1
          + branchSign3 input.b2 * input.w2
          + branchSign3 input.b3 * input.w3)
        = input.p * (input.t0 + input.p * input.m) →
      let s := input.p * input.t0 + input.m
      let u1 := -(branchSign3 input.b1 - input.c * s * input.w1)
      let u2 := -(branchSign3 input.b2 - input.c * s * input.w2)
      let u3 := -(branchSign3 input.b3 - input.c * s * input.w3)
      u1 ≠ 0 ∧ u2 ≠ 0 ∧ u3 ≠ 0
        ∧ u1 * u2 * u3
          = -(branchSign3 input.b1 * branchSign3 input.b2 * branchSign3 input.b3) := by
  rintro ⟨⟨e, p, c⟩, ⟨w1, w2, w3⟩, ⟨t0, m⟩, ⟨b1, b2, b3⟩⟩
    hep hroot hcoefficient hpair
  dsimp [ShortRootNegativeMod3Input.e, ShortRootNegativeMod3Input.p,
    ShortRootNegativeMod3Input.c, ShortRootNegativeMod3Input.w1,
    ShortRootNegativeMod3Input.w2, ShortRootNegativeMod3Input.w3,
    ShortRootNegativeMod3Input.t0, ShortRootNegativeMod3Input.m,
    ShortRootNegativeMod3Input.b1, ShortRootNegativeMod3Input.b2,
    ShortRootNegativeMod3Input.b3] at hep hroot hcoefficient hpair ⊢
  have he_ne : e ≠ 0 := by
    intro hezero
    rw [hezero, zero_mul] at hep
    exact (by decide : (0 : ZMod 3) ≠ 2) hep
  have hp_ne : p ≠ 0 := by
    intro hpzero
    rw [hpzero, mul_zero] at hep
    exact (by decide : (0 : ZMod 3) ≠ 2) hep
  have hcp : c = p := by
    apply mul_right_cancel₀ he_ne
    calc
      c * e = 2 := hcoefficient
      _ = e * p := hep.symm
      _ = p * e := mul_comm _ _
  have hp_sq : p ^ 2 = 1 := by
    have hall : ∀ y : ZMod 3, y ≠ 0 → y ^ 2 = 1 := by decide
    exact hall p hp_ne
  let A : ZMod 3 := branchSign3 b1 * w1 + branchSign3 b2 * w2 +
    branchSign3 b3 * w3
  have hA : A = t0 + p * m := by
    apply mul_left_cancel₀ hp_ne
    simpa [A] using hpair
  have hs : p * t0 + m = p * A := by
    calc
      p * t0 + m = p * t0 + p ^ 2 * m := by rw [hp_sq, one_mul]
      _ = p * (t0 + p * m) := by ring
      _ = p * A := by rw [hA]
  have hcs : c * (p * t0 + m) = A := by
    calc
      c * (p * t0 + m) = p * (p * A) := by rw [hcp, hs]
      _ = A := by rw [← mul_assoc, ← pow_two, hp_sq, one_mul]
  rw [hcs]
  simpa [A] using shortRoot_negative_signCube_mod3
    w1 w2 w3 b1 b2 b3 (hroot.trans hep)

/-- A nonzero residue modulo three squares to one. -/
lemma zmod3_sq_eq_one_of_ne_zero (x : ZMod 3) (hx : x ≠ 0) : x ^ 2 = 1 := by
  have hall : ∀ y : ZMod 3, y ≠ 0 → y ^ 2 = 1 := by decide
  exact hall x hx

/-- Integer negative-target data cast into the finite sign-cube theorem.
The coordinate offsets are eliminated modulo three using
`c*t0*w_s = 12*i_s+p*d_s`. -/
lemma shortRoot_negative_integral_mod3
    (b1 b2 b3 : Bool)
    (p e c i j k w1 w2 w3 t0 m d1 d2 d3 x1 x2 x3 : ℤ)
    (hep : ((e * p : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hx1 : (x1 : ZMod 3) = (p : ZMod 3) * branchSign3 b1)
    (hx2 : (x2 : ZMod 3) = (p : ZMod 3) * branchSign3 b2)
    (hx3 : (x3 : ZMod 3) = (p : ZMod 3) * branchSign3 b3)
    (hpair : ternaryDot x1 x2 x3 w1 w2 w3 = p * (t0 + p * m))
    (hoffset1 : c * t0 * w1 = 12 * i + p * d1)
    (hoffset2 : c * t0 * w2 = 12 * j + p * d2)
    (hoffset3 : c * t0 * w3 = 12 * k + p * d3) :
    let u1 := -branchSign b1 + d1 + c * m * w1
    let u2 := -branchSign b2 + d2 + c * m * w2
    let u3 := -branchSign b3 + d3 + c * m * w3
    ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) := by
  let input : ShortRootNegativeMod3Input :=
    ⟨(e, p, c), (w1, w2, w3), (t0, m), (b1, b2, b3)⟩
  have hpne : (p : ZMod 3) ≠ 0 := by
    intro hpzero
    have := hep
    rw [Int.cast_mul, hpzero, mul_zero] at this
    exact (by decide : (0 : ZMod 3) ≠ 2) this
  have hpSq : (p : ZMod 3) ^ 2 = 1 := zmod3_sq_eq_one_of_ne_zero p hpne
  have hfinite := shortRoot_negative_mod3 input
  have hep' : input.e * input.p = 2 := by
    simpa [input, ShortRootNegativeMod3Input.e, ShortRootNegativeMod3Input.p] using hep
  have hroot' : input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2
      = input.e * input.p := by
    simpa [input, ShortRootNegativeMod3Input.w1, ShortRootNegativeMod3Input.w2,
      ShortRootNegativeMod3Input.w3, ShortRootNegativeMod3Input.e,
      ShortRootNegativeMod3Input.p, ternaryNorm]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hroot
  have hc' : input.c * input.e = 2 := by
    simpa [input, ShortRootNegativeMod3Input.c, ShortRootNegativeMod3Input.e]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hcoefficient
  have hpairCast := congrArg (fun x : ℤ => (x : ZMod 3)) hpair
  have hpair' : input.p * (branchSign3 input.b1 * input.w1
        + branchSign3 input.b2 * input.w2 + branchSign3 input.b3 * input.w3)
      = input.p * (input.t0 + input.p * input.m) := by
    simp only [ternaryDot, Int.cast_add, Int.cast_mul] at hpairCast
    rw [mul_add, mul_add]
    simpa [input, ShortRootNegativeMod3Input.p, ShortRootNegativeMod3Input.w1,
      ShortRootNegativeMod3Input.w2, ShortRootNegativeMod3Input.w3,
      ShortRootNegativeMod3Input.t0, ShortRootNegativeMod3Input.m,
      ShortRootNegativeMod3Input.b1, ShortRootNegativeMod3Input.b2,
      ShortRootNegativeMod3Input.b3, hx1, hx2, hx3, mul_assoc, mul_left_comm,
      mul_comm] using hpairCast
  have hoff1 := congrArg (fun x : ℤ => (x : ZMod 3)) hoffset1
  have hoff2 := congrArg (fun x : ℤ => (x : ZMod 3)) hoffset2
  have hoff3 := congrArg (fun x : ℤ => (x : ZMod 3)) hoffset3
  have hd1 : (d1 : ZMod 3) = (p : ZMod 3) * c * t0 * w1 := by
    have h12 : (12 : ZMod 3) = 0 := by decide
    simp only [Int.cast_add, Int.cast_mul] at hoff1
    have hoff1' : (c : ZMod 3) * t0 * w1 = p * d1 := by
      simpa [h12] using hoff1
    calc
      (d1 : ZMod 3) = (p : ZMod 3) ^ 2 * d1 := by rw [hpSq, one_mul]
      _ = (p : ZMod 3) * (p * d1) := by ring
      _ = (p : ZMod 3) * (c * t0 * w1) := by rw [hoff1']
      _ = (p : ZMod 3) * c * t0 * w1 := by ring
  have hd2 : (d2 : ZMod 3) = (p : ZMod 3) * c * t0 * w2 := by
    have h12 : (12 : ZMod 3) = 0 := by decide
    simp only [Int.cast_add, Int.cast_mul] at hoff2
    have hoff2' : (c : ZMod 3) * t0 * w2 = p * d2 := by
      simpa [h12] using hoff2
    calc
      (d2 : ZMod 3) = (p : ZMod 3) ^ 2 * d2 := by rw [hpSq, one_mul]
      _ = (p : ZMod 3) * (p * d2) := by ring
      _ = (p : ZMod 3) * (c * t0 * w2) := by rw [hoff2']
      _ = (p : ZMod 3) * c * t0 * w2 := by ring
  have hd3 : (d3 : ZMod 3) = (p : ZMod 3) * c * t0 * w3 := by
    have h12 : (12 : ZMod 3) = 0 := by decide
    simp only [Int.cast_add, Int.cast_mul] at hoff3
    have hoff3' : (c : ZMod 3) * t0 * w3 = p * d3 := by
      simpa [h12] using hoff3
    calc
      (d3 : ZMod 3) = (p : ZMod 3) ^ 2 * d3 := by rw [hpSq, one_mul]
      _ = (p : ZMod 3) * (p * d3) := by ring
      _ = (p : ZMod 3) * (c * t0 * w3) := by rw [hoff3']
      _ = (p : ZMod 3) * c * t0 * w3 := by ring
  have hu1 : ((-branchSign b1 + d1 + c * m * w1 : ℤ) : ZMod 3)
      = -(branchSign3 b1 - c * (p * t0 + m) * w1) := by
    cases b1 <;> simp [branchSign3, branchSign, hd1] <;> ring
  have hu2 : ((-branchSign b2 + d2 + c * m * w2 : ℤ) : ZMod 3)
      = -(branchSign3 b2 - c * (p * t0 + m) * w2) := by
    cases b2 <;> simp [branchSign3, branchSign, hd2] <;> ring
  have hu3 : ((-branchSign b3 + d3 + c * m * w3 : ℤ) : ZMod 3)
      = -(branchSign3 b3 - c * (p * t0 + m) * w3) := by
    cases b3 <;> simp [branchSign3, branchSign, hd3] <;> ring
  dsimp only
  rw [hu1, hu2, hu3]
  have hbranch (b : Bool) : ((branchSign b : ℤ) : ZMod 3) = branchSign3 b := by
    cases b <;> rfl
  rw [hbranch b1, hbranch b2, hbranch b3]
  simpa [input, ShortRootNegativeMod3Input.e, ShortRootNegativeMod3Input.p,
    ShortRootNegativeMod3Input.c, ShortRootNegativeMod3Input.w1,
    ShortRootNegativeMod3Input.w2, ShortRootNegativeMod3Input.w3,
    ShortRootNegativeMod3Input.t0, ShortRootNegativeMod3Input.m,
    ShortRootNegativeMod3Input.b1, ShortRootNegativeMod3Input.b2,
    ShortRootNegativeMod3Input.b3,
    mul_assoc, mul_left_comm, mul_comm]
    using hfinite hep' hroot' hc' hpair'

/-- The integer negative-reflection branch residue is odd. -/
lemma shortRoot_negative_output_odd
    (b : Bool) (w i p e c t0 m d w1 w2 w3 x1 x2 x3 : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hx1odd : Odd x1) (hx2odd : Odd x2) (hx3odd : Odd x3)
    (hpair : ternaryDot x1 x2 x3 w1 w2 w3 = p * (t0 + p * m))
    (hoffset : c * t0 * w = 12 * i + p * d) :
    Odd (-branchSign b + d + c * m * w) := by
  obtain ⟨a, ha⟩ := branchSign_odd b
  have hpone : (p : ZMod 2) = 1 := by
    obtain ⟨z, hz⟩ := hpodd
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [hz]
    simp [htwo]
  have hxone (x : ℤ) (hx : Odd x) : (x : ZMod 2) = 1 := by
    obtain ⟨z, hz⟩ := hx
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [hz]
    simp [htwo]
  have hctzero : (c : ZMod 2) * ((t0 : ZMod 2) + (p : ZMod 2) * (m : ZMod 2))
      * (w : ZMod 2) = 0 := by
    rcases he with rfl | rfl
    · have hc : c = 2 := by omega
      have hc0 : (c : ZMod 2) = 0 := by rw [hc]; decide
      rw [hc0]
      ring
    · have hc : c = 1 := by omega
      have hsum := directRoot_sum_even_of_norm_two_mul p w1 w2 w3 (by simpa using hroot)
      have hsumzero : ((w1 + w2 + w3 : ℤ) : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (w1 + w2 + w3) 2).mpr hsum.two_dvd
      have hpairCast := congrArg (fun x : ℤ => (x : ZMod 2)) hpair
      have htzero : ((t0 + p * m : ℤ) : ZMod 2) = 0 := by
        calc
          ((t0 + p * m : ℤ) : ZMod 2)
              = (w1 : ZMod 2) + w2 + w3 := by
                simpa [ternaryDot, hxone x1 hx1odd, hxone x2 hx2odd,
                  hxone x3 hx3odd, hpone] using hpairCast.symm
          _ = 0 := by simpa using hsumzero
      have htzero' : (t0 : ZMod 2) + (p : ZMod 2) * (m : ZMod 2) = 0 := by
        simpa only [Int.cast_add, Int.cast_mul] using htzero
      rw [hc, htzero']
      ring
  have hoffCast := congrArg (fun x : ℤ => (x : ZMod 2)) hoffset
  have hshiftzero : ((d + c * m * w : ℤ) : ZMod 2) = 0 := by
    have h12 : (12 : ZMod 2) = 0 := by decide
    simp only [Int.cast_add, Int.cast_mul] at hoffCast
    calc
      ((d + c * m * w : ℤ) : ZMod 2) = d + c * m * w := by push_cast; rfl
      _ = c * t0 * w + c * m * w := by simpa [hpone, h12] using congrArg id hoffCast.symm
      _ = c * (t0 + p * m) * w := by rw [show (p : ZMod 2) = 1 from hpone]; ring
      _ = 0 := hctzero
  have hshiftEven : Even (d + c * m * w) := even_iff_two_dvd.mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (d + c * m * w) 2).mp hshiftzero)
  obtain ⟨z, hz⟩ := hshiftEven
  refine ⟨z - a - 1, ?_⟩
  rw [ha]
  linear_combination hz

/-- **Uniform sign-corrected negative eight-branch matching.** -/
theorem shortRoot_negative_eight_branch_matching
    (b1 b2 b3 : Bool)
    (p e c i j k w1 w2 w3 t0 m d1 d2 d3 n1 n2 n3 : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hep : ((e * p : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hpair : ternaryDot
      (quintLatticeCoord b1 p i n1)
      (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) w1 w2 w3 = p * (t0 + p * m))
    (hoffset1 : c * t0 * w1 = 12 * i + p * d1)
    (hoffset2 : c * t0 * w2 = 12 * j + p * d2)
    (hoffset3 : c * t0 * w3 = 12 * k + p * d3) :
    ∃ b1' b2' b3' : Bool, ∃ z1 z2 z3 : ℤ,
      -branchSign b1 + d1 + c * m * w1 = branchSign b1' + 6 * z1
        ∧ -branchSign b2 + d2 + c * m * w2 = branchSign b2' + 6 * z2
        ∧ -branchSign b3 + d3 + c * m * w3 = branchSign b3' + 6 * z3
        ∧ branchSign b1' * branchSign b2' * branchSign b3'
          = -(branchSign b1 * branchSign b2 * branchSign b3)
        ∧ quintLatticeCoord b1' p i (-n1 + z1)
          = -shortRootReflectCoord c (t0 + p * m) w1 (quintLatticeCoord b1 p i n1)
        ∧ quintLatticeCoord b2' p j (-n2 + z2)
          = -shortRootReflectCoord c (t0 + p * m) w2 (quintLatticeCoord b2 p j n2)
        ∧ quintLatticeCoord b3' p k (-n3 + z3)
          = -shortRootReflectCoord c (t0 + p * m) w3 (quintLatticeCoord b3 p k n3)
        ∧ tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
          = tripleQuintExp2 b1' b2' b3' p i j k (-n1 + z1) (-n2 + z2) (-n3 + z3)
        ∧ -shortRootReflectCoord c (t0 + p * m) w1
            (quintLatticeCoord b1' p i (-n1 + z1)) = quintLatticeCoord b1 p i n1
        ∧ -shortRootReflectCoord c (t0 + p * m) w2
            (quintLatticeCoord b2' p j (-n2 + z2)) = quintLatticeCoord b2 p j n2
        ∧ -shortRootReflectCoord c (t0 + p * m) w3
            (quintLatticeCoord b3' p k (-n3 + z3)) = quintLatticeCoord b3 p k n3 := by
  let x1 := quintLatticeCoord b1 p i n1
  let x2 := quintLatticeCoord b2 p j n2
  let x3 := quintLatticeCoord b3 p k n3
  let u1 := -branchSign b1 + d1 + c * m * w1
  let u2 := -branchSign b2 + d2 + c * m * w2
  let u3 := -branchSign b3 + d3 + c * m * w3
  have hsix : (6 : ZMod 3) = 0 := by decide
  have hx1mod : (x1 : ZMod 3) = (p : ZMod 3) * branchSign3 b1 := by
    cases b1 <;> simp [x1, quintLatticeCoord, branchSign3, hsix]
  have hx2mod : (x2 : ZMod 3) = (p : ZMod 3) * branchSign3 b2 := by
    cases b2 <;> simp [x2, quintLatticeCoord, branchSign3, hsix]
  have hx3mod : (x3 : ZMod 3) = (p : ZMod 3) * branchSign3 b3 := by
    cases b3 <;> simp [x3, quintLatticeCoord, branchSign3, hsix]
  have hmod := shortRoot_negative_integral_mod3 b1 b2 b3 p e c i j k w1 w2 w3
    t0 m d1 d2 d3 x1 x2 x3 hep hroot hcoefficient hx1mod hx2mod hx3mod
    (by simpa [x1, x2, x3] using hpair) hoffset1 hoffset2 hoffset3
  change ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) at hmod
  have hx1odd := quintLatticeCoord_odd_of_odd b1 p i n1 hpodd
  have hx2odd := quintLatticeCoord_odd_of_odd b2 p j n2 hpodd
  have hx3odd := quintLatticeCoord_odd_of_odd b3 p k n3 hpodd
  have hu1odd : Odd u1 := shortRoot_negative_output_odd b1 w1 i p e c t0 m d1
    w1 w2 w3 x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd
    (by simpa [x1, x2, x3] using hpair) hoffset1
  have hu2odd : Odd u2 := shortRoot_negative_output_odd b2 w2 j p e c t0 m d2
    w1 w2 w3 x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd
    (by simpa [x1, x2, x3] using hpair) hoffset2
  have hu3odd : Odd u3 := shortRoot_negative_output_odd b3 w3 k p e c t0 m d3
    w1 w2 w3 x1 x2 x3 hpodd he hroot hcoefficient hx1odd hx2odd hx3odd
    (by simpa [x1, x2, x3] using hpair) hoffset3
  obtain ⟨b1', z1, hz1⟩ := exists_branch_of_odd_of_mod3_ne_zero u1 hu1odd hmod.1
  obtain ⟨b2', z2, hz2⟩ := exists_branch_of_odd_of_mod3_ne_zero u2 hu2odd hmod.2.1
  obtain ⟨b3', z3, hz3⟩ := exists_branch_of_odd_of_mod3_ne_zero u3 hu3odd hmod.2.2.1
  have hproduct3 : branchSign3 b1' * branchSign3 b2' * branchSign3 b3'
      = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) := by
    simpa [branchSign3, branchSign, hz1, hz2, hz3, hsix] using hmod.2.2.2
  have hproduct := branchSign_product_eq_of_mod3 b1' b2' b3' b1 b2 b3 hproduct3
  have hcoord1 : quintLatticeCoord b1' p i (-n1 + z1)
      = -shortRootReflectCoord c (t0 + p * m) w1 (quintLatticeCoord b1 p i n1) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u1] at hz1 ⊢
    linear_combination -p * hz1 - hoffset1
  have hcoord2 : quintLatticeCoord b2' p j (-n2 + z2)
      = -shortRootReflectCoord c (t0 + p * m) w2 (quintLatticeCoord b2 p j n2) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u2] at hz2 ⊢
    linear_combination -p * hz2 - hoffset2
  have hcoord3 : quintLatticeCoord b3' p k (-n3 + z3)
      = -shortRootReflectCoord c (t0 + p * m) w3 (quintLatticeCoord b3 p k n3) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, u3] at hz3 ⊢
    linear_combination -p * hz3 - hoffset3
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hexponent := shortRoot_preserves_tripleQuintExp2 b1 b2 b3 b1' b2' b3'
    p e c (-1) i j k w1 w2 w3 (t0 + p * m) n1 n2 n3
    (-n1 + z1) (-n2 + z2) (-n3 + z3) hpne hroot hcoefficient (by norm_num)
    hpair (by simpa using hcoord1) (by simpa using hcoord2) (by simpa using hcoord3)
  refine ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
    hcoord1, hcoord2, hcoord3, hexponent, ?_, ?_, ?_⟩
  · rw [hcoord1]
    exact negativeShortRootReflect_involutive c (t0 + p * m) w1 _
  · rw [hcoord2]
    exact negativeShortRootReflect_involutive c (t0 + p * m) w2 _
  · rw [hcoord3]
    exact negativeShortRootReflect_involutive c (t0 + p * m) w3 _

/-! ### From uniform branch closure to coefficient vanishing -/

/-- **Positive pairing-to-vanishing bridge.**

This is the reusable global form of the positive eight-branch theorem.  The
function `M` may depend arbitrarily on a branch point.  It is enough that every
point contributing to the requested coefficient has root pairing `p² M(x)`.
The proof constructs the partner, proves that its multiplier is `-M(x)` from
the reflected pairing, and therefore obtains a genuine involution of the full
coefficient support. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_positive_root_pairing
    (p i j k K : ℕ) (e c w1 w2 w3 : ℤ)
    (M : TripleQuintBranchIndex → ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hpair : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      ternaryDot (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        w1 w2 w3 = (p : ℤ) ^ 2 * M x) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  have hpne : (p : ℤ) ≠ 0 := by
    rintro hpzero
    obtain ⟨a, ha⟩ := hpodd
    omega
  let PartnerSpec : TripleQuintBranchIndex → TripleQuintBranchIndex → Prop :=
    fun x y =>
      pointBranchWeight y = -pointBranchWeight x ∧
      pointTripleExp2 p i j k y = pointTripleExp2 p i j k x ∧
      pointCoord1 p i y = shortRootReflectCoord c ((p : ℤ) * M x) w1
        (pointCoord1 p i x) ∧
      pointCoord2 p j y = shortRootReflectCoord c ((p : ℤ) * M x) w2
        (pointCoord2 p j x) ∧
      pointCoord3 p k y = shortRootReflectCoord c ((p : ℤ) * M x) w3
        (pointCoord3 p k x) ∧
      shortRootReflectCoord c (-((p : ℤ) * M x)) w1 (pointCoord1 p i y) =
        pointCoord1 p i x ∧
      shortRootReflectCoord c (-((p : ℤ) * M x)) w2 (pointCoord2 p j y) =
        pointCoord2 p j x ∧
      shortRootReflectCoord c (-((p : ℤ) * M x)) w3 (pointCoord3 p k y) =
        pointCoord3 p k x
  have hexists : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      ∃ y, PartnerSpec x y := by
    intro x hexp
    obtain ⟨b1', b2', b3', z1, z2, z3, _hz1, _hz2, _hz3, hproduct,
        hcoord1, hcoord2, hcoord3, hexponent, hreturn1, hreturn2, hreturn3⟩ :=
      shortRoot_positive_eight_branch_matching
        (pointB1 x) (pointB2 x) (pointB3 x) p e c i j k w1 w2 w3 (M x)
        (pointN1 x) (pointN2 x) (pointN3 x) hpodd he hep hroot hcoefficient
        (by simpa [pointCoord1, pointCoord2, pointCoord3] using hpair x hexp)
    let y : TripleQuintBranchIndex :=
      (((b1', pointN1 x + z1), (b2', pointN2 x + z2)),
        (b3', pointN3 x + z3))
    refine ⟨y, ?_⟩
    dsimp [PartnerSpec]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
      rw [hproduct]
      simp [pointB1, pointB2, pointB3]
    · simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1,
        pointN2, pointN3] using hexponent.symm
    · simpa [pointCoord1, y, pointB1, pointN1] using hcoord1
    · simpa [pointCoord2, y, pointB2, pointN2] using hcoord2
    · simpa [pointCoord3, y, pointB3, pointN3] using hcoord3
    · simpa [pointCoord1, y, pointB1, pointN1] using hreturn1
    · simpa [pointCoord2, y, pointB2, pointN2] using hreturn2
    · simpa [pointCoord3, y, pointB3, pointN3] using hreturn3
  let partner : TripleQuintBranchIndex → TripleQuintBranchIndex := fun x =>
    if hx : pointTripleExp2 p i j k x = 2 * (K : ℤ) then
      Classical.choose (hexists x hx)
    else x
  have partner_spec : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      PartnerSpec x (partner x) := by
    intro x hexp
    dsimp [partner]
    simp only [dif_pos hexp]
    exact Classical.choose_spec (hexists x hexp)
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_expInvolution
    p i j k K partner hi hpi hj hpj hk hpk
  · intro x hexp
    exact (partner_spec x hexp).1
  · intro x hexp
    exact (partner_spec x hexp).2.1
  · intro x hexp
    have hxy := partner_spec x hexp
    have hyexp : pointTripleExp2 p i j k (partner x) = 2 * (K : ℤ) :=
      hxy.2.1.trans hexp
    have hyz := partner_spec (partner x) hyexp
    have hxpair := hpair x hexp
    have hypair := hpair (partner x) hyexp
    have hflip := shortRootReflect_flips_pairing (p : ℤ) e c
      ((p : ℤ) * M x) w1 w2 w3
      (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
      hroot (by simpa [pow_two, mul_assoc] using hxpair) hcoefficient
    have hpartnerPair : ternaryDot
        (pointCoord1 p i (partner x)) (pointCoord2 p j (partner x))
        (pointCoord3 p k (partner x)) w1 w2 w3 =
        -(p : ℤ) * ((p : ℤ) * M x) := by
      rw [hxy.2.2.1, hxy.2.2.2.1, hxy.2.2.2.2.1]
      exact hflip
    have hM : M (partner x) = -M x := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hpne)
      calc
        (p : ℤ) ^ 2 * M (partner x) = ternaryDot
            (pointCoord1 p i (partner x)) (pointCoord2 p j (partner x))
            (pointCoord3 p k (partner x)) w1 w2 w3 := hypair.symm
        _ = -(p : ℤ) * ((p : ℤ) * M x) := hpartnerPair
        _ = (p : ℤ) ^ 2 * (-M x) := by ring
    have hc1 : pointCoord1 p i (partner (partner x)) = pointCoord1 p i x := by
      rw [hyz.2.2.1, hM]
      simpa only [mul_neg] using hxy.2.2.2.2.2.1
    have hc2 : pointCoord2 p j (partner (partner x)) = pointCoord2 p j x := by
      rw [hyz.2.2.2.1, hM]
      simpa only [mul_neg] using hxy.2.2.2.2.2.2.1
    have hc3 : pointCoord3 p k (partner (partner x)) = pointCoord3 p k x := by
      rw [hyz.2.2.2.2.1, hM]
      simpa only [mul_neg] using hxy.2.2.2.2.2.2.2
    apply Prod.ext
    · apply Prod.ext
      · exact quintBranchIndex_eq_of_coord_eq p i hpne _ _
          (by simpa [pointCoord1] using hc1)
      · exact quintBranchIndex_eq_of_coord_eq p j hpne _ _
          (by simpa [pointCoord2] using hc2)
    · exact quintBranchIndex_eq_of_coord_eq p k hpne _ _
        (by simpa [pointCoord3] using hc3)

/-- **Negative pairing-to-vanishing bridge.**

For the sign-corrected reflection, the affine root quotient
`t₀+p*M(x)` is preserved rather than negated.  Fixed coordinate-offset
identities place `-R` back in the three quintuple branch cosets.  The resulting
partner is again an honest sign-reversing involution of every contributing
point, hence cancels the actual product coefficient. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_negative_root_pairing
    (p i j k K : ℕ) (e c w1 w2 w3 t0 d1 d2 d3 : ℤ)
    (M : TripleQuintBranchIndex → ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hoffset1 : c * t0 * w1 = 12 * i + p * d1)
    (hoffset2 : c * t0 * w2 = 12 * j + p * d2)
    (hoffset3 : c * t0 * w3 = 12 * k + p * d3)
    (hpair : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      ternaryDot (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        w1 w2 w3 = (p : ℤ) * (t0 + (p : ℤ) * M x)) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  have hpne : (p : ℤ) ≠ 0 := by
    rintro hpzero
    obtain ⟨a, ha⟩ := hpodd
    omega
  let PartnerSpec : TripleQuintBranchIndex → TripleQuintBranchIndex → Prop :=
    fun x y =>
      pointBranchWeight y = -pointBranchWeight x ∧
      pointTripleExp2 p i j k y = pointTripleExp2 p i j k x ∧
      pointCoord1 p i y = -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w1
        (pointCoord1 p i x) ∧
      pointCoord2 p j y = -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w2
        (pointCoord2 p j x) ∧
      pointCoord3 p k y = -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w3
        (pointCoord3 p k x) ∧
      -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w1 (pointCoord1 p i y) =
        pointCoord1 p i x ∧
      -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w2 (pointCoord2 p j y) =
        pointCoord2 p j x ∧
      -shortRootReflectCoord c (t0 + (p : ℤ) * M x) w3 (pointCoord3 p k y) =
        pointCoord3 p k x
  have hexists : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      ∃ y, PartnerSpec x y := by
    intro x hexp
    obtain ⟨b1', b2', b3', z1, z2, z3, _hz1, _hz2, _hz3, hproduct,
        hcoord1, hcoord2, hcoord3, hexponent, hreturn1, hreturn2, hreturn3⟩ :=
      shortRoot_negative_eight_branch_matching
        (pointB1 x) (pointB2 x) (pointB3 x) p e c i j k w1 w2 w3 t0 (M x)
        d1 d2 d3 (pointN1 x) (pointN2 x) (pointN3 x) hpodd he hep hroot
        hcoefficient
        (by simpa [pointCoord1, pointCoord2, pointCoord3] using hpair x hexp)
        hoffset1 hoffset2 hoffset3
    let y : TripleQuintBranchIndex :=
      (((b1', -pointN1 x + z1), (b2', -pointN2 x + z2)),
        (b3', -pointN3 x + z3))
    refine ⟨y, ?_⟩
    dsimp [PartnerSpec]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
      rw [hproduct]
      simp [pointB1, pointB2, pointB3]
    · simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1,
        pointN2, pointN3] using hexponent.symm
    · simpa [pointCoord1, y, pointB1, pointN1] using hcoord1
    · simpa [pointCoord2, y, pointB2, pointN2] using hcoord2
    · simpa [pointCoord3, y, pointB3, pointN3] using hcoord3
    · simpa [pointCoord1, y, pointB1, pointN1] using hreturn1
    · simpa [pointCoord2, y, pointB2, pointN2] using hreturn2
    · simpa [pointCoord3, y, pointB3, pointN3] using hreturn3
  let partner : TripleQuintBranchIndex → TripleQuintBranchIndex := fun x =>
    if hx : pointTripleExp2 p i j k x = 2 * (K : ℤ) then
      Classical.choose (hexists x hx)
    else x
  have partner_spec : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      PartnerSpec x (partner x) := by
    intro x hexp
    dsimp [partner]
    simp only [dif_pos hexp]
    exact Classical.choose_spec (hexists x hexp)
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_expInvolution
    p i j k K partner hi hpi hj hpj hk hpk
  · intro x hexp
    exact (partner_spec x hexp).1
  · intro x hexp
    exact (partner_spec x hexp).2.1
  · intro x hexp
    have hxy := partner_spec x hexp
    have hyexp : pointTripleExp2 p i j k (partner x) = 2 * (K : ℤ) :=
      hxy.2.1.trans hexp
    have hyz := partner_spec (partner x) hyexp
    have hxpair := hpair x hexp
    have hypair := hpair (partner x) hyexp
    have hflip := shortRootReflect_flips_pairing (p : ℤ) e c
      (t0 + (p : ℤ) * M x) w1 w2 w3
      (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
      hroot hxpair hcoefficient
    have hpartnerPair : ternaryDot
        (pointCoord1 p i (partner x)) (pointCoord2 p j (partner x))
        (pointCoord3 p k (partner x)) w1 w2 w3 =
        (p : ℤ) * (t0 + (p : ℤ) * M x) := by
      rw [hxy.2.2.1, hxy.2.2.2.1, hxy.2.2.2.2.1]
      simp only [ternaryDot] at hflip ⊢
      linear_combination -hflip
    have hM : M (partner x) = M x := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hpne)
      have heq := hypair.symm.trans hpartnerPair
      linear_combination heq
    have hc1 : pointCoord1 p i (partner (partner x)) = pointCoord1 p i x := by
      rw [hyz.2.2.1, hM]
      exact hxy.2.2.2.2.2.1
    have hc2 : pointCoord2 p j (partner (partner x)) = pointCoord2 p j x := by
      rw [hyz.2.2.2.1, hM]
      exact hxy.2.2.2.2.2.2.1
    have hc3 : pointCoord3 p k (partner (partner x)) = pointCoord3 p k x := by
      rw [hyz.2.2.2.2.1, hM]
      exact hxy.2.2.2.2.2.2.2
    apply Prod.ext
    · apply Prod.ext
      · exact quintBranchIndex_eq_of_coord_eq p i hpne _ _
          (by simpa [pointCoord1] using hc1)
      · exact quintBranchIndex_eq_of_coord_eq p j hpne _ _
          (by simpa [pointCoord2] using hc2)
    · exact quintBranchIndex_eq_of_coord_eq p k hpne _ _
        (by simpa [pointCoord3] using hc3)

/-! ### Uniform projective-root vanishings -/

/-- **Uniform positive projective-root vanishing.**

A projective lift `w = lambda*v + p*a` of the factor vector, with short norm
`e*p`, forces the entire coefficient progression to vanish whenever its scalar
target expression is divisible by `p`.  This is the general theorem of which
the previously discovered `p=71` affine cancellation is one instance. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_positive_projectiveRoot
    (p i j k N R : ℕ)
    (lambda e c w1 w2 w3 a1 a2 a3 u h : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 1)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hvw : ternaryDot i j k w1 w2 w3 = p * u)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * lambda * R = w1 + w2 + w3 - 6 * u + p * h) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  let M : TripleQuintBranchIndex → ℤ := fun x =>
    h + 2 * lambda * pointResidueQuotient p i j k R x +
      2 * projectiveLiftBranchCorrection (pointB1 x) (pointB2 x) (pointB3 x)
        a1 a2 a3 (pointN1 x) (pointN2 x) (pointN3 x)
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_positive_root_pairing
    p i j k (p * N + R) e c w1 w2 w3 M hi hpi hj hpj hk hpk hpodd he hep
    hroot hcoefficient
  intro x hexp
  obtain ⟨q, hres⟩ := tripleLinearResidue_eq_progression
    (pointB1 x) (pointB2 x) (pointB3 x) p i j k N R
    (pointN1 x) (pointN2 x) (pointN3 x) hpodd (by
      simpa [pointTripleExp2] using hexp)
  have hpne : (p : ℤ) ≠ 0 := by
    rintro hpzero
    obtain ⟨z, hz⟩ := hpodd
    omega
  have hxExists : ∃ qx : ℤ, pointLinearResidue i j k x = R + (p : ℤ) * qx :=
    ⟨q, by simpa [pointLinearResidue] using hres⟩
  have hxquot := pointLinearResidue_eq_add_mul_quotient p i j k R x hxExists
  have hqx : pointResidueQuotient p i j k R x = q := by
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R x =
          pointLinearResidue i j k x - R := by linarith [hxquot]
      _ = (p : ℤ) * q := by
        simpa [pointLinearResidue] using congrArg (fun t => t - (R : ℤ)) hres
  have hpair := projectiveRoot_positive_target_pairing
    (pointB1 x) (pointB2 x) (pointB3 x) p lambda i j k w1 w2 w3
    a1 a2 a3 u (pointN1 x) (pointN2 x) (pointN3 x) R q h
    hw1 hw2 hw3 hvw hres htarget
  simpa [M, pointCoord1, pointCoord2, pointCoord3, hqx] using hpair

/-- **Uniform negative projective-root vanishing.**

When the projective target has a nonzero affine base, the single scalar
congruence `c*lambda*base = 12 (mod p)` generates all three coordinate offsets.
Together with the negative pairing bridge this cancels every coefficient in
the progression. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_negative_projectiveRoot
    (p i j k N R : ℕ)
    (lambda e c w1 w2 w3 a1 a2 a3 u base h : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 2)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hvw : ternaryDot i j k w1 w2 w3 = p * u)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hbase : base = 2 * lambda * R - (w1 + w2 + w3) + 6 * u)
    (htarget : c * lambda * base = 12 + p * h) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  let M : TripleQuintBranchIndex → ℤ := fun x =>
    2 * lambda * pointResidueQuotient p i j k R x +
      2 * projectiveLiftBranchCorrection (pointB1 x) (pointB2 x) (pointB3 x)
        a1 a2 a3 (pointN1 x) (pointN2 x) (pointN3 x)
  obtain ⟨hoffset1, hoffset2, hoffset3⟩ :=
    projectiveRoot_negative_coordinate_offsets p c lambda base i j k w1 w2 w3
      a1 a2 a3 h hw1 hw2 hw3 htarget
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_negative_root_pairing
    p i j k (p * N + R) e c w1 w2 w3 base
    (h * i + c * base * a1) (h * j + c * base * a2) (h * k + c * base * a3)
    M hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient
    hoffset1 hoffset2 hoffset3
  intro x hexp
  obtain ⟨q, hres⟩ := tripleLinearResidue_eq_progression
    (pointB1 x) (pointB2 x) (pointB3 x) p i j k N R
    (pointN1 x) (pointN2 x) (pointN3 x) hpodd (by
      simpa [pointTripleExp2] using hexp)
  have hpne : (p : ℤ) ≠ 0 := by
    rintro hpzero
    obtain ⟨z, hz⟩ := hpodd
    omega
  have hxExists : ∃ qx : ℤ, pointLinearResidue i j k x = R + (p : ℤ) * qx :=
    ⟨q, by simpa [pointLinearResidue] using hres⟩
  have hxquot := pointLinearResidue_eq_add_mul_quotient p i j k R x hxExists
  have hqx : pointResidueQuotient p i j k R x = q := by
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R x =
          pointLinearResidue i j k x - R := by linarith [hxquot]
      _ = (p : ℤ) * q := by
        simpa [pointLinearResidue] using congrArg (fun t => t - (R : ℤ)) hres
  have hpair := projectiveRoot_reflection_quotient
    (pointB1 x) (pointB2 x) (pointB3 x) p lambda i j k w1 w2 w3
    a1 a2 a3 u (pointN1 x) (pointN2 x) (pointN3 x) R q
    hw1 hw2 hw3 hvw hres
  rw [← hbase] at hpair
  simpa [M, pointCoord1, pointCoord2, pointCoord3, hqx, mul_assoc] using hpair

/-- **Root-to-Vanishing Theorem (uniform projective form).**

Every short projective root satisfying one of the two exact branch-closing
target laws forces the full arithmetic progression of coefficients of the
actual sparse triple quintuple product to vanish.  The disjunction is complete
for the two nonzero mod-three norm classes. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_projectiveRoot
    (p i j k N R : ℕ)
    (lambda e c w1 w2 w3 a1 a2 a3 u : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hvw : ternaryDot i j k w1 w2 w3 = p * u)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hcase :
      (((e * (p : ℤ) : ℤ) : ZMod 3) = 1 ∧
        ∃ h : ℤ, 2 * lambda * R = w1 + w2 + w3 - 6 * u + p * h) ∨
      (((e * (p : ℤ) : ℤ) : ZMod 3) = 2 ∧
        ∃ base h : ℤ,
          base = 2 * lambda * R - (w1 + w2 + w3) + 6 * u ∧
          c * lambda * base = 12 + p * h)) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rcases hcase with ⟨hep, h, htarget⟩ | ⟨hep, base, h, hbase, htarget⟩
  · exact coeff_tripleQuintupleSpecialized_eq_zero_of_positive_projectiveRoot
      p i j k N R lambda e c w1 w2 w3 a1 a2 a3 u h
      hi hpi hj hpj hk hpk hpodd he hep hw1 hw2 hw3 hvw hroot hcoefficient htarget
  · exact coeff_tripleQuintupleSpecialized_eq_zero_of_negative_projectiveRoot
      p i j k N R lambda e c w1 w2 w3 a1 a2 a3 u base h
      hi hpi hj hpj hk hpk hpodd he hep hw1 hw2 hw3 hvw hroot hcoefficient
      hbase htarget

/-- The direct-root quotient is the `lambda=1`, `a=0`, `u=e`
specialization of the projective law. -/
theorem projectiveRoot_quotient_specializes_to_direct
    (b1 b2 b3 : Bool) (p e i j k n1 n2 n3 r q : ℤ)
    (hroot : ternaryNorm i j k = e * p)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) i j k
      = p * (2 * r + 2 * p * q + 6 * e - (i + j + k)) := by
  have hvw : ternaryDot i j k i j k = p * e := by
    simpa [ternaryDot, ternaryNorm, pow_two, mul_comm] using hroot
  have h := projectiveRoot_reflection_quotient b1 b2 b3 p 1 i j k i j k
    0 0 0 e n1 n2 n3 r q (by ring) (by ring) (by ring) hvw hresidue
  have hcorrection :
      projectiveLiftBranchCorrection b1 b2 b3 0 0 0 n1 n2 n3 = 0 := by
    simp [projectiveLiftBranchCorrection, tripleLinearResidue]
  calc
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) i j k
        = p * (2 * 1 * r - (i + j + k) + 6 * e
            + p * (2 * 1 * q
              + 2 * projectiveLiftBranchCorrection b1 b2 b3 0 0 0 n1 n2 n3)) := h
    _ = p * (2 * r + 2 * p * q + 6 * e - (i + j + k)) := by
      rw [hcorrection]
      ring

/-! The two flagship residues are instances of the uniform target laws. -/

theorem p71_projectiveRoot_positive_target_formula :
    2 * 6 * (61 : ℤ) = 6 + (-5) + (-9) - 6 * (-5) + 71 * 10 := by
  norm_num

theorem p79_projectiveRoot_negative_target_formula :
    let base : ℤ := 2 * 1 * 9 - (1 + 6 + 11) + 6 * 2
    1 * 1 * base = 12 + 79 * 0 := by
  norm_num

/-- The uniform theorem recovers the non-direct `p=71`, residue-`61`
progression directly from the short projective root `(6,-5,-9)`. -/
theorem coeff_quintupleSpecialized_p71_sixtyOne_zero_by_uniform_projectiveRoot
    (N : ℕ) :
    coeff (71 * N + 61) (quintupleSpecialized 71 1 * quintupleSpecialized 71 11 *
      quintupleSpecialized 71 34) = 0 := by
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_positive_projectiveRoot
    71 1 11 34 N 61 6 2 1 6 (-5) (-9) 0 (-1) (-3) (-5) 10
  all_goals norm_num [ternaryDot, ternaryNorm]
  all_goals native_decide

/-- The same theorem recovers the direct `p=79`, residue-`9` progression as
the negative-sign specialization with affine base `12`. -/
theorem coeff_quintupleSpecialized_p79_nine_zero_by_uniform_projectiveRoot
    (N : ℕ) :
    coeff (79 * N + 9) (quintupleSpecialized 79 1 * quintupleSpecialized 79 6 *
      quintupleSpecialized 79 11) = 0 := by
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_negative_projectiveRoot
    79 1 6 11 N 9 1 2 1 1 6 11 0 0 0 2 12 0
  all_goals norm_num [ternaryDot, ternaryNorm]
  all_goals native_decide

end Ramanujan.MultiQuintuple
