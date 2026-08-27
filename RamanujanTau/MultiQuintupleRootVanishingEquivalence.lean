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

These theorems close the quotient/residue interface in the forward
root-to-vanishing direction.  The construction of all eight target branches
and the converse assertion that every vanishing must arise from such a root
remain separate steps; no biconditional is asserted here.
-/
import RamanujanTau.MultiQuintupleProjectiveCancellation

namespace Ramanujan.MultiQuintuple

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

end Ramanujan.MultiQuintuple
