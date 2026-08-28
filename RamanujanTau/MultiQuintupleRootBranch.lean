/-
# Short-root transport of the three bilateral quintuple branches

The completed-square coordinate of one specialized quintuple summand is

  `Y_b(p,i,n) = 6*p*n + 6*i + (2*b-1)*p`,  `b in {0,1}`.

For three factors, equality of the sum of the three squared coordinates is exactly
equality of the doubled product exponent.  Consequently a short-root Householder
reflection gives an exponent-preserving branch map as soon as its three output
coordinates land in target branch cosets.  This file proves that reusable bridge.

The final section records the two universal target-residue formulas for a direct
three-square root `w=(i,j,k)`, `||w||^2=e*p`.  The identity for the reflection quotient
is the key calculation behind the automatic eight-branch certificate.
-/
import RamanujanTau.MultiQuintupleRootConverse

namespace Ramanujan.MultiQuintuple

/-- The three-branch doubled exponent. -/
def tripleQuintExp2
    (b1 b2 b3 : Bool) (p i j k n1 n2 n3 : ℤ) : ℤ :=
  quintExp2 b1 p i n1 + quintExp2 b2 p j n2 + quintExp2 b3 p k n3

/-- The three completed-square coordinates. -/
def tripleQuintNorm
    (b1 b2 b3 : Bool) (p i j k n1 n2 n3 : ℤ) : ℤ :=
  quintLatticeCoord b1 p i n1 ^ 2
    + quintLatticeCoord b2 p j n2 ^ 2
    + quintLatticeCoord b3 p k n3 ^ 2

/-- Square completion for a triple product, with a branch-independent offset. -/
theorem tripleQuintExp2_square_completion
    (b1 b2 b3 : Bool) (p i j k n1 n2 n3 : ℤ) :
    12 * p * tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
        + (6 * i - p) ^ 2 + (6 * j - p) ^ 2 + (6 * k - p) ^ 2
      = tripleQuintNorm b1 b2 b3 p i j k n1 n2 n3 := by
  simp only [tripleQuintExp2, tripleQuintNorm]
  have h1 := quintExp2_square_completion b1 p i n1
  have h2 := quintExp2_square_completion b2 p j n2
  have h3 := quintExp2_square_completion b3 p k n3
  linear_combination h1 + h2 + h3

/-- Equal completed norms imply equal doubled exponents when `p` is nonzero. -/
theorem tripleQuintExp2_eq_of_norm_eq
    (b1 b2 b3 b1' b2' b3' : Bool) (p i j k n1 n2 n3 n1' n2' n3' : ℤ)
    (hp : p ≠ 0)
    (hnorm : tripleQuintNorm b1 b2 b3 p i j k n1 n2 n3
      = tripleQuintNorm b1' b2' b3' p i j k n1' n2' n3') :
    tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
      = tripleQuintExp2 b1' b2' b3' p i j k n1' n2' n3' := by
  have hs := tripleQuintExp2_square_completion b1 b2 b3 p i j k n1 n2 n3
  have ht := tripleQuintExp2_square_completion b1' b2' b3' p i j k n1' n2' n3'
  have hmul : 12 * p * tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
      = 12 * p * tripleQuintExp2 b1' b2' b3' p i j k n1' n2' n3' := by
    linear_combination hs - ht + hnorm
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (12 : ℤ) ≠ 0) hp) hmul

/-- Multiplying all three coordinates by a sign does not change their square norm. -/
theorem ternaryNorm_sign (sigma x y z : ℤ) (hsigma : sigma ^ 2 = 1) :
    ternaryNorm (sigma * x) (sigma * y) (sigma * z) = ternaryNorm x y z := by
  simp only [ternaryNorm]
  calc
    (sigma * x) ^ 2 + (sigma * y) ^ 2 + (sigma * z) ^ 2
        = sigma ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    _ = x ^ 2 + y ^ 2 + z ^ 2 := by rw [hsigma]; ring

/-- **Root-to-branch exponent transport.**

If the signed Householder images of the three source completed-square coordinates
are target completed-square coordinates, then the associated triple-product summands
have exactly equal exponent.  This is the generic theorem consumed by emitted affine
branch certificates. -/
theorem shortRoot_preserves_tripleQuintExp2
    (source1 source2 source3 target1 target2 target3 : Bool)
    (p e c sigma i j k w1 w2 w3 t
      n1 n2 n3 n1' n2' n3' : ℤ)
    (hp : p ≠ 0)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hcoefficient : c * e = 2)
    (hsigma : sigma ^ 2 = 1)
    (hpairing : ternaryDot
      (quintLatticeCoord source1 p i n1)
      (quintLatticeCoord source2 p j n2)
      (quintLatticeCoord source3 p k n3) w1 w2 w3 = p * t)
    (hcoord1 : quintLatticeCoord target1 p i n1'
      = sigma * shortRootReflectCoord c t w1 (quintLatticeCoord source1 p i n1))
    (hcoord2 : quintLatticeCoord target2 p j n2'
      = sigma * shortRootReflectCoord c t w2 (quintLatticeCoord source2 p j n2))
    (hcoord3 : quintLatticeCoord target3 p k n3'
      = sigma * shortRootReflectCoord c t w3 (quintLatticeCoord source3 p k n3)) :
    tripleQuintExp2 source1 source2 source3 p i j k n1 n2 n3
      = tripleQuintExp2 target1 target2 target3 p i j k n1' n2' n3' := by
  apply tripleQuintExp2_eq_of_norm_eq source1 source2 source3 target1 target2 target3
    p i j k n1 n2 n3 n1' n2' n3' hp
  simp only [tripleQuintNorm, hcoord1, hcoord2, hcoord3]
  change ternaryNorm
      (quintLatticeCoord source1 p i n1)
      (quintLatticeCoord source2 p j n2)
      (quintLatticeCoord source3 p k n3)
    = ternaryNorm
      (sigma * shortRootReflectCoord c t w1 (quintLatticeCoord source1 p i n1))
      (sigma * shortRootReflectCoord c t w2 (quintLatticeCoord source2 p j n2))
      (sigma * shortRootReflectCoord c t w3 (quintLatticeCoord source3 p k n3))
  rw [ternaryNorm_sign sigma _ _ _ hsigma,
    shortRootReflect_preserves_norm p e c t w1 w2 w3
      (quintLatticeCoord source1 p i n1)
      (quintLatticeCoord source2 p j n2)
      (quintLatticeCoord source3 p k n3) hroot hpairing hcoefficient]

/-! ### The universal direct-root residue calculation -/

/-- The linear residue expression selecting a coefficient progression. -/
def tripleLinearResidue
    (b1 b2 b3 : Bool) (i j k n1 n2 n3 : ℤ) : ℤ :=
  i * (3 * n1 + if b1 then 1 else 0)
    + j * (3 * n2 + if b2 then 1 else 0)
    + k * (3 * n3 + if b3 then 1 else 0)

/-- Sign coordinate `2b-1` for a bilateral branch bit. -/
def branchSign (b : Bool) : ℤ := if b then 1 else -1

/-- For a direct root `(i,j,k)` of norm `e*p`, the Householder quotient of a
completed-square branch point depends only on its coefficient residue quotient:

`t = 2*r + 2*p*q + 6*e - (i+j+k)`.

This is the identity from which both target residues follow. -/
theorem directRoot_reflection_quotient
    (b1 b2 b3 : Bool) (p e i j k n1 n2 n3 r q : ℤ)
    (hroot : ternaryNorm i j k = e * p)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) i j k
      = p * (2 * r + 2 * p * q + 6 * e - (i + j + k)) := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [ternaryNorm, ternaryDot, tripleLinearResidue, quintLatticeCoord]
      at hroot hresidue ⊢ <;>
    linear_combination 6 * hroot + 2 * p * hresidue

/-- At the positive-reflection target residue `2r = i+j+k-6e (mod p)`,
the root pairing is a multiple of `p^2`. -/
theorem directRoot_positive_target_pairing
    (b1 b2 b3 : Bool) (p e i j k n1 n2 n3 r q h : ℤ)
    (hroot : ternaryNorm i j k = e * p)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k - 6 * e + p * h) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) i j k
      = p ^ 2 * (h + 2 * q) := by
  rw [directRoot_reflection_quotient b1 b2 b3 p e i j k n1 n2 n3 r q hroot hresidue,
    htarget]
  ring

/-- At the negative-reflection target residue `2r = i+j+k (mod p)`, the root
pairing differs from a multiple of `p^2` by the universal shift `6e*p`. -/
theorem directRoot_negative_target_pairing
    (b1 b2 b3 : Bool) (p e i j k n1 n2 n3 r q h : ℤ)
    (hroot : ternaryNorm i j k = e * p)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k + p * h) :
    ternaryDot
        (quintLatticeCoord b1 p i n1)
        (quintLatticeCoord b2 p j n2)
        (quintLatticeCoord b3 p k n3) i j k
      = p * (p * (h + 2 * q) + 6 * e) := by
  rw [directRoot_reflection_quotient b1 b2 b3 p e i j k n1 n2 n3 r q hroot hresidue,
    htarget]
  ring

/-! ### The finite mod-3 mechanism selecting the sign -/

local instance finiteForallDecidable {alpha : Type*} [Fintype alpha]
    {P : alpha → Prop} [DecidablePred P] : Decidable (∀ x, P x) :=
  Fintype.decidableForallFintype


set_option maxRecDepth 10000

/-- Bundling the finite residue data keeps the exhaustive decision procedure shallow. -/
structure Mod3BranchInput where
  epc : ZMod 3 × ZMod 3 × ZMod 3
  root : ZMod 3 × ZMod 3 × ZMod 3
  residue : ZMod 3 × ZMod 3 × ZMod 3
  bits : Bool × Bool × Bool
  deriving DecidableEq, Fintype

namespace Mod3BranchInput
def e (x : Mod3BranchInput) := x.epc.1
def p (x : Mod3BranchInput) := x.epc.2.1
def c (x : Mod3BranchInput) := x.epc.2.2
def w1 (x : Mod3BranchInput) := x.root.1
def w2 (x : Mod3BranchInput) := x.root.2.1
def w3 (x : Mod3BranchInput) := x.root.2.2
def r (x : Mod3BranchInput) := x.residue.1
def q (x : Mod3BranchInput) := x.residue.2.1
def h (x : Mod3BranchInput) := x.residue.2.2
def b1 (x : Mod3BranchInput) := x.bits.1
def b2 (x : Mod3BranchInput) := x.bits.2.1
def b3 (x : Mod3BranchInput) := x.bits.2.2
end Mod3BranchInput

/-- Branch sign in `ZMod 3`. -/
def branchSign3 (b : Bool) : ZMod 3 := if b then 1 else -1

/-- When the root norm is `1 mod 3`, the positive Householder reflection sends
every branch sign vector to another nonzero sign vector and reverses the product
of its three signs.  This finite lemma exhausts the exact `3^8 * 2^3` residue
calculation; it is a theorem of `ZMod 3`, not an experimental prime scan. -/
theorem directRoot_positive_mod3 :
    ∀ input : Mod3BranchInput,
      input.e * input.p = 1 →
      input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2 = input.e * input.p →
      input.c * input.e = 2 →
      2 * input.r = input.w1 + input.w2 + input.w3 + input.p * input.h →
      input.w1 * (if input.b1 then 1 else 0)
          + input.w2 * (if input.b2 then 1 else 0)
          + input.w3 * (if input.b3 then 1 else 0) = input.r + input.p * input.q →
      let m := input.h + 2 * input.q
      let u1 := branchSign3 input.b1 - input.c * m * input.w1
      let u2 := branchSign3 input.b2 - input.c * m * input.w2
      let u3 := branchSign3 input.b3 - input.c * m * input.w3
      u1 ≠ 0 ∧ u2 ≠ 0 ∧ u3 ≠ 0
        ∧ u1 * u2 * u3
          = -(branchSign3 input.b1 * branchSign3 input.b2 * branchSign3 input.b3) := by
  native_decide

/-- When the root norm is `2 mod 3`, the negative Householder reflection is the
one that preserves the branch cube and reverses branch parity. -/
theorem directRoot_negative_mod3 :
    ∀ input : Mod3BranchInput,
      input.e * input.p = 2 →
      input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2 = input.e * input.p →
      input.c * input.e = 2 →
      2 * input.r = input.w1 + input.w2 + input.w3 + input.p * input.h →
      input.w1 * (if input.b1 then 1 else 0)
          + input.w2 * (if input.b2 then 1 else 0)
          + input.w3 * (if input.b3 then 1 else 0) = input.r + input.p * input.q →
      let m := input.h + 2 * input.q
      let u1 := branchSign3 input.b1 - input.c * m * input.w1
      let u2 := branchSign3 input.b2 - input.c * m * input.w2
      let u3 := branchSign3 input.b3 - input.c * m * input.w3
      u1 ≠ 0 ∧ u2 ≠ 0 ∧ u3 ≠ 0
        ∧ (-u1) * (-u2) * (-u3)
          = -(branchSign3 input.b1 * branchSign3 input.b2 * branchSign3 input.b3) := by
  native_decide

/-! ### Lifting the finite calculation to the integral branch cube -/

/-- The three residues modulo three, in branch-sign form. -/
lemma zmod3_zero_or_branchSign :
    ∀ u : ZMod 3, u = 0 ∨ u = 1 ∨ u = -1 := by
  decide

/-- Every nonzero residue modulo three is one of the two branch signs. -/
lemma zmod3_eq_branchSign3 {u : ZMod 3} (hu : u ≠ 0) :
    u = 1 ∨ u = -1 := by
  rcases zmod3_zero_or_branchSign u with h | h | h
  · exact (hu h).elim
  · exact Or.inl h
  · exact Or.inr h

/-- An odd integer not divisible by three lies in exactly one of the two completed-square
branch cosets modulo six.  This is the CRT lift from the finite mod-three calculation. -/
lemma exists_branch_of_odd_of_mod3_ne_zero (u : ℤ) (huodd : Odd u)
    (hu3 : (u : ZMod 3) ≠ 0) :
    ∃ b : Bool, ∃ z : ℤ, u = branchSign b + 6 * z := by
  rcases zmod3_eq_branchSign3 hu3 with hu | hu
  · have hdvd : (3 : ℤ) ∣ u - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u - 1) 3).mp
      simpa using sub_eq_zero.mpr hu
    obtain ⟨a, ha⟩ := hdvd
    obtain ⟨d, hd⟩ := huodd
    have hthree : (3 : ℤ) ∣ d := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one (a := 3) (b := 2) (c := d)
      · exact ⟨a, by omega⟩
      · norm_num
    obtain ⟨z, hz⟩ := hthree
    exact ⟨true, z, by simp [branchSign]; omega⟩
  · have hdvd : (3 : ℤ) ∣ u - (-1) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u - (-1)) 3).mp
      simpa using sub_eq_zero.mpr hu
    obtain ⟨a, ha⟩ := hdvd
    obtain ⟨d, hd⟩ := huodd
    have hthree : (3 : ℤ) ∣ d + 1 := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one (a := 3) (b := 2) (c := d + 1)
      · exact ⟨a, by omega⟩
      · norm_num
    obtain ⟨z, hz⟩ := hthree
    exact ⟨false, z, by simp [branchSign]; omega⟩

/-- Equality of products of branch signs modulo three is already equality over the
integers, because both sides are `1` or `-1`. -/
lemma branchSign_product_eq_of_mod3
    (a1 a2 a3 b1 b2 b3 : Bool)
    (h : (branchSign3 a1 * branchSign3 a2 * branchSign3 a3)
      = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3)) :
    branchSign a1 * branchSign a2 * branchSign a3
      = -(branchSign b1 * branchSign b2 * branchSign b3) := by
  have hall : ∀ a1 a2 a3 b1 b2 b3 : Bool,
      (branchSign3 a1 * branchSign3 a2 * branchSign3 a3)
          = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) →
        branchSign a1 * branchSign a2 * branchSign a3
          = -(branchSign b1 * branchSign b2 * branchSign b3) := by
    decide
  exact hall a1 a2 a3 b1 b2 b3 h

/-- Every branch sign is odd. -/
lemma branchSign_odd (b : Bool) : Odd (branchSign b) := by
  cases b
  · exact ⟨-1, rfl⟩
  · exact ⟨0, rfl⟩

/-- The parity of a square equals the parity of its base, summed over three
coordinates.  In particular a root of norm `2p` has even coordinate sum. -/
lemma directRoot_sum_even_of_norm_two_mul
    (p i j k : ℤ) (hroot : ternaryNorm i j k = 2 * p) :
    Even (i + j + k) := by
  have hcast := congrArg (fun x : ℤ => (x : ZMod 2)) hroot
  have hsquare (x : ZMod 2) : x ^ 2 = x := by
    fin_cases x <;> decide
  have hzero : ((i + j + k : ℤ) : ZMod 2) = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    simpa [ternaryNorm, hsquare, htwo] using hcast
  have hdvd : (2 : ℤ) ∣ i + j + k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (i + j + k) 2).mp hzero
  obtain ⟨d, hd⟩ := hdvd
  exact ⟨d, by omega⟩

/-- Casting the positive-target hypotheses into the finite theorem gives the three
nonzero output residues and the sign-product reversal. -/
lemma directRoot_positive_integral_mod3
    (b1 b2 b3 : Bool) (p e c i j k r q h n1 n2 n3 : ℤ)
    (hep : ((e * p : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k - 6 * e + p * h) :
    let m := h + 2 * q
    let u1 := branchSign b1 - c * m * i
    let u2 := branchSign b2 - c * m * j
    let u3 := branchSign b3 - c * m * k
    ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) := by
  let input : Mod3BranchInput :=
    ⟨(e, p, c), (i, j, k), (r, q, h), (b1, b2, b3)⟩
  have heq := directRoot_positive_mod3 input
  have hep' : input.e * input.p = 1 := by
    simpa [input, Mod3BranchInput.e, Mod3BranchInput.p] using hep
  have hroot' : input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2
      = input.e * input.p := by
    simpa [input, Mod3BranchInput.w1, Mod3BranchInput.w2, Mod3BranchInput.w3,
      Mod3BranchInput.e, Mod3BranchInput.p, ternaryNorm]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hroot
  have hc' : input.c * input.e = 2 := by
    simpa [input, Mod3BranchInput.c, Mod3BranchInput.e]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hcoefficient
  have ht' : 2 * input.r = input.w1 + input.w2 + input.w3 + input.p * input.h := by
    have hsix : (6 : ZMod 3) = 0 := by decide
    simpa [input, Mod3BranchInput.r, Mod3BranchInput.w1, Mod3BranchInput.w2,
      Mod3BranchInput.w3, Mod3BranchInput.p, Mod3BranchInput.h, hsix]
      using congrArg (fun x : ℤ => (x : ZMod 3)) htarget
  have hr' : input.w1 * (if input.b1 then 1 else 0)
        + input.w2 * (if input.b2 then 1 else 0)
        + input.w3 * (if input.b3 then 1 else 0) = input.r + input.p * input.q := by
    have hthree : (3 : ZMod 3) = 0 := by decide
    change (i : ZMod 3) * (if b1 then 1 else 0)
        + (j : ZMod 3) * (if b2 then 1 else 0)
        + (k : ZMod 3) * (if b3 then 1 else 0) = r + p * q
    cases b1 <;> cases b2 <;> cases b3 <;>
      simpa [tripleLinearResidue, hthree]
        using congrArg (fun x : ℤ => (x : ZMod 3)) hresidue
  simpa [input, Mod3BranchInput.e, Mod3BranchInput.p, Mod3BranchInput.c,
    Mod3BranchInput.w1, Mod3BranchInput.w2, Mod3BranchInput.w3,
    Mod3BranchInput.r, Mod3BranchInput.q, Mod3BranchInput.h,
    Mod3BranchInput.b1, Mod3BranchInput.b2, Mod3BranchInput.b3,
    branchSign, branchSign3]
    using heq hep' hroot' hc' ht' hr'

/-- The same cast bridge for the negative-reflection target. -/
lemma directRoot_negative_integral_mod3
    (b1 b2 b3 : Bool) (p e c i j k r q h n1 n2 n3 : ℤ)
    (hep : ((e * p : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k + p * h) :
    let m := h + 2 * q
    let u1 := branchSign b1 - c * m * i
    let u2 := branchSign b2 - c * m * j
    let u3 := branchSign b3 - c * m * k
    ((u1 : ℤ) : ZMod 3) ≠ 0 ∧ ((u2 : ℤ) : ZMod 3) ≠ 0
      ∧ ((u3 : ℤ) : ZMod 3) ≠ 0
      ∧ ((-u1 : ℤ) : ZMod 3) * ((-u2 : ℤ) : ZMod 3) * ((-u3 : ℤ) : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) := by
  let input : Mod3BranchInput :=
    ⟨(e, p, c), (i, j, k), (r, q, h), (b1, b2, b3)⟩
  have heq := directRoot_negative_mod3 input
  have hep' : input.e * input.p = 2 := by
    simpa [input, Mod3BranchInput.e, Mod3BranchInput.p] using hep
  have hroot' : input.w1 ^ 2 + input.w2 ^ 2 + input.w3 ^ 2
      = input.e * input.p := by
    simpa [input, Mod3BranchInput.w1, Mod3BranchInput.w2, Mod3BranchInput.w3,
      Mod3BranchInput.e, Mod3BranchInput.p, ternaryNorm]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hroot
  have hc' : input.c * input.e = 2 := by
    simpa [input, Mod3BranchInput.c, Mod3BranchInput.e]
      using congrArg (fun x : ℤ => (x : ZMod 3)) hcoefficient
  have ht' : 2 * input.r = input.w1 + input.w2 + input.w3 + input.p * input.h := by
    simpa [input, Mod3BranchInput.r, Mod3BranchInput.w1, Mod3BranchInput.w2,
      Mod3BranchInput.w3, Mod3BranchInput.p, Mod3BranchInput.h]
      using congrArg (fun x : ℤ => (x : ZMod 3)) htarget
  have hr' : input.w1 * (if input.b1 then 1 else 0)
        + input.w2 * (if input.b2 then 1 else 0)
        + input.w3 * (if input.b3 then 1 else 0) = input.r + input.p * input.q := by
    have hthree : (3 : ZMod 3) = 0 := by decide
    change (i : ZMod 3) * (if b1 then 1 else 0)
        + (j : ZMod 3) * (if b2 then 1 else 0)
        + (k : ZMod 3) * (if b3 then 1 else 0) = r + p * q
    cases b1 <;> cases b2 <;> cases b3 <;>
      simpa [tripleLinearResidue, hthree]
        using congrArg (fun x : ℤ => (x : ZMod 3)) hresidue
  simpa [input, Mod3BranchInput.e, Mod3BranchInput.p, Mod3BranchInput.c,
    Mod3BranchInput.w1, Mod3BranchInput.w2, Mod3BranchInput.w3,
    Mod3BranchInput.r, Mod3BranchInput.q, Mod3BranchInput.h,
    Mod3BranchInput.b1, Mod3BranchInput.b2, Mod3BranchInput.b3,
    branchSign, branchSign3]
    using heq hep' hroot' hc' ht' hr'

/-- The reflected branch residues are odd for either short-root norm. -/
lemma directRoot_output_odd
    (b : Bool) (w p e c i j k r q h : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * r = i + j + k - 6 * e + p * h) :
    Odd (branchSign b - c * (h + 2 * q) * w) := by
  obtain ⟨d, hd⟩ := branchSign_odd b
  rcases he with rfl | rfl
  · have hc : c = 2 := by omega
    refine ⟨d - (h + 2 * q) * w, ?_⟩
    rw [hc, hd]
    ring
  · have hc : c = 1 := by omega
    have hsum := directRoot_sum_even_of_norm_two_mul p i j k (by simpa using hroot)
    have hpone : (p : ZMod 2) = 1 := by
      obtain ⟨a, ha⟩ := hpodd
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [ha]
      simp [htwo]
    have hheven : Even h := by
      have htcast := congrArg (fun x : ℤ => (x : ZMod 2)) htarget
      have hsumzero : ((i + j + k : ℤ) : ZMod 2) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (i + j + k) 2).mpr
        exact hsum.two_dvd
      have hhzero : (h : ZMod 2) = 0 := by
        have htwo : (2 : ZMod 2) = 0 := by decide
        have hsix : (6 : ZMod 2) = 0 := by decide
        have htwelve : (12 : ZMod 2) = 0 := by decide
        simpa [htwo, hsix, htwelve, hpone, hsumzero] using htcast.symm
      exact even_iff_two_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd h 2).mp hhzero)
    obtain ⟨v, hv⟩ := hheven
    refine ⟨d - (v + q) * w, ?_⟩
    rw [hc, hd, hv]
    ring

/-- Negating an odd reflected residue keeps it odd. -/
lemma directRoot_negative_output_odd
    (b : Bool) (w p e c i j k r q h : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * r = i + j + k + p * h) :
    Odd (-(branchSign b - c * (h + 2 * q) * w)) := by
  obtain ⟨d, hd⟩ := branchSign_odd b
  rcases he with rfl | rfl
  · have hc : c = 2 := by omega
    refine ⟨-d + (h + 2 * q) * w - 1, ?_⟩
    rw [hc, hd]
    ring
  · have hc : c = 1 := by omega
    have hsum := directRoot_sum_even_of_norm_two_mul p i j k (by simpa using hroot)
    have hpone : (p : ZMod 2) = 1 := by
      obtain ⟨a, ha⟩ := hpodd
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [ha]
      simp [htwo]
    have hheven : Even h := by
      have htcast := congrArg (fun x : ℤ => (x : ZMod 2)) htarget
      have hsumzero : ((i + j + k : ℤ) : ZMod 2) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (i + j + k) 2).mpr
        exact hsum.two_dvd
      have hhzero : (h : ZMod 2) = 0 := by
        have htwo : (2 : ZMod 2) = 0 := by decide
        simpa [htwo, hpone, hsumzero] using htcast.symm
      exact even_iff_two_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd h 2).mp hhzero)
    obtain ⟨v, hv⟩ := hheven
    refine ⟨-d + (v + q) * w - 1, ?_⟩
    rw [hc, hd, hv]
    ring

/-- Completed-square coordinates written uniformly using `branchSign`. -/
lemma quintLatticeCoord_eq_branchSign (b : Bool) (p i n : ℤ) :
    quintLatticeCoord b p i n = 6 * p * n + 6 * i + p * branchSign b := by
  cases b <;> simp [quintLatticeCoord, branchSign]

/-- The signed reflection used in the negative residue case is also an involution. -/
lemma negativeShortRootReflect_involutive (c t w x : ℤ) :
    -shortRootReflectCoord c t w (-shortRootReflectCoord c t w x) = x := by
  simp [shortRootReflectCoord]

/-- **Universal positive eight-branch matching.**

For a direct root `(i,j,k)` of norm `p` or `2p`, if `e*p = 1 (mod 3)` then
the positive Householder reflection pairs every one of the eight bilateral branches
with a branch of opposite sign.  The theorem returns the three target bits, their
affine integer shifts, preservation of the selected residue, equality of exponents,
and the coordinatewise return identities proving that the pairing is involutive. -/
theorem directRoot_positive_eight_branch_matching
    (b1 b2 b3 : Bool) (p e c i j k n1 n2 n3 r q h : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hep : ((e * p : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k - 6 * e + p * h) :
    ∃ b1' b2' b3' : Bool, ∃ z1 z2 z3 : ℤ,
      branchSign b1 - c * (h + 2 * q) * i = branchSign b1' + 6 * z1
        ∧ branchSign b2 - c * (h + 2 * q) * j = branchSign b2' + 6 * z2
        ∧ branchSign b3 - c * (h + 2 * q) * k = branchSign b3' + 6 * z3
        ∧ branchSign b1' * branchSign b2' * branchSign b3'
          = -(branchSign b1 * branchSign b2 * branchSign b3)
        ∧ tripleLinearResidue b1' b2' b3' i j k (n1 + z1) (n2 + z2) (n3 + z3)
          = r + p * (-h - q)
        ∧ quintLatticeCoord b1' p i (n1 + z1)
          = shortRootReflectCoord c (p * (h + 2 * q)) i (quintLatticeCoord b1 p i n1)
        ∧ quintLatticeCoord b2' p j (n2 + z2)
          = shortRootReflectCoord c (p * (h + 2 * q)) j (quintLatticeCoord b2 p j n2)
        ∧ quintLatticeCoord b3' p k (n3 + z3)
          = shortRootReflectCoord c (p * (h + 2 * q)) k (quintLatticeCoord b3 p k n3)
        ∧ tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
          = tripleQuintExp2 b1' b2' b3' p i j k (n1 + z1) (n2 + z2) (n3 + z3)
        ∧ shortRootReflectCoord c (-(p * (h + 2 * q))) i
            (quintLatticeCoord b1' p i (n1 + z1)) = quintLatticeCoord b1 p i n1
        ∧ shortRootReflectCoord c (-(p * (h + 2 * q))) j
            (quintLatticeCoord b2' p j (n2 + z2)) = quintLatticeCoord b2 p j n2
        ∧ shortRootReflectCoord c (-(p * (h + 2 * q))) k
            (quintLatticeCoord b3' p k (n3 + z3)) = quintLatticeCoord b3 p k n3 := by
  let m : ℤ := h + 2 * q
  let u1 : ℤ := branchSign b1 - c * m * i
  let u2 : ℤ := branchSign b2 - c * m * j
  let u3 : ℤ := branchSign b3 - c * m * k
  have hmod := directRoot_positive_integral_mod3 b1 b2 b3
    p e c i j k r q h n1 n2 n3 hep hroot hcoefficient hresidue htarget
  change ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ (u1 : ZMod 3) * (u2 : ZMod 3) * (u3 : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) at hmod
  have hu1odd : Odd u1 := by
    exact directRoot_output_odd b1 i p e c i j k r q h hpodd he hroot hcoefficient htarget
  have hu2odd : Odd u2 := by
    exact directRoot_output_odd b2 j p e c i j k r q h hpodd he hroot hcoefficient htarget
  have hu3odd : Odd u3 := by
    exact directRoot_output_odd b3 k p e c i j k r q h hpodd he hroot hcoefficient htarget
  obtain ⟨b1', z1, hz1⟩ := exists_branch_of_odd_of_mod3_ne_zero u1 hu1odd hmod.1
  obtain ⟨b2', z2, hz2⟩ := exists_branch_of_odd_of_mod3_ne_zero u2 hu2odd hmod.2.1
  obtain ⟨b3', z3, hz3⟩ := exists_branch_of_odd_of_mod3_ne_zero u3 hu3odd hmod.2.2.1
  have hproduct3 : branchSign3 b1' * branchSign3 b2' * branchSign3 b3'
      = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) := by
    have hsix : (6 : ZMod 3) = 0 := by decide
    simpa [branchSign3, branchSign, hz1, hz2, hz3, hsix] using hmod.2.2.2
  have hproduct := branchSign_product_eq_of_mod3 b1' b2' b3' b1 b2 b3 hproduct3
  have hcoord1 : quintLatticeCoord b1' p i (n1 + z1)
      = shortRootReflectCoord c (p * m) i (quintLatticeCoord b1 p i n1) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord]
    dsimp [u1] at hz1
    linear_combination -p * hz1
  have hcoord2 : quintLatticeCoord b2' p j (n2 + z2)
      = shortRootReflectCoord c (p * m) j (quintLatticeCoord b2 p j n2) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord]
    dsimp [u2] at hz2
    linear_combination -p * hz2
  have hcoord3 : quintLatticeCoord b3' p k (n3 + z3)
      = shortRootReflectCoord c (p * m) k (quintLatticeCoord b3 p k n3) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord]
    dsimp [u3] at hz3
    linear_combination -p * hz3
  have hpair : ternaryDot
      (quintLatticeCoord b1 p i n1) (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) i j k = p * (p * m) := by
    simpa [m, pow_two, mul_assoc] using
      directRoot_positive_target_pairing b1 b2 b3 p e i j k n1 n2 n3 r q h
        hroot hresidue htarget
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hexponent : tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
      = tripleQuintExp2 b1' b2' b3' p i j k (n1 + z1) (n2 + z2) (n3 + z3) :=
    shortRoot_preserves_tripleQuintExp2 b1 b2 b3 b1' b2' b3'
      p e c 1 i j k i j k (p * m) n1 n2 n3 (n1 + z1) (n2 + z2) (n3 + z3)
      hpne hroot hcoefficient (by norm_num) hpair
      (by simpa using hcoord1) (by simpa using hcoord2) (by simpa using hcoord3)
  let targetResidue := tripleLinearResidue b1' b2' b3' i j k
    (n1 + z1) (n2 + z2) (n3 + z3)
  have htargetPair : ternaryDot
      (quintLatticeCoord b1' p i (n1 + z1))
      (quintLatticeCoord b2' p j (n2 + z2))
      (quintLatticeCoord b3' p k (n3 + z3)) i j k = -p * (p * m) := by
    rw [hcoord1, hcoord2, hcoord3]
    exact shortRootReflect_flips_pairing p e c (p * m) i j k
      (quintLatticeCoord b1 p i n1) (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) hroot hpair hcoefficient
  have hformula := directRoot_reflection_quotient b1' b2' b3' p e i j k
    (n1 + z1) (n2 + z2) (n3 + z3) targetResidue 0 hroot (by simp [targetResidue])
  have hcancel : 2 * targetResidue + 6 * e - (i + j + k) = -p * m := by
    apply mul_left_cancel₀ hpne
    calc
      p * (2 * targetResidue + 6 * e - (i + j + k))
          = ternaryDot
              (quintLatticeCoord b1' p i (n1 + z1))
              (quintLatticeCoord b2' p j (n2 + z2))
              (quintLatticeCoord b3' p k (n3 + z3)) i j k := by
                simpa using hformula.symm
      _ = -p * (p * m) := htargetPair
      _ = p * (-p * m) := by ring
  have htargetResidue : targetResidue = r + p * (-h - q) := by
    dsimp [m] at hcancel
    nlinarith [htarget]
  refine ⟨b1', b2', b3', z1, z2, z3, ?_⟩
  change u1 = _ ∧ u2 = _ ∧ u3 = _ ∧ _
  refine ⟨hz1, hz2, hz3, hproduct, ?_⟩
  refine ⟨by simpa [targetResidue] using htargetResidue, ?_⟩
  dsimp [m] at hcoord1 hcoord2 hcoord3 hexponent
  refine ⟨hcoord1, hcoord2, hcoord3, hexponent, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoord1]
    exact shortRootReflect_involutive c (p * (h + 2 * q)) i _
  · rw [hcoord2]
    exact shortRootReflect_involutive c (p * (h + 2 * q)) j _
  · rw [hcoord3]
    exact shortRootReflect_involutive c (p * (h + 2 * q)) k _

/-- **Universal negative eight-branch matching.**

When `e*p = 2 (mod 3)`, the sign-corrected reflection `-R` is the unique choice
that closes on the eight bilateral branches.  It again reverses the branch product,
preserves the selected coefficient residue and exponent, and squares to the identity. -/
theorem directRoot_negative_eight_branch_matching
    (b1 b2 b3 : Bool) (p e c i j k n1 n2 n3 r q h : ℤ)
    (hpodd : Odd p) (he : e = 1 ∨ e = 2)
    (hep : ((e * p : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm i j k = e * p)
    (hcoefficient : c * e = 2)
    (hresidue : tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q)
    (htarget : 2 * r = i + j + k + p * h) :
    ∃ b1' b2' b3' : Bool, ∃ z1 z2 z3 : ℤ,
      -(branchSign b1 - c * (h + 2 * q) * i) = branchSign b1' + 6 * z1
        ∧ -(branchSign b2 - c * (h + 2 * q) * j) = branchSign b2' + 6 * z2
        ∧ -(branchSign b3 - c * (h + 2 * q) * k) = branchSign b3' + 6 * z3
        ∧ branchSign b1' * branchSign b2' * branchSign b3'
          = -(branchSign b1 * branchSign b2 * branchSign b3)
        ∧ tripleLinearResidue b1' b2' b3' i j k (-n1 + z1) (-n2 + z2) (-n3 + z3)
          = r + p * q
        ∧ quintLatticeCoord b1' p i (-n1 + z1)
          = -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) i
              (quintLatticeCoord b1 p i n1)
        ∧ quintLatticeCoord b2' p j (-n2 + z2)
          = -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) j
              (quintLatticeCoord b2 p j n2)
        ∧ quintLatticeCoord b3' p k (-n3 + z3)
          = -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) k
              (quintLatticeCoord b3 p k n3)
        ∧ tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
          = tripleQuintExp2 b1' b2' b3' p i j k (-n1 + z1) (-n2 + z2) (-n3 + z3)
        ∧ -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) i
            (quintLatticeCoord b1' p i (-n1 + z1)) = quintLatticeCoord b1 p i n1
        ∧ -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) j
            (quintLatticeCoord b2' p j (-n2 + z2)) = quintLatticeCoord b2 p j n2
        ∧ -shortRootReflectCoord c (p * (h + 2 * q) + 6 * e) k
            (quintLatticeCoord b3' p k (-n3 + z3)) = quintLatticeCoord b3 p k n3 := by
  let m : ℤ := h + 2 * q
  let t : ℤ := p * m + 6 * e
  let u1 : ℤ := branchSign b1 - c * m * i
  let u2 : ℤ := branchSign b2 - c * m * j
  let u3 : ℤ := branchSign b3 - c * m * k
  have hmod := directRoot_negative_integral_mod3 b1 b2 b3
    p e c i j k r q h n1 n2 n3 hep hroot hcoefficient hresidue htarget
  change ((u1 : ZMod 3) ≠ 0) ∧ ((u2 : ZMod 3) ≠ 0) ∧ ((u3 : ZMod 3) ≠ 0)
      ∧ ((-u1 : ℤ) : ZMod 3) * ((-u2 : ℤ) : ZMod 3) * ((-u3 : ℤ) : ZMod 3)
        = -((branchSign b1 : ZMod 3) * (branchSign b2 : ZMod 3)
          * (branchSign b3 : ZMod 3)) at hmod
  have hu1odd : Odd (-u1) := by
    exact directRoot_negative_output_odd b1 i p e c i j k r q h
      hpodd he hroot hcoefficient htarget
  have hu2odd : Odd (-u2) := by
    exact directRoot_negative_output_odd b2 j p e c i j k r q h
      hpodd he hroot hcoefficient htarget
  have hu3odd : Odd (-u3) := by
    exact directRoot_negative_output_odd b3 k p e c i j k r q h
      hpodd he hroot hcoefficient htarget
  have hu1mod : ((-u1 : ℤ) : ZMod 3) ≠ 0 := by simpa using neg_ne_zero.mpr hmod.1
  have hu2mod : ((-u2 : ℤ) : ZMod 3) ≠ 0 := by simpa using neg_ne_zero.mpr hmod.2.1
  have hu3mod : ((-u3 : ℤ) : ZMod 3) ≠ 0 := by simpa using neg_ne_zero.mpr hmod.2.2.1
  obtain ⟨b1', z1, hz1⟩ := exists_branch_of_odd_of_mod3_ne_zero (-u1) hu1odd hu1mod
  obtain ⟨b2', z2, hz2⟩ := exists_branch_of_odd_of_mod3_ne_zero (-u2) hu2odd hu2mod
  obtain ⟨b3', z3, hz3⟩ := exists_branch_of_odd_of_mod3_ne_zero (-u3) hu3odd hu3mod
  have hproduct3 : branchSign3 b1' * branchSign3 b2' * branchSign3 b3'
      = -(branchSign3 b1 * branchSign3 b2 * branchSign3 b3) := by
    have hsix : (6 : ZMod 3) = 0 := by decide
    simpa [branchSign3, branchSign, hz1, hz2, hz3, hsix] using hmod.2.2.2
  have hproduct := branchSign_product_eq_of_mod3 b1' b2' b3' b1 b2 b3 hproduct3
  have hcoord1 : quintLatticeCoord b1' p i (-n1 + z1)
      = -shortRootReflectCoord c t i (quintLatticeCoord b1 p i n1) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, t]
    dsimp [u1] at hz1
    linear_combination -p * hz1 - 6 * i * hcoefficient
  have hcoord2 : quintLatticeCoord b2' p j (-n2 + z2)
      = -shortRootReflectCoord c t j (quintLatticeCoord b2 p j n2) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, t]
    dsimp [u2] at hz2
    linear_combination -p * hz2 - 6 * j * hcoefficient
  have hcoord3 : quintLatticeCoord b3' p k (-n3 + z3)
      = -shortRootReflectCoord c t k (quintLatticeCoord b3 p k n3) := by
    rw [quintLatticeCoord_eq_branchSign, quintLatticeCoord_eq_branchSign]
    dsimp [shortRootReflectCoord, t]
    dsimp [u3] at hz3
    linear_combination -p * hz3 - 6 * k * hcoefficient
  have hpair : ternaryDot
      (quintLatticeCoord b1 p i n1) (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) i j k = p * t := by
    simpa [t, m, mul_assoc] using
      directRoot_negative_target_pairing b1 b2 b3 p e i j k n1 n2 n3 r q h
        hroot hresidue htarget
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hexponent : tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3
      = tripleQuintExp2 b1' b2' b3' p i j k (-n1 + z1) (-n2 + z2) (-n3 + z3) :=
    shortRoot_preserves_tripleQuintExp2 b1 b2 b3 b1' b2' b3'
      p e c (-1) i j k i j k t n1 n2 n3 (-n1 + z1) (-n2 + z2) (-n3 + z3)
      hpne hroot hcoefficient (by norm_num) hpair
      (by simpa using hcoord1) (by simpa using hcoord2) (by simpa using hcoord3)
  let targetResidue := tripleLinearResidue b1' b2' b3' i j k
    (-n1 + z1) (-n2 + z2) (-n3 + z3)
  have hreflectPair := shortRootReflect_flips_pairing p e c t i j k
    (quintLatticeCoord b1 p i n1) (quintLatticeCoord b2 p j n2)
    (quintLatticeCoord b3 p k n3) hroot hpair hcoefficient
  have htargetPair : ternaryDot
      (quintLatticeCoord b1' p i (-n1 + z1))
      (quintLatticeCoord b2' p j (-n2 + z2))
      (quintLatticeCoord b3' p k (-n3 + z3)) i j k = p * t := by
    rw [hcoord1, hcoord2, hcoord3]
    simp only [ternaryDot] at hreflectPair ⊢
    linear_combination -hreflectPair
  have hformula := directRoot_reflection_quotient b1' b2' b3' p e i j k
    (-n1 + z1) (-n2 + z2) (-n3 + z3) targetResidue 0 hroot (by simp [targetResidue])
  have hcancel : 2 * targetResidue + 6 * e - (i + j + k) = t := by
    apply mul_left_cancel₀ hpne
    calc
      p * (2 * targetResidue + 6 * e - (i + j + k))
          = ternaryDot
              (quintLatticeCoord b1' p i (-n1 + z1))
              (quintLatticeCoord b2' p j (-n2 + z2))
              (quintLatticeCoord b3' p k (-n3 + z3)) i j k := by
                simpa using hformula.symm
      _ = p * t := htargetPair
  have htargetResidue : targetResidue = r + p * q := by
    dsimp [t, m] at hcancel
    nlinarith [htarget]
  refine ⟨b1', b2', b3', z1, z2, z3, ?_⟩
  change -u1 = _ ∧ -u2 = _ ∧ -u3 = _ ∧ _
  refine ⟨hz1, hz2, hz3, hproduct, ?_⟩
  refine ⟨by simpa [targetResidue] using htargetResidue, ?_⟩
  dsimp [t, m] at hcoord1 hcoord2 hcoord3 hexponent
  refine ⟨hcoord1, hcoord2, hcoord3, hexponent, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoord1]
    exact negativeShortRootReflect_involutive c (p * (h + 2 * q) + 6 * e) i _
  · rw [hcoord2]
    exact negativeShortRootReflect_involutive c (p * (h + 2 * q) + 6 * e) j _
  · rw [hcoord3]
    exact negativeShortRootReflect_involutive c (p * (h + 2 * q) + 6 * e) k _

end Ramanujan.MultiQuintuple
