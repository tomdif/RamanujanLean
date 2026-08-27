/-
# Projective short-root cancellation for sparse triple quintuple products

This file transports an exact affine reflection certificate through the finite
coefficient-box assembly.  It proves the non-direct `p=71` progression and the
direct-root `p=79` progression for the actual threefold Pochhammer products.
-/
import RamanujanTau.MultiQuintupleCancellation
import RamanujanTau.MultiQuintuplePaleySpinor

namespace Ramanujan.MultiQuintuple
open PowerSeries

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

lemma mem_tripleQuintBranchBox_of_exp
    (p i j k K : ℕ) (x : TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)) :
    x ∈ tripleQuintBranchBox K := by
  have hb := triplePoint_natAbs_le_add_one p i j k K x
    hi hpi hj hpj hk hpk hexp
  rw [tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_quintBranchBox_of_natAbs_le K _ _ hb.1,
      mem_quintBranchBox_of_natAbs_le K _ _ hb.2.1⟩,
    mem_quintBranchBox_of_natAbs_le K _ _ hb.2.2⟩

/-- A sign-reversing exponent-preserving involution on all contributing branch
points cancels the corresponding coefficient of the actual triple product. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_expInvolution
    (p i j k K : ℕ) (partner : TripleQuintBranchIndex → TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hweight : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      pointBranchWeight (partner x) = -pointBranchWeight x)
    (hexponent : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      pointTripleExp2 p i j k (partner x) = pointTripleExp2 p i j k x)
    (hinvolutive : ∀ x, pointTripleExp2 p i j k x = 2 * (K : ℤ) →
      partner (partner x) = x) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K
    hi hpi hj hpj hk hpk]
  let s := tripleQuintBranchBox K
  let partnerOnBox : ∀ x ∈ s, TripleQuintBranchIndex := fun x _ =>
    if hx : pointTripleExp2 p i j k x = 2 * (K : ℤ) then partner x else x
  have partner_mem : ∀ x (hx : x ∈ s), partnerOnBox x hx ∈ s := by
    intro x hx
    dsimp [partnerOnBox]
    split_ifs with hexp
    · apply mem_tripleQuintBranchBox_of_exp p i j k K
        (partner x) hi hpi hj hpj hk hpk
      exact (hexponent x hexp).trans hexp
    · exact hx
  change (∑ x ∈ s, pointContribution p i j k K x) = 0
  refine Finset.sum_involution partnerOnBox ?_ ?_ partner_mem ?_
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)
    · have hpartnerExp : pointTripleExp2 p i j k (partner x) = 2 * (K : ℤ) :=
        (hexponent x hexp).trans hexp
      simp [partnerOnBox, pointContribution, hexp, hpartnerExp, hweight x hexp]
    · simp [partnerOnBox, pointContribution, hexp]
  · intro x hx hnonzero
    have hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ) := by
      by_contra hne
      rw [pointContribution, if_neg hne] at hnonzero
      exact hnonzero rfl
    have hweightEq := hweight x hexp
    intro heq
    have hzero : pointBranchWeight x = 0 := by
      rw [show partnerOnBox x hx = partner x by simp [partnerOnBox, hexp]] at heq
      rw [heq] at hweightEq
      linarith
    rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
    cases b1 <;> cases b2 <;> cases b3 <;>
      norm_num [pointBranchWeight, pointB1, pointB2, pointB3, branchSign] at hzero
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)
    · have hpartnerExp : pointTripleExp2 p i j k (partner x) = 2 * (K : ℤ) :=
        (hexponent x hexp).trans hexp
      simp [partnerOnBox, hexp, hpartnerExp, hinvolutive x hexp]
    · simp [partnerOnBox, hexp]

def p71C0 (b1 b2 b3 : Bool) : ℤ :=
  match b1, b2, b3 with
  | false, false, false => 18
  | false, false, true => 65
  | false, true, false => 52
  | false, true, true => 28
  | true, false, false => 34
  | true, false, true => 10
  | true, true, false => 68
  | true, true, true => 44

def p71Q0 (b1 b2 b3 : Bool) : ℤ :=
  match b1, b2, b3 with
  | false, false, false => 25
  | false, false, true => 93
  | false, true, false => 74
  | false, true, true => 40
  | true, false, false => 48
  | true, false, true => 14
  | true, true, false => 97
  | true, true, true => 63

lemma p71_branch_constant (b1 b2 b3 : Bool) :
    (if b1 then 1 else 0) + 11 * (if b2 then 1 else 0) +
        34 * (if b3 then 1 else 0) + 102 * p71C0 b1 b2 b3 =
      61 + 71 * p71Q0 b1 b2 b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> norm_num [p71C0, p71Q0]

def p71FiberZ (x : TripleQuintBranchIndex) : ℤ :=
  (pointN3 x - 48 * pointN1 x - 31 * pointN2 x -
    p71C0 (pointB1 x) (pointB2 x) (pointB3 x)) / 71

lemma p71_fiber_representation (x : TripleQuintBranchIndex) (q : ℤ)
    (hresidue : pointLinearResidue 1 11 34 x = 61 + 71 * q) :
    pointN3 x = 48 * pointN1 x + 31 * pointN2 x +
      p71C0 (pointB1 x) (pointB2 x) (pointB3 x) + 71 * p71FiberZ x := by
  let d := pointN3 x - 48 * pointN1 x - 31 * pointN2 x -
    p71C0 (pointB1 x) (pointB2 x) (pointB3 x)
  let a := q - p71Q0 (pointB1 x) (pointB2 x) (pointB3 x) -
    69 * pointN1 x - 45 * pointN2 x
  have h102 : 102 * d = 71 * a := by
    have hc := p71_branch_constant (pointB1 x) (pointB2 x) (pointB3 x)
    dsimp [pointLinearResidue, tripleLinearResidue] at hresidue
    dsimp [d, a]
    linear_combination hresidue - hc
  have hdiv : (71 : ℤ) ∣ d := by
    refine ⟨55 * a - 79 * d, ?_⟩
    linear_combination 55 * h102
  obtain ⟨z, hz⟩ := hdiv
  have hquot : p71FiberZ x = z := by
    rw [p71FiberZ]
    change d / 71 = z
    rw [hz]
    norm_num
  dsimp [d] at hz
  rw [hquot]
  linarith

def p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    TripleQuintBranchIndex :=
  (((b1, n1), (b2, n2)),
    (b3, 48 * n1 + 31 * n2 + p71C0 b1 b2 b3 + 71 * z))

@[simp] lemma pointB1_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointB1 (p71FiberPoint b1 b2 b3 n1 n2 z) = b1 := rfl

@[simp] lemma pointB2_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointB2 (p71FiberPoint b1 b2 b3 n1 n2 z) = b2 := rfl

@[simp] lemma pointB3_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointB3 (p71FiberPoint b1 b2 b3 n1 n2 z) = b3 := rfl

@[simp] lemma pointN1_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointN1 (p71FiberPoint b1 b2 b3 n1 n2 z) = n1 := rfl

@[simp] lemma pointN2_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointN2 (p71FiberPoint b1 b2 b3 n1 n2 z) = n2 := rfl

@[simp] lemma pointN3_p71FiberPoint (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointN3 (p71FiberPoint b1 b2 b3 n1 n2 z) =
      48 * n1 + 31 * n2 + p71C0 b1 b2 b3 + 71 * z := rfl

@[simp] lemma mul_71_ediv_71 (z : ℤ) : z * 71 / 71 = z := by
  exact Int.mul_ediv_cancel z (by norm_num)

@[simp] lemma p71FiberZ_fiberPoint
    (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    p71FiberZ (p71FiberPoint b1 b2 b3 n1 n2 z) = z := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [p71FiberZ, p71FiberPoint, p71C0, pointB1, pointB2, pointB3,
      pointN1, pointN2, pointN3] <;>
    convert mul_71_ediv_71 z using 1 <;> ring

lemma eq_p71FiberPoint_of_residue (x : TripleQuintBranchIndex) (q : ℤ)
    (hresidue : pointLinearResidue 1 11 34 x = 61 + 71 * q) :
    x = p71FiberPoint (pointB1 x) (pointB2 x) (pointB3 x)
      (pointN1 x) (pointN2 x) (p71FiberZ x) := by
  have hrepr := p71_fiber_representation x q hresidue
  rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
  simpa [p71FiberPoint, pointB1, pointB2, pointB3, pointN1, pointN2, pointN3]
    using hrepr

def p71AffinePoint (b1 b2 b3 : Bool) (c0 cx cy cz x y z : ℤ) :
    TripleQuintBranchIndex :=
  let x' := reflect71AffineX cx x y z
  let y' := reflect71AffineY cy x y z
  let z' := reflect71AffineZ cz x y z
  (((b1, x'), (b2, y')), (b3, 48 * x' + 31 * y' + c0 + 71 * z'))

@[simp] lemma p71FiberZ_affinePoint
    (b1 b2 b3 : Bool) (c0 cx cy cz x y z : ℤ)
    (hc0 : c0 = p71C0 b1 b2 b3) :
    p71FiberZ (p71AffinePoint b1 b2 b3 c0 cx cy cz x y z) =
      reflect71AffineZ cz x y z := by
  subst c0
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [p71FiberZ, p71AffinePoint, p71C0, pointB1, pointB2, pointB3,
      pointN1, pointN2, pointN3] <;>
    convert mul_71_ediv_71 (reflect71AffineZ cz x y z) using 1 <;> ring

/-- The affine reflection on a point already parameterized in one residue coset. -/
def p71PartnerFiber (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    TripleQuintBranchIndex :=
  match b1, b2, b3 with
  | false, false, false => p71FiberPoint false true false
      (reflect71AffineX 14 n1 n2 z) (reflect71AffineY (-12) n1 n2 z)
      (reflect71AffineZ (-5) n1 n2 z)
  | false, true, false => p71FiberPoint false false false
      (reflect71AffineX 40 n1 n2 z) (reflect71AffineY (-33) n1 n2 z)
      (reflect71AffineZ (-13) n1 n2 z)
  | false, true, true => p71FiberPoint false false true
      (reflect71AffineX 22 n1 n2 z) (reflect71AffineY (-18) n1 n2 z)
      (reflect71AffineZ (-8) n1 n2 z)
  | false, false, true => p71FiberPoint false true true
      (reflect71AffineX 50 n1 n2 z) (reflect71AffineY (-42) n1 n2 z)
      (reflect71AffineZ (-16) n1 n2 z)
  | true, false, true => p71FiberPoint true true true
      (reflect71AffineX 8 n1 n2 z) (reflect71AffineY (-7) n1 n2 z)
      (reflect71AffineZ (-3) n1 n2 z)
  | true, true, true => p71FiberPoint true false true
      (reflect71AffineX 34 n1 n2 z) (reflect71AffineY (-28) n1 n2 z)
      (reflect71AffineZ (-11) n1 n2 z)
  | true, true, false => p71FiberPoint true false false
      (reflect71AffineX 52 n1 n2 z) (reflect71AffineY (-43) n1 n2 z)
      (reflect71AffineZ (-17) n1 n2 z)
  | true, false, false => p71FiberPoint true true false
      (reflect71AffineX 26 n1 n2 z) (reflect71AffineY (-22) n1 n2 z)
      (reflect71AffineZ (-9) n1 n2 z)

/-- The exact eight-coset affine reflection for `(71;1,11,34)`. -/
def p71Partner (x : TripleQuintBranchIndex) : TripleQuintBranchIndex :=
  p71PartnerFiber (pointB1 x) (pointB2 x) (pointB3 x)
    (pointN1 x) (pointN2 x) (p71FiberZ x)

@[simp] lemma p71Partner_fiberPoint
    (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    p71Partner (p71FiberPoint b1 b2 b3 n1 n2 z) =
      p71PartnerFiber b1 b2 b3 n1 n2 z := by
  simp only [p71Partner, pointB1_p71FiberPoint, pointB2_p71FiberPoint,
    pointB3_p71FiberPoint, pointN1_p71FiberPoint, pointN2_p71FiberPoint,
    p71FiberZ_fiberPoint]

lemma p71Partner_weight (x : TripleQuintBranchIndex) :
    pointBranchWeight (p71Partner x) = -pointBranchWeight x := by
  rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    norm_num [p71Partner, p71PartnerFiber, p71FiberPoint,
      pointBranchWeight, pointB1, pointB2,
      pointB3, pointN1, pointN2, pointN3, branchSign]

lemma p71Partner_preserves_exponent_fiberPoint
    (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    pointTripleExp2 71 1 11 34 (p71Partner (p71FiberPoint b1 b2 b3 n1 n2 z)) =
      pointTripleExp2 71 1 11 34 (p71FiberPoint b1 b2 b3 n1 n2 z) := by
  cases b1 <;> cases b2 <;> cases b3
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 false true false 52
        (reflect71AffineX 14 n1 n2 z) (reflect71AffineY (-12) n1 n2 z)
        (reflect71AffineZ (-5) n1 n2 z) =
      restrictedTripleExp2_71 false false false 18 n1 n2 z
    exact (p71_branch_pair_000_010 n1 n2 z).symm
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 false true true 28
        (reflect71AffineX 50 n1 n2 z) (reflect71AffineY (-42) n1 n2 z)
        (reflect71AffineZ (-16) n1 n2 z) =
      restrictedTripleExp2_71 false false true 65 n1 n2 z
    simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY,
      reflect71AffineZ, reflect71X, reflect71Y, reflect71Z,
      quintExp2, quintExpA2, quintExpB2]
    ring
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 false false false 18
        (reflect71AffineX 40 n1 n2 z) (reflect71AffineY (-33) n1 n2 z)
        (reflect71AffineZ (-13) n1 n2 z) =
      restrictedTripleExp2_71 false true false 52 n1 n2 z
    simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY,
      reflect71AffineZ, reflect71X, reflect71Y, reflect71Z,
      quintExp2, quintExpA2, quintExpB2]
    ring
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 false false true 65
        (reflect71AffineX 22 n1 n2 z) (reflect71AffineY (-18) n1 n2 z)
        (reflect71AffineZ (-8) n1 n2 z) =
      restrictedTripleExp2_71 false true true 28 n1 n2 z
    exact (p71_branch_pair_011_001 n1 n2 z).symm
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 true true false 68
        (reflect71AffineX 26 n1 n2 z) (reflect71AffineY (-22) n1 n2 z)
        (reflect71AffineZ (-9) n1 n2 z) =
      restrictedTripleExp2_71 true false false 34 n1 n2 z
    simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY,
      reflect71AffineZ, reflect71X, reflect71Y, reflect71Z,
      quintExp2, quintExpA2, quintExpB2]
    ring
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 true true true 44
        (reflect71AffineX 8 n1 n2 z) (reflect71AffineY (-7) n1 n2 z)
        (reflect71AffineZ (-3) n1 n2 z) =
      restrictedTripleExp2_71 true false true 10 n1 n2 z
    exact (p71_branch_pair_101_111 n1 n2 z).symm
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 true false false 34
        (reflect71AffineX 52 n1 n2 z) (reflect71AffineY (-43) n1 n2 z)
        (reflect71AffineZ (-17) n1 n2 z) =
      restrictedTripleExp2_71 true true false 68 n1 n2 z
    exact (p71_branch_pair_110_100 n1 n2 z).symm
  · rw [p71Partner_fiberPoint]
    change restrictedTripleExp2_71 true false true 10
        (reflect71AffineX 34 n1 n2 z) (reflect71AffineY (-28) n1 n2 z)
        (reflect71AffineZ (-11) n1 n2 z) =
      restrictedTripleExp2_71 true true true 44 n1 n2 z
    simp [restrictedTripleExp2_71, reflect71AffineX, reflect71AffineY,
      reflect71AffineZ, reflect71X, reflect71Y, reflect71Z,
      quintExp2, quintExpA2, quintExpB2]
    ring

lemma p71Partner_involutive_fiberPoint
    (b1 b2 b3 : Bool) (n1 n2 z : ℤ) :
    p71Partner (p71Partner (p71FiberPoint b1 b2 b3 n1 n2 z)) =
      p71FiberPoint b1 b2 b3 n1 n2 z := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [p71Partner_fiberPoint, p71PartnerFiber] <;>
    simp [p71FiberPoint, reflect71AffineX, reflect71AffineY, reflect71AffineZ,
      reflect71X, reflect71Y, reflect71Z] <;>
    ring_nf <;>
    simp

lemma p71Partner_preserves_exponent_of_residue
    (x : TripleQuintBranchIndex) (q : ℤ)
    (hresidue : pointLinearResidue 1 11 34 x = 61 + 71 * q) :
    pointTripleExp2 71 1 11 34 (p71Partner x) =
      pointTripleExp2 71 1 11 34 x := by
  rw [eq_p71FiberPoint_of_residue x q hresidue]
  exact p71Partner_preserves_exponent_fiberPoint _ _ _ _ _ _

lemma p71Partner_involutive_of_residue
    (x : TripleQuintBranchIndex) (q : ℤ)
    (hresidue : pointLinearResidue 1 11 34 x = 61 + 71 * q) :
    p71Partner (p71Partner x) = x := by
  rw [eq_p71FiberPoint_of_residue x q hresidue]
  exact p71Partner_involutive_fiberPoint _ _ _ _ _ _

lemma p71_target_point_has_residue (N : ℕ) (x : TripleQuintBranchIndex)
    (hexp : pointTripleExp2 71 1 11 34 x = 2 * ((71 * N + 61 : ℕ) : ℤ)) :
    ∃ q : ℤ, pointLinearResidue 1 11 34 x = 61 + 71 * q := by
  obtain ⟨q, hq⟩ := tripleLinearResidue_eq_progression
    (pointB1 x) (pointB2 x) (pointB3 x) 71 1 11 34 N 61
    (pointN1 x) (pointN2 x) (pointN3 x) (⟨35, by norm_num⟩) (by
      simpa [pointTripleExp2] using hexp)
  exact ⟨q, by simpa [pointLinearResidue] using hq⟩

/-- **The non-direct projective-root vanishing at `p=71`.**  The affine
reflection attached to `(6,-5,-9) ≡ 6(1,11,34)` cancels every coefficient
in the progression `71*N+61` of the actual three-factor product. -/
theorem coeff_quintupleSpecialized_p71_sixtyOne_zero (N : ℕ) :
    coeff (71 * N + 61) (quintupleSpecialized 71 1 * quintupleSpecialized 71 11 *
      quintupleSpecialized 71 34) = 0 := by
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_expInvolution
    71 1 11 34 (71 * N + 61) p71Partner
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro x hexp
    exact p71Partner_weight x
  · intro x hexp
    obtain ⟨q, hq⟩ := p71_target_point_has_residue N x hexp
    exact p71Partner_preserves_exponent_of_residue x q hq
  · intro x hexp
    obtain ⟨q, hq⟩ := p71_target_point_has_residue N x hexp
    exact p71Partner_involutive_of_residue x q hq

/-- **The direct-root vanishing at `p=79`.**  Here `(1,6,11)` itself has
norm `2*79`, so the universal short-root capstone gives residue `9`. -/
theorem coeff_quintupleSpecialized_p79_nine_zero (N : ℕ) :
    coeff (79 * N + 9) (quintupleSpecialized 79 1 * quintupleSpecialized 79 6 *
      quintupleSpecialized 79 11) = 0 := by
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_negative_shortRoot
    79 1 6 11 N 9 2 1 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨39, by norm_num⟩
  · exact Or.inr rfl
  · have hthree : (3 : ZMod 3) = 0 := by decide
    change (158 : ZMod 3) = 2
    linear_combination 52 * hthree
  · norm_num [ternaryNorm]
  · norm_num
  · norm_num

end Ramanujan.MultiQuintuple
