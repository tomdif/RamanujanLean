/-
# Arithmetic lattice extracted from coherent theta cancellation

The eight Watson branches admit a simpler affine coordinate.  Writing

  m_s = 3 n_s + b_s,

the completed square coordinate is

  6 p n_s + 6 i_s + (2 b_s - 1) p
    = (6 i_s - p) + 2 p m_s.

The progression condition is exactly `i*m₁+j*m₂+k*m₃ = R (mod p)`.
This file proves that every vector in the corresponding homogeneous
congruence lattice is a difference of two Watson points in the affine fiber.
Consequently a coherent rational theta involution acts integrally on the
entire index-`p` congruence lattice, which is the arithmetic input required
by the primitive Householder converse.
-/
import RamanujanTau.MultiQuintupleThetaRigidity

namespace Ramanujan.MultiQuintuple

/-- Integral affine indices `m_s=3n_s+b_s` behind the Watson branches. -/
abbrev TernaryIntIndex := (ℤ × ℤ) × ℤ

/-- A branch bit as the integer zero or one. -/
def branchBitInt (b : Bool) : ℤ := if b then 1 else 0

/-- The affine index of a bilateral branch point. -/
def pointAffineIndex (x : TripleQuintBranchIndex) : TernaryIntIndex :=
  ((3 * pointN1 x + branchBitInt (pointB1 x),
    3 * pointN2 x + branchBitInt (pointB2 x)),
    3 * pointN3 x + branchBitInt (pointB3 x))

/-- Dot product of the quintuple-index vector with an affine index. -/
def affineIndexDot (i j k : ℤ) (m : TernaryIntIndex) : ℤ :=
  i * m.1.1 + j * m.1.2 + k * m.2

/-- The branch-independent origin in completed-square coordinates. -/
def thetaAffineBase (p i j k : ℤ) : TernaryIntPoint :=
  ((6 * i - p, 6 * j - p), 6 * k - p)

/-- Coordinatewise multiplication of an integral ternary point. -/
def ternaryIntScale (c : ℤ) (x : TernaryIntPoint) : TernaryIntPoint :=
  ((c * x.1.1, c * x.1.2), c * x.2)

lemma quintLatticeCoord_eq_affineIndex
    (b : Bool) (p i n : ℤ) :
    quintLatticeCoord b p i n =
      (6 * i - p) + 2 * p * (3 * n + branchBitInt b) := by
  cases b <;> simp [quintLatticeCoord, branchBitInt] <;> ring

/-- Exact affine-coordinate formula for every completed Watson point. -/
theorem pointThetaVector_eq_affineBase_add
    (p i j k : ℕ) (x : TripleQuintBranchIndex) :
    pointThetaVector p i j k x =
      thetaAffineBase p i j k +
        ternaryIntScale (2 * (p : ℤ)) (pointAffineIndex x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [pointThetaVector, pointCoord1, pointAffineIndex,
        thetaAffineBase, ternaryIntScale, Prod.fst_add]
      rw [quintLatticeCoord_eq_affineIndex]
    · simp only [pointThetaVector, pointCoord2, pointAffineIndex,
        thetaAffineBase, ternaryIntScale, Prod.fst_add, Prod.snd_add]
      rw [quintLatticeCoord_eq_affineIndex]
  · simp only [pointThetaVector, pointCoord3, pointAffineIndex,
      thetaAffineBase, ternaryIntScale, Prod.snd_add]
    rw [quintLatticeCoord_eq_affineIndex]

/-- The linear residue is exactly the dot product in affine-index
coordinates. -/
lemma pointLinearResidue_eq_affineIndexDot
    (i j k : ℕ) (x : TripleQuintBranchIndex) :
    pointLinearResidue i j k x = affineIndexDot i j k (pointAffineIndex x) := by
  rfl

/-- Homogeneous index-`p` congruence lattice. -/
def InThetaIndexLattice (p i j k : ℕ) (d : TernaryIntIndex) : Prop :=
  (p : ℤ) ∣ affineIndexDot i j k d

/-- One affine residue fiber in index coordinates. -/
def InThetaIndexFiber (p i j k R : ℕ) (m : TernaryIntIndex) : Prop :=
  ∃ q : ℤ, affineIndexDot i j k m = R + (p : ℤ) * q

lemma inThetaResidueFiber_iff_affineIndex
    (p i j k R : ℕ) (x : TripleQuintBranchIndex) :
    InThetaResidueFiber p i j k R x ↔
      InThetaIndexFiber p i j k R (pointAffineIndex x) := by
  rfl

/-- Every integer displacement can be realized between two one-dimensional
Watson indices.  The source and target residues modulo three are chosen from
`{0,1}`; this is the elementary reason the eight branches span all
differences even though they do not cover every index. -/
lemma exists_watson_branch_step (d : ℤ) :
    ∃ b b' : Bool, ∃ n : ℤ,
      3 * n + branchBitInt b' = branchBitInt b + d := by
  have hnonneg := Int.emod_nonneg d (by norm_num : (3 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos d (by norm_num : (0 : ℤ) < 3)
  have hdecomp := Int.mul_ediv_add_emod d 3
  have hcases : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · refine ⟨false, false, d / 3, ?_⟩
    simp [branchBitInt]
    omega
  · refine ⟨false, true, d / 3, ?_⟩
    simp [branchBitInt]
    omega
  · refine ⟨true, false, d / 3 + 1, ?_⟩
    simp [branchBitInt]
    omega

/-- An explicit integer Bézout inverse for `3i` modulo `p` lets every
homogeneous lattice vector be realized as a difference of two Watson points
in the same affine fiber. -/
theorem thetaIndexLattice_difference_spanning_of_bezout
    (p i j k R : ℕ) (d : TernaryIntIndex)
    (bp bv : ℤ) (hunit : bp * p + bv * (3 * i) = 1)
    (hd : InThetaIndexLattice p i j k d) :
    ∃ x y : TripleQuintBranchIndex,
      InThetaResidueFiber p i j k R x ∧
      InThetaResidueFiber p i j k R y ∧
      pointAffineIndex y = pointAffineIndex x + d := by
  obtain ⟨b1, b1', n1, hn1⟩ := exists_watson_branch_step d.1.1
  obtain ⟨b2, b2', n2, hn2⟩ := exists_watson_branch_step d.1.2
  obtain ⟨b3, b3', n3, hn3⟩ := exists_watson_branch_step d.2
  let base : ℤ :=
    (i : ℤ) * branchBitInt b1 + (j : ℤ) * branchBitInt b2 +
      (k : ℤ) * branchBitInt b3
  let t : ℤ := bv * ((R : ℤ) - base)
  let x : TripleQuintBranchIndex := (((b1, t), (b2, 0)), (b3, 0))
  let y : TripleQuintBranchIndex :=
    (((b1', t + n1), (b2', n2)), (b3', n3))
  have hxindex : pointAffineIndex x =
      ((3 * t + branchBitInt b1, branchBitInt b2), branchBitInt b3) := by
    simp [x, pointAffineIndex, pointB1, pointB2, pointB3,
      pointN1, pointN2, pointN3]
  have hyindex : pointAffineIndex y =
      ((3 * (t + n1) + branchBitInt b1',
        3 * n2 + branchBitInt b2'),
        3 * n3 + branchBitInt b3') := by
    simp [y, pointAffineIndex, pointB1, pointB2, pointB3,
      pointN1, pointN2, pointN3]
  have hdiff : pointAffineIndex y = pointAffineIndex x + d := by
    rw [hxindex, hyindex]
    apply Prod.ext
    · apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      · linear_combination hn1
      · linear_combination hn2
    · simp only [Prod.snd_add]
      linear_combination hn3
  have hxfiber : InThetaResidueFiber p i j k R x := by
    rw [inThetaResidueFiber_iff_affineIndex, InThetaIndexFiber, hxindex]
    refine ⟨-bp * ((R : ℤ) - base), ?_⟩
    dsimp [affineIndexDot, base, t]
    linear_combination ((R : ℤ) - base) * hunit
  have hdotadd : affineIndexDot i j k (pointAffineIndex x + d) =
      affineIndexDot i j k (pointAffineIndex x) + affineIndexDot i j k d := by
    rcases pointAffineIndex x with ⟨⟨x1, x2⟩, x3⟩
    rcases d with ⟨⟨d1, d2⟩, d3⟩
    simp [affineIndexDot]
    ring
  obtain ⟨s, hs⟩ := hd
  obtain ⟨q, hq⟩ := (inThetaResidueFiber_iff_affineIndex
    p i j k R x).mp hxfiber
  have hyfiber : InThetaResidueFiber p i j k R y := by
    rw [inThetaResidueFiber_iff_affineIndex, InThetaIndexFiber, hdiff, hdotadd,
      hq, hs]
    exact ⟨q + s, by ring⟩
  exact ⟨x, y, hxfiber, hyfiber, hdiff⟩

lemma affineIndexDot_sub (i j k : ℤ) (x y : TernaryIntIndex) :
    affineIndexDot i j k (x - y) =
      affineIndexDot i j k x - affineIndexDot i j k y := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  simp [affineIndexDot]
  ring

/-- Rational cast of an affine index. -/
def ternaryIntIndexToRat (x : TernaryIntIndex) : TernaryRatPoint :=
  (((x.1.1 : ℚ), (x.1.2 : ℚ)), (x.2 : ℚ))

lemma ternaryIntIndexToRat_injective :
    Function.Injective ternaryIntIndexToRat := by
  intro x y h
  exact ternaryIntPointToRat_injective h

lemma ternaryRatDot_smul_right (c : ℚ) (x y : TernaryRatPoint) :
    ternaryRatDot x (c • y) = c * ternaryRatDot x y := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  simp [ternaryRatDot]
  ring

lemma ternaryRatNorm_smul (c : ℚ) (x : TernaryRatPoint) :
    ternaryRatNorm (c • x) = c ^ 2 * ternaryRatNorm x := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  simp [ternaryRatNorm]
  ring

/-- Householder reflection depends only on the projective normal line. -/
theorem ternaryRatHouseholder_smul_normal
    (c : ℚ) (hc : c ≠ 0) (w : TernaryRatPoint) (hw : w ≠ 0)
    (x : TernaryRatPoint) :
    ternaryRatHouseholder (c • w) x = ternaryRatHouseholder w x := by
  have hnorm : ternaryRatNorm w ≠ 0 :=
    ne_of_gt (ternaryRatNorm_pos hw)
  rw [ternaryRatHouseholder, ternaryRatHouseholder,
    ternaryRatDot_smul_right, ternaryRatNorm_smul]
  rw [smul_smul]
  congr 1
  field_simp [hc, hnorm]

/-- A positive common denominator for three rational coordinates. -/
def ternaryRatCommonDenom (w : TernaryRatPoint) : ℕ :=
  w.1.1.den * w.1.2.den * w.2.den

/-- Integral normal obtained by clearing all three rational denominators. -/
def clearTernaryRatDenominators (w : TernaryRatPoint) : TernaryIntIndex :=
  ((w.1.1.num * w.1.2.den * w.2.den,
    w.1.2.num * w.1.1.den * w.2.den),
    w.2.num * w.1.1.den * w.1.2.den)

lemma ternaryRatCommonDenom_pos (w : TernaryRatPoint) :
    0 < ternaryRatCommonDenom w := by
  exact mul_pos (mul_pos w.1.1.den_pos w.1.2.den_pos) w.2.den_pos

/-- Clearing denominators really is multiplication by the common positive
integer in rational ternary space. -/
theorem ternaryIntIndexToRat_clearDenominators (w : TernaryRatPoint) :
    ternaryIntIndexToRat (clearTernaryRatDenominators w) =
      (ternaryRatCommonDenom w : ℚ) • w := by
  apply Prod.ext
  · apply Prod.ext
    · have hden1 : (w.1.1.den : ℚ) ≠ 0 := by exact_mod_cast w.1.1.den_nz
      change ((w.1.1.num * w.1.2.den * w.2.den : ℤ) : ℚ) =
        ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.1.1
      calc
        ((w.1.1.num * w.1.2.den * w.2.den : ℤ) : ℚ) =
            (w.1.1.num : ℚ) * w.1.2.den * w.2.den := by push_cast; ring
        _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) *
            ((w.1.1.num : ℚ) / w.1.1.den) := by
              push_cast
              field_simp [hden1]
        _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.1.1 := by
              rw [w.1.1.num_div_den]
    · have hden2 : (w.1.2.den : ℚ) ≠ 0 := by exact_mod_cast w.1.2.den_nz
      change ((w.1.2.num * w.1.1.den * w.2.den : ℤ) : ℚ) =
        ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.1.2
      calc
        ((w.1.2.num * w.1.1.den * w.2.den : ℤ) : ℚ) =
            (w.1.2.num : ℚ) * w.1.1.den * w.2.den := by push_cast; ring
        _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) *
            ((w.1.2.num : ℚ) / w.1.2.den) := by
              push_cast
              field_simp [hden2]
        _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.1.2 := by
              rw [w.1.2.num_div_den]
  · have hden3 : (w.2.den : ℚ) ≠ 0 := by exact_mod_cast w.2.den_nz
    change ((w.2.num * w.1.1.den * w.1.2.den : ℤ) : ℚ) =
      ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.2
    calc
      ((w.2.num * w.1.1.den * w.1.2.den : ℤ) : ℚ) =
          (w.2.num : ℚ) * w.1.1.den * w.1.2.den := by push_cast; ring
      _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) *
          ((w.2.num : ℚ) / w.2.den) := by
            push_cast
            field_simp [hden3]
      _ = ((w.1.1.den * w.1.2.den * w.2.den : ℕ) : ℚ) * w.2 := by
            rw [w.2.num_div_den]

lemma clearTernaryRatDenominators_ne_zero
    {w : TernaryRatPoint} (hw : w ≠ 0) :
    clearTernaryRatDenominators w ≠ 0 := by
  intro hzero
  have hcast := ternaryIntIndexToRat_clearDenominators w
  rw [hzero] at hcast
  have hden : (ternaryRatCommonDenom w : ℚ) ≠ 0 := by
    exact_mod_cast (ternaryRatCommonDenom_pos w).ne'
  apply hw
  apply Prod.ext
  · apply Prod.ext
    · have h := congrArg (fun z : TernaryRatPoint => z.1.1) hcast
      change 0 = (ternaryRatCommonDenom w : ℚ) * w.1.1 at h
      exact (mul_eq_zero.mp h.symm).resolve_left hden
    · have h := congrArg (fun z : TernaryRatPoint => z.1.2) hcast
      change 0 = (ternaryRatCommonDenom w : ℚ) * w.1.2 at h
      exact (mul_eq_zero.mp h.symm).resolve_left hden
  · have h := congrArg (fun z : TernaryRatPoint => z.2) hcast
    change 0 = (ternaryRatCommonDenom w : ℚ) * w.2 at h
    exact (mul_eq_zero.mp h.symm).resolve_left hden

/-- Every rational Householder reflection has a nonzero integral normal. -/
theorem exists_integral_normal_for_ternaryRatHouseholder
    (w : TernaryRatPoint) (hw : w ≠ 0) :
    ∃ W : TernaryIntIndex, W ≠ 0 ∧
      ∀ x, ternaryRatHouseholder w x =
        ternaryRatHouseholder (ternaryIntIndexToRat W) x := by
  refine ⟨clearTernaryRatDenominators w,
    clearTernaryRatDenominators_ne_zero hw, ?_⟩
  intro x
  rw [ternaryIntIndexToRat_clearDenominators]
  exact (ternaryRatHouseholder_smul_normal
    (ternaryRatCommonDenom w : ℚ)
    (by exact_mod_cast (ternaryRatCommonDenom_pos w).ne') w hw x).symm

/-- The rational classification can therefore be strengthened to an
integral-normal classification, before primitive normalization. -/
theorem CoherentThetaInvolution.exists_integral_householder_or_neg_householder
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R) :
    (∃ W : TernaryIntIndex, W ≠ 0 ∧
      ∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat W) x) ∨
    (∃ W : TernaryIntIndex, W ≠ 0 ∧
      ∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat W) x) := by
  rcases T.exists_householder_or_neg_householder with hpositive | hnegative
  · obtain ⟨w, hw, hwanti, hT⟩ := hpositive
    obtain ⟨W, hW, hscale⟩ :=
      exists_integral_normal_for_ternaryRatHouseholder w hw
    exact Or.inl ⟨W, hW, fun x => (hT x).trans (hscale x)⟩
  · obtain ⟨w, hw, hwfixed, hT⟩ := hnegative
    obtain ⟨W, hW, hscale⟩ :=
      exists_integral_normal_for_ternaryRatHouseholder w hw
    exact Or.inr ⟨W, hW, fun x =>
      (hT x).trans (congrArg Neg.neg (hscale x))⟩

/-- A linear three-coordinate Bézout identity yields the square-Bézout
certificate used by the reflection-denominator converse.  The proof is the
explicit degree-four pigeonhole identity: every monomial of
`(a*w1+b*w2+c*w3)^4` contains one of the three coordinate squares. -/
theorem linear_bezout_implies_square_bezout
    (w1 w2 w3 a b c : ℤ)
    (hlinear : a * w1 + b * w2 + c * w3 = 1) :
    ∃ b1 b2 b3 : ℤ,
      b1 * w1 ^ 2 + b2 * w2 ^ 2 + b3 * w3 ^ 2 = 1 := by
  refine ⟨
    a ^ 2 * (a ^ 2 * w1 ^ 2 + 4 * a * b * w1 * w2 +
      4 * a * c * w1 * w3 + 6 * b ^ 2 * w2 ^ 2 +
      12 * b * c * w2 * w3 + 6 * c ^ 2 * w3 ^ 2),
    b ^ 2 * (4 * a * b * w1 * w2 + 12 * a * c * w1 * w3 +
      b ^ 2 * w2 ^ 2 + 4 * b * c * w2 * w3 + 6 * c ^ 2 * w3 ^ 2),
    c ^ 2 * (12 * a * b * w1 * w2 + 4 * a * c * w1 * w3 +
      4 * b * c * w2 * w3 + c ^ 2 * w3 ^ 2), ?_⟩
  calc
    _ = (a * w1 + b * w2 + c * w3) ^ 4 := by ring
    _ = 1 := by rw [hlinear]; norm_num

/-- Every nonzero integral ternary normal is a positive integer multiple of
a primitive normal carrying an explicit linear Bézout certificate. -/
theorem exists_primitive_ternary_rescaling
    (W : TernaryIntIndex) (hW : W ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ ∃ w : TernaryIntIndex,
      W = ternaryIntScale g w ∧
      ∃ a b c : ℤ,
        a * w.1.1 + b * w.1.2 + c * w.2 = 1 := by
  let g23 : ℕ := Int.gcd W.1.2 W.2
  let g : ℕ := Int.gcd W.1.1 (g23 : ℤ)
  have hg_ne : g ≠ 0 := by
    intro hg
    have hgz : (g : ℤ) = 0 := by simp [hg]
    have hdiv1 : (g : ℤ) ∣ W.1.1 := Int.gcd_dvd_left W.1.1 (g23 : ℤ)
    have hdiv23 : (g : ℤ) ∣ (g23 : ℤ) :=
      Int.gcd_dvd_right W.1.1 (g23 : ℤ)
    rw [hgz] at hdiv1 hdiv23
    have hw1 : W.1.1 = 0 := (zero_dvd_iff.mp hdiv1)
    have hg23z : (g23 : ℤ) = 0 := (zero_dvd_iff.mp hdiv23)
    have hdiv2 : (g23 : ℤ) ∣ W.1.2 := Int.gcd_dvd_left W.1.2 W.2
    have hdiv3 : (g23 : ℤ) ∣ W.2 := Int.gcd_dvd_right W.1.2 W.2
    rw [hg23z] at hdiv2 hdiv3
    have hw2 : W.1.2 = 0 := zero_dvd_iff.mp hdiv2
    have hw3 : W.2 = 0 := zero_dvd_iff.mp hdiv3
    apply hW
    apply Prod.ext
    · apply Prod.ext <;> assumption
    · assumption
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg_ne
  have hgdiv1 : (g : ℤ) ∣ W.1.1 := Int.gcd_dvd_left W.1.1 (g23 : ℤ)
  have hgdiv23 : (g : ℤ) ∣ (g23 : ℤ) :=
    Int.gcd_dvd_right W.1.1 (g23 : ℤ)
  have h23div2 : (g23 : ℤ) ∣ W.1.2 := Int.gcd_dvd_left W.1.2 W.2
  have h23div3 : (g23 : ℤ) ∣ W.2 := Int.gcd_dvd_right W.1.2 W.2
  have hgdiv2 : (g : ℤ) ∣ W.1.2 := dvd_trans hgdiv23 h23div2
  have hgdiv3 : (g : ℤ) ∣ W.2 := dvd_trans hgdiv23 h23div3
  let w : TernaryIntIndex :=
    ((W.1.1 / (g : ℤ), W.1.2 / (g : ℤ)), W.2 / (g : ℤ))
  have hw1 : W.1.1 = (g : ℤ) * w.1.1 := by
    dsimp [w]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgdiv1).symm
  have hw2 : W.1.2 = (g : ℤ) * w.1.2 := by
    dsimp [w]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgdiv2).symm
  have hw3 : W.2 = (g : ℤ) * w.2 := by
    dsimp [w]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgdiv3).symm
  have hscale : W = ternaryIntScale g w := by
    apply Prod.ext
    · apply Prod.ext
      · simpa [ternaryIntScale] using hw1
      · simpa [ternaryIntScale] using hw2
    · simpa [ternaryIntScale] using hw3
  let A : ℤ := Int.gcdA W.1.1 (g23 : ℤ)
  let B : ℤ := Int.gcdB W.1.1 (g23 : ℤ)
  let C : ℤ := Int.gcdA W.1.2 W.2
  let D : ℤ := Int.gcdB W.1.2 W.2
  have hgbezout : (g : ℤ) = W.1.1 * A + (g23 : ℤ) * B := by
    exact Int.gcd_eq_gcd_ab W.1.1 (g23 : ℤ)
  have h23bezout : (g23 : ℤ) = W.1.2 * C + W.2 * D := by
    exact Int.gcd_eq_gcd_ab W.1.2 W.2
  have hcombined : (g : ℤ) =
      W.1.1 * A + W.1.2 * (B * C) + W.2 * (B * D) := by
    linear_combination hgbezout + B * h23bezout
  have hfactor : (g : ℤ) = (g : ℤ) *
      (A * w.1.1 + (B * C) * w.1.2 + (B * D) * w.2) := by
    calc
      (g : ℤ) = W.1.1 * A + W.1.2 * (B * C) + W.2 * (B * D) := hcombined
      _ = (g : ℤ) *
          (A * w.1.1 + (B * C) * w.1.2 + (B * D) * w.2) := by
            rw [hw1, hw2, hw3]
            ring
  have hgz_ne : (g : ℤ) ≠ 0 := by exact_mod_cast hg_ne
  have hlinear : A * w.1.1 + (B * C) * w.1.2 + (B * D) * w.2 = 1 := by
    apply mul_left_cancel₀ hgz_ne
    simpa using hfactor.symm
  exact ⟨g, hgpos, w, hscale, A, B * C, B * D, hlinear⟩

/-- Primitive rescaling also supplies exactly the square-Bézout certificate
expected by `primitive_reflection_norm_dvd_two_mul`. -/
theorem exists_primitive_ternary_rescaling_with_square_bezout
    (W : TernaryIntIndex) (hW : W ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ ∃ w : TernaryIntIndex,
      W = ternaryIntScale g w ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 := by
  obtain ⟨g, hg, w, hscale, a, b, c, hlinear⟩ :=
    exists_primitive_ternary_rescaling W hW
  obtain ⟨b1, b2, b3, hsquare⟩ :=
    linear_bezout_implies_square_bezout w.1.1 w.1.2 w.2 a b c hlinear
  exact ⟨g, hg, w, hscale, b1, b2, b3, hsquare⟩

lemma ternaryIntIndexToRat_scale (c : ℤ) (w : TernaryIntIndex) :
    ternaryIntIndexToRat (ternaryIntScale c w) =
      (c : ℚ) • ternaryIntIndexToRat w := by
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  simp [ternaryIntIndexToRat, ternaryIntScale]

/-- **Primitive integral Householder classification.**  Every coherent
involution is a Householder reflection or its negative with a nonzero
primitive integral normal, where primitivity is supplied in exactly the
square-Bézout form consumed by the existing denominator converse. -/
theorem CoherentThetaInvolution.exists_primitive_integral_householder_or_neg
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R) :
    (∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        ∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
    (∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        ∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := by
  rcases T.exists_integral_householder_or_neg_householder with
    hpositive | hnegative
  · obtain ⟨W, hW, hT⟩ := hpositive
    obtain ⟨g, hg, w, hscale, b1, b2, b3, hsquare⟩ :=
      exists_primitive_ternary_rescaling_with_square_bezout W hW
    have hw : w ≠ 0 := by
      intro hwzero
      apply hW
      rw [hscale, hwzero]
      simp [ternaryIntScale]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hnormal : ∀ x,
        ternaryRatHouseholder (ternaryIntIndexToRat W) x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x := by
      intro x
      rw [hscale, ternaryIntIndexToRat_scale]
      exact ternaryRatHouseholder_smul_normal (g : ℚ) hgq
        (ternaryIntIndexToRat w)
        (by
          intro hzero
          apply hw
          apply ternaryIntIndexToRat_injective
          simpa using hzero) x
    exact Or.inl ⟨w, hw, b1, b2, b3, hsquare,
      fun x => (hT x).trans (hnormal x)⟩
  · obtain ⟨W, hW, hT⟩ := hnegative
    obtain ⟨g, hg, w, hscale, b1, b2, b3, hsquare⟩ :=
      exists_primitive_ternary_rescaling_with_square_bezout W hW
    have hw : w ≠ 0 := by
      intro hwzero
      apply hW
      rw [hscale, hwzero]
      simp [ternaryIntScale]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hnormal : ∀ x,
        ternaryRatHouseholder (ternaryIntIndexToRat W) x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x := by
      intro x
      rw [hscale, ternaryIntIndexToRat_scale]
      exact ternaryRatHouseholder_smul_normal (g : ℚ) hgq
        (ternaryIntIndexToRat w)
        (by
          intro hzero
          apply hw
          apply ternaryIntIndexToRat_injective
          simpa using hzero) x
    exact Or.inr ⟨w, hw, b1, b2, b3, hsquare,
      fun x => (hT x).trans (congrArg Neg.neg (hnormal x))⟩

lemma ternaryIntPointToRat_sub_affineBase
    (p i j k : ℕ) (x y : TripleQuintBranchIndex) :
    ternaryIntPointToRat (pointThetaVector p i j k y) -
        ternaryIntPointToRat (pointThetaVector p i j k x) =
      (2 * (p : ℚ)) •
        ternaryIntIndexToRat (pointAffineIndex y - pointAffineIndex x) := by
  rw [pointThetaVector_eq_affineBase_add,
    pointThetaVector_eq_affineBase_add]
  rcases pointAffineIndex x with ⟨⟨x1, x2⟩, x3⟩
  rcases pointAffineIndex y with ⟨⟨y1, y2⟩, y3⟩
  simp [ternaryIntPointToRat, thetaAffineBase, ternaryIntScale,
    ternaryIntIndexToRat]
  constructor
  · constructor <;> ring
  · ring

/-- The exact arithmetic consequence of coherent cancellation: under the
standard Bézout inverse and canonical hypotheses, the rational involution
sends every vector of the homogeneous index-`p` congruence lattice to another
integral vector of that lattice. -/
theorem CoherentThetaInvolution.maps_thetaIndexLattice
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (hR : R < p)
    (bp bv : ℤ) (hunit : bp * p + bv * (3 * i) = 1)
    (d : TernaryIntIndex) (hd : InThetaIndexLattice p i j k d) :
    ∃ d' : TernaryIntIndex,
      InThetaIndexLattice p i j k d' ∧
      T.linear (ternaryIntIndexToRat d) = ternaryIntIndexToRat d' := by
  obtain ⟨x, y, hxfiber, hyfiber, hdiff⟩ :=
    thetaIndexLattice_difference_spanning_of_bezout
      p i j k R d bp bv hunit hd
  have hxprog := (onThetaProgression_iff_inThetaResidueFiber
    p i j k R x hi hpi hj hpj hk hpk hpodd hR).mpr hxfiber
  have hyprog := (onThetaProgression_iff_inThetaResidueFiber
    p i j k R y hi hpi hj hpj hk hpk hpodd hR).mpr hyfiber
  have hxpartner := T.partner_onThetaProgression (by omega) x hxprog
  have hypartner := T.partner_onThetaProgression (by omega) y hyprog
  let d' := pointAffineIndex (T.partner y) - pointAffineIndex (T.partner x)
  have hd' : InThetaIndexLattice p i j k d' := by
    obtain ⟨qx, hqx⟩ := (inThetaResidueFiber_iff_affineIndex
      p i j k R (T.partner x)).mp
        ((onThetaProgression_iff_inThetaResidueFiber
          p i j k R (T.partner x) hi hpi hj hpj hk hpk hpodd hR).mp hxpartner)
    obtain ⟨qy, hqy⟩ := (inThetaResidueFiber_iff_affineIndex
      p i j k R (T.partner y)).mp
        ((onThetaProgression_iff_inThetaResidueFiber
          p i j k R (T.partner y) hi hpi hj hpj hk hpk hpodd hR).mp hypartner)
    refine ⟨qy - qx, ?_⟩
    dsimp [d', InThetaIndexLattice]
    rw [affineIndexDot_sub, hqy, hqx]
    ring
  refine ⟨d', hd', ?_⟩
  have hsource := ternaryIntPointToRat_sub_affineBase p i j k x y
  have htarget := ternaryIntPointToRat_sub_affineBase
    p i j k (T.partner x) (T.partner y)
  have htransport :
      T.linear
          (ternaryIntPointToRat (pointThetaVector p i j k y) -
            ternaryIntPointToRat (pointThetaVector p i j k x)) =
          ternaryIntPointToRat (pointThetaVector p i j k (T.partner y)) -
          ternaryIntPointToRat (pointThetaVector p i j k (T.partner x)) := by
    rw [map_sub]
    change T.linear (pointThetaVectorRat p i j k y) -
        T.linear (pointThetaVectorRat p i j k x) = _
    rw [T.coordinate_transport y hyprog, T.coordinate_transport x hxprog]
    rfl
  rw [hsource, htarget] at htransport
  have hp0 : 0 < p := by omega
  have hpq : (2 * (p : ℚ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast hp0.ne')
  rw [hdiff] at htransport
  simp only [add_sub_cancel_left, map_smul] at htransport
  dsimp [d']
  apply Prod.ext
  · apply Prod.ext
    · have h := congrArg (fun z : TernaryRatPoint => z.1.1) htransport
      change (2 * (p : ℚ)) *
          (T.linear (ternaryIntIndexToRat d)).1.1 =
        (2 * (p : ℚ)) *
          (ternaryIntIndexToRat
            (pointAffineIndex (T.partner y) - pointAffineIndex (T.partner x))).1.1 at h
      exact mul_left_cancel₀ hpq h
    · have h := congrArg (fun z : TernaryRatPoint => z.1.2) htransport
      change (2 * (p : ℚ)) *
          (T.linear (ternaryIntIndexToRat d)).1.2 =
        (2 * (p : ℚ)) *
          (ternaryIntIndexToRat
            (pointAffineIndex (T.partner y) - pointAffineIndex (T.partner x))).1.2 at h
      exact mul_left_cancel₀ hpq h
  · have h := congrArg (fun z : TernaryRatPoint => z.2) htransport
    change (2 * (p : ℚ)) *
        (T.linear (ternaryIntIndexToRat d)).2 =
      (2 * (p : ℚ)) *
        (ternaryIntIndexToRat
          (pointAffineIndex (T.partner y) - pointAffineIndex (T.partner x))).2 at h
    exact mul_left_cancel₀ hpq h

/-- Admissibility supplies the Bézout inverse used by the difference-spanning
construction: the prime `p` is coprime to `3i`. -/
theorem admissibleSparseTriple_exists_three_i_bezout
    {p i j k : ℕ} (hadmissible : AdmissibleSparseTriple p i j k) :
    ∃ bp bv : ℤ, bp * p + bv * (3 * i) = 1 := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hip : i < p := by omega
  have hnotdiv : ¬p ∣ 3 * i := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with hpdiv3 | hpdivi
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpdiv3 with hpone | hpthree
      · exact hp.ne_one hpone
      · exact hp3 hpthree
    · exact (not_le_of_gt hip) (Nat.le_of_dvd hi hpdivi)
  have hcoprime : Nat.Coprime p (3 * i) :=
    hp.coprime_iff_not_dvd.mpr hnotdiv
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (hcoprime.isCoprime : IsCoprime (p : ℤ) ((3 * i : ℕ) : ℤ))

/-- On admissible data the Bézout side condition disappears: every coherent
theta involution is an integral automorphism of the full homogeneous
index-`p` congruence lattice. -/
theorem CoherentThetaInvolution.maps_admissible_thetaIndexLattice
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (d : TernaryIntIndex) (hd : InThetaIndexLattice p i j k d) :
    ∃ d' : TernaryIntIndex,
      InThetaIndexLattice p i j k d' ∧
      T.linear (ternaryIntIndexToRat d) = ternaryIntIndexToRat d' := by
  obtain ⟨bp, bv, hunit⟩ :=
    admissibleSparseTriple_exists_three_i_bezout hadmissible
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  exact T.maps_thetaIndexLattice hi hpi hj hpj hk hpk hpodd hR
    bp bv hunit d hd

/-- The three standard integral basis vectors. -/
def thetaIndexBasis1 : TernaryIntIndex := ((1, 0), 0)
def thetaIndexBasis2 : TernaryIntIndex := ((0, 1), 0)
def thetaIndexBasis3 : TernaryIntIndex := ((0, 0), 1)

lemma p_basis1_mem_thetaIndexLattice (p i j k : ℕ) :
    InThetaIndexLattice p i j k (ternaryIntScale p thetaIndexBasis1) := by
  refine ⟨i, ?_⟩
  simp [affineIndexDot, ternaryIntScale,
    thetaIndexBasis1]
  ring

lemma p_basis2_mem_thetaIndexLattice (p i j k : ℕ) :
    InThetaIndexLattice p i j k (ternaryIntScale p thetaIndexBasis2) := by
  refine ⟨j, ?_⟩
  simp [affineIndexDot, ternaryIntScale,
    thetaIndexBasis2]
  ring

lemma p_basis3_mem_thetaIndexLattice (p i j k : ℕ) :
    InThetaIndexLattice p i j k (ternaryIntScale p thetaIndexBasis3) := by
  refine ⟨k, ?_⟩
  simp [affineIndexDot, ternaryIntScale,
    thetaIndexBasis3]
  ring

/-- In particular, coherence supplies the three integral `p*e_s` images
whose diagonal coordinates force a primitive Householder denominator to
divide `2p` in `MultiQuintupleRootConverse`. -/
theorem CoherentThetaInvolution.exists_integral_images_of_p_basis
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p) :
    (∃ y1 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis1)) =
        ternaryIntIndexToRat y1) ∧
    (∃ y2 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis2)) =
        ternaryIntIndexToRat y2) ∧
    (∃ y3 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis3)) =
        ternaryIntIndexToRat y3) := by
  obtain ⟨y1, hy1, hmap1⟩ := T.maps_admissible_thetaIndexLattice hadmissible hR
    (ternaryIntScale p thetaIndexBasis1) (p_basis1_mem_thetaIndexLattice p i j k)
  obtain ⟨y2, hy2, hmap2⟩ := T.maps_admissible_thetaIndexLattice hadmissible hR
    (ternaryIntScale p thetaIndexBasis2) (p_basis2_mem_thetaIndexLattice p i j k)
  obtain ⟨y3, hy3, hmap3⟩ := T.maps_admissible_thetaIndexLattice hadmissible hR
    (ternaryIntScale p thetaIndexBasis3) (p_basis3_mem_thetaIndexLattice p i j k)
  exact ⟨⟨y1, hmap1⟩, ⟨y2, hmap2⟩, ⟨y3, hmap3⟩⟩

lemma ternaryRatNorm_intIndexToRat (w : TernaryIntIndex) :
    ternaryRatNorm (ternaryIntIndexToRat w) =
      (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) := by
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  simp [ternaryRatNorm, ternaryIntIndexToRat, ternaryNorm]

/-- Integrality of the first `p*e_s` Householder image gives the first
denominator divisibility test. -/
theorem householder_integral_p_basis1_norm_dvd
    (p : ℕ) (w y : TernaryIntIndex) (hw : w ≠ 0)
    (hmap :
      ternaryRatHouseholder (ternaryIntIndexToRat w)
          (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis1)) =
        ternaryIntIndexToRat y) :
    ternaryNorm w.1.1 w.1.2 w.2 ∣ 2 * (p : ℤ) * w.1.1 ^ 2 := by
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormq : (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) ≠ 0 := by
    rw [← ternaryRatNorm_intIndexToRat]
    exact ne_of_gt (ternaryRatNorm_pos hcast_ne)
  have hcoord := congrArg (fun z : TernaryRatPoint => z.1.1) hmap
  simp [ternaryRatHouseholder, ternaryIntIndexToRat,
    ternaryIntScale, thetaIndexBasis1, ternaryRatDot,
    ternaryRatNorm] at hcoord
  have hnormexpand :
      ((w.1.1 : ℚ) ^ 2 + (w.1.2 : ℚ) ^ 2 + (w.2 : ℚ) ^ 2) =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) := by
    simp [ternaryNorm]
  rw [hnormexpand] at hcoord
  field_simp [hnormq] at hcoord
  refine ⟨(p : ℤ) - y.1.1, ?_⟩
  exact_mod_cast (show
    (2 * (p : ℚ) * (w.1.1 : ℚ) ^ 2) =
      (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * ((p : ℚ) - y.1.1) by
        linear_combination -hcoord)

theorem householder_integral_p_basis2_norm_dvd
    (p : ℕ) (w y : TernaryIntIndex) (hw : w ≠ 0)
    (hmap :
      ternaryRatHouseholder (ternaryIntIndexToRat w)
          (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis2)) =
        ternaryIntIndexToRat y) :
    ternaryNorm w.1.1 w.1.2 w.2 ∣ 2 * (p : ℤ) * w.1.2 ^ 2 := by
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormq : (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) ≠ 0 := by
    rw [← ternaryRatNorm_intIndexToRat]
    exact ne_of_gt (ternaryRatNorm_pos hcast_ne)
  have hcoord := congrArg (fun z : TernaryRatPoint => z.1.2) hmap
  simp [ternaryRatHouseholder, ternaryIntIndexToRat,
    ternaryIntScale, thetaIndexBasis2, ternaryRatDot,
    ternaryRatNorm] at hcoord
  have hnormexpand :
      ((w.1.1 : ℚ) ^ 2 + (w.1.2 : ℚ) ^ 2 + (w.2 : ℚ) ^ 2) =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) := by
    simp [ternaryNorm]
  rw [hnormexpand] at hcoord
  field_simp [hnormq] at hcoord
  refine ⟨(p : ℤ) - y.1.2, ?_⟩
  exact_mod_cast (show
    (2 * (p : ℚ) * (w.1.2 : ℚ) ^ 2) =
      (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * ((p : ℚ) - y.1.2) by
        linear_combination -hcoord)

theorem householder_integral_p_basis3_norm_dvd
    (p : ℕ) (w y : TernaryIntIndex) (hw : w ≠ 0)
    (hmap :
      ternaryRatHouseholder (ternaryIntIndexToRat w)
          (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis3)) =
        ternaryIntIndexToRat y) :
    ternaryNorm w.1.1 w.1.2 w.2 ∣ 2 * (p : ℤ) * w.2 ^ 2 := by
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormq : (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) ≠ 0 := by
    rw [← ternaryRatNorm_intIndexToRat]
    exact ne_of_gt (ternaryRatNorm_pos hcast_ne)
  have hcoord := congrArg (fun z : TernaryRatPoint => z.2) hmap
  simp [ternaryRatHouseholder, ternaryIntIndexToRat,
    ternaryIntScale, thetaIndexBasis3, ternaryRatDot,
    ternaryRatNorm] at hcoord
  have hnormexpand :
      ((w.1.1 : ℚ) ^ 2 + (w.1.2 : ℚ) ^ 2 + (w.2 : ℚ) ^ 2) =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) := by
    simp [ternaryNorm]
  rw [hnormexpand] at hcoord
  field_simp [hnormq] at hcoord
  refine ⟨(p : ℤ) - y.2, ?_⟩
  exact_mod_cast (show
    (2 * (p : ℚ) * (w.2 : ℚ) ^ 2) =
      (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * ((p : ℚ) - y.2) by
        linear_combination -hcoord)

/-- An odd prime larger than two positive factors cannot divide twice their
product when both factors are strictly smaller than the prime. -/
lemma prime_not_dvd_two_mul_of_lt
    {p a b : ℕ} (hp : Nat.Prime p)
    (ha : 0 < a) (hb : 0 < b) (hpa : a < p) (hpb : b < p)
    (hp2 : 2 < p) :
    ¬(p : ℤ) ∣ 2 * (a : ℤ) * (b : ℤ) := by
  intro hdiv
  have hdivNat : p ∣ (2 * a) * b := by
    exact_mod_cast hdiv
  rcases hp.dvd_mul.mp hdivNat with hdiv2a | hdivb
  · rcases hp.dvd_mul.mp hdiv2a with hdiv2 | hdiva
    · exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp2) hdiv2
    · exact (Nat.not_dvd_of_pos_of_lt ha hpa) hdiva
  · exact (Nat.not_dvd_of_pos_of_lt hb hpb) hdivb

/-- For `0 < a < b` and `2b < p`, the prime cannot divide the difference
of the two squares.  This is the modular fact that excludes signed swaps of
two distinct canonical coordinates. -/
lemma prime_not_dvd_square_sub_square_of_canonical
    {p a b : ℕ} (hp : Nat.Prime p)
    (ha : 0 < a) (hab : a < b) (hpb : 2 * b < p) :
    ¬(p : ℤ) ∣ (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
  intro hdiv
  have hfactor :
      (b : ℤ) ^ 2 - (a : ℤ) ^ 2 =
        (((b - a) * (b + a) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hab)]
    push_cast
    ring
  have hdivNat : p ∣ (b - a) * (b + a) := by
    apply Int.natCast_dvd_natCast.mp
    simpa [hfactor] using hdiv
  rcases hp.dvd_mul.mp hdivNat with hminus | hplus
  · apply (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hab) (by omega)) hminus
  · apply (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hplus

/-- A rational equality with an integral multiplier certifies integer
divisibility; allowing both signs avoids irrelevant orientation choices in
the kernel-vector computations below. -/
lemma int_dvd_of_rat_eq_mul_or_neg (p x q : ℤ)
    (h : (x : ℚ) = (p : ℚ) * (q : ℚ) ∨
      (x : ℚ) = -((p : ℚ) * (q : ℚ))) :
    p ∣ x := by
  rcases h with h | h
  · exact ⟨q, by exact_mod_cast h⟩
  · refine ⟨-q, ?_⟩
    exact_mod_cast (show (x : ℚ) = (p : ℚ) * (-q : ℚ) by
      nlinarith [h])

/-- Finite mod-three data for the converse sign-selection calculation. -/
structure Mod3BranchConverseInput where
  epc : ZMod 3 × ZMod 3 × ZMod 3
  root : ZMod 3 × ZMod 3 × ZMod 3
  output : ZMod 3 × ZMod 3 × ZMod 3
  bits : Bool × Bool × Bool
  deriving DecidableEq, Fintype

namespace Mod3BranchConverseInput
def e (x : Mod3BranchConverseInput) := x.epc.1
def p (x : Mod3BranchConverseInput) := x.epc.2.1
def c (x : Mod3BranchConverseInput) := x.epc.2.2
def w1 (x : Mod3BranchConverseInput) := x.root.1
def w2 (x : Mod3BranchConverseInput) := x.root.2.1
def w3 (x : Mod3BranchConverseInput) := x.root.2.2
def u1 (x : Mod3BranchConverseInput) := x.output.1
def u2 (x : Mod3BranchConverseInput) := x.output.2.1
def u3 (x : Mod3BranchConverseInput) := x.output.2.2
def b1 (x : Mod3BranchConverseInput) := x.bits.1
def b2 (x : Mod3BranchConverseInput) := x.bits.2.1
def b3 (x : Mod3BranchConverseInput) := x.bits.2.2
def t (x : Mod3BranchConverseInput) := x.p *
  (branchSign3 x.b1 * x.w1 + branchSign3 x.b2 * x.w2 +
    branchSign3 x.b3 * x.w3)
end Mod3BranchConverseInput

open Mod3BranchConverseInput

/- The finite core omits the three output coordinates, which are uniquely
determined by the reflection equations.  This keeps ordinary kernel reduction
small enough to avoid the soundness axiom used by native evaluation. -/
structure Mod3BranchCoreInput where
  epc : ZMod 3 × ZMod 3 × ZMod 3
  root : ZMod 3 × ZMod 3 × ZMod 3
  bits : Bool × Bool × Bool
  deriving DecidableEq, Fintype

namespace Mod3BranchCoreInput
def e (x : Mod3BranchCoreInput) := x.epc.1
def p (x : Mod3BranchCoreInput) := x.epc.2.1
def c (x : Mod3BranchCoreInput) := x.epc.2.2
def w1 (x : Mod3BranchCoreInput) := x.root.1
def w2 (x : Mod3BranchCoreInput) := x.root.2.1
def w3 (x : Mod3BranchCoreInput) := x.root.2.2
def b1 (x : Mod3BranchCoreInput) := x.bits.1
def b2 (x : Mod3BranchCoreInput) := x.bits.2.1
def b3 (x : Mod3BranchCoreInput) := x.bits.2.2
def t (x : Mod3BranchCoreInput) := x.p *
  (branchSign3 x.b1 * x.w1 + branchSign3 x.b2 * x.w2 +
    branchSign3 x.b3 * x.w3)
def pu1 (x : Mod3BranchCoreInput) :=
  branchSign3 x.b1 - x.c * x.t * x.w1
def pu2 (x : Mod3BranchCoreInput) :=
  branchSign3 x.b2 - x.c * x.t * x.w2
def pu3 (x : Mod3BranchCoreInput) :=
  branchSign3 x.b3 - x.c * x.t * x.w3
def nu1 (x : Mod3BranchCoreInput) := -x.pu1
def nu2 (x : Mod3BranchCoreInput) := -x.pu2
def nu3 (x : Mod3BranchCoreInput) := -x.pu3
end Mod3BranchCoreInput

open Mod3BranchCoreInput

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem positive_branch_core_forces_norm_one_mod3 :
    ∀ x : Mod3BranchCoreInput,
      (x.e = 1 ∨ x.e = 2) → x.p ≠ 0 → x.c * x.e = 2 →
      x.w1 ^ 2 + x.w2 ^ 2 + x.w3 ^ 2 = x.e * x.p →
      x.pu1 ≠ 0 → x.pu2 ≠ 0 → x.pu3 ≠ 0 →
      x.pu1 * x.pu2 * x.pu3 =
        -(branchSign3 x.b1 * branchSign3 x.b2 * branchSign3 x.b3) →
      x.e * x.p = 1 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem negative_branch_core_forces_norm_two_mod3 :
    ∀ x : Mod3BranchCoreInput,
      (x.e = 1 ∨ x.e = 2) → x.p ≠ 0 → x.c * x.e = 2 →
      x.w1 ^ 2 + x.w2 ^ 2 + x.w3 ^ 2 = x.e * x.p →
      x.nu1 ≠ 0 → x.nu2 ≠ 0 → x.nu3 ≠ 0 →
      x.nu1 * x.nu2 * x.nu3 =
        -(branchSign3 x.b1 * branchSign3 x.b2 * branchSign3 x.b3) →
      x.e * x.p = 2 := by
  decide

/-- A positive Householder map that closes even one branch and reverses its
three-sign product must have root norm `1 mod 3`. -/
theorem positive_branch_reversal_forces_norm_one_mod3 :
    ∀ x : Mod3BranchConverseInput,
      (x.e = 1 ∨ x.e = 2) → x.p ≠ 0 → x.c * x.e = 2 →
      x.w1 ^ 2 + x.w2 ^ 2 + x.w3 ^ 2 = x.e * x.p →
      x.u1 = branchSign3 x.b1 - x.c * x.t * x.w1 →
      x.u2 = branchSign3 x.b2 - x.c * x.t * x.w2 →
      x.u3 = branchSign3 x.b3 - x.c * x.t * x.w3 →
      x.u1 ≠ 0 → x.u2 ≠ 0 → x.u3 ≠ 0 →
      x.u1 * x.u2 * x.u3 =
        -(branchSign3 x.b1 * branchSign3 x.b2 * branchSign3 x.b3) →
      x.e * x.p = 1 := by
  intro x he hp hc hroot h1 h2 h3 hu1 hu2 hu3 hproduct
  let y : Mod3BranchCoreInput := ⟨x.epc, x.root, x.bits⟩
  have h1' : x.u1 = y.pu1 := by simpa [y, Mod3BranchCoreInput.pu1,
    Mod3BranchCoreInput.t, Mod3BranchCoreInput.e, Mod3BranchCoreInput.p,
    Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1, Mod3BranchCoreInput.w2,
    Mod3BranchCoreInput.w3, Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h1
  have h2' : x.u2 = y.pu2 := by simpa [y, Mod3BranchCoreInput.pu2,
    Mod3BranchCoreInput.t, Mod3BranchCoreInput.e, Mod3BranchCoreInput.p,
    Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1, Mod3BranchCoreInput.w2,
    Mod3BranchCoreInput.w3, Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h2
  have h3' : x.u3 = y.pu3 := by simpa [y, Mod3BranchCoreInput.pu3,
    Mod3BranchCoreInput.t, Mod3BranchCoreInput.e, Mod3BranchCoreInput.p,
    Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1, Mod3BranchCoreInput.w2,
    Mod3BranchCoreInput.w3, Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h3
  rw [h1'] at hu1 hproduct
  rw [h2'] at hu2 hproduct
  rw [h3'] at hu3 hproduct
  exact positive_branch_core_forces_norm_one_mod3 y
    (by simpa [y, Mod3BranchCoreInput.e] using he)
    (by simpa [y, Mod3BranchCoreInput.p] using hp)
    (by simpa [y, Mod3BranchCoreInput.c, Mod3BranchCoreInput.e] using hc)
    (by simpa [y, Mod3BranchCoreInput.w1, Mod3BranchCoreInput.w2,
      Mod3BranchCoreInput.w3, Mod3BranchCoreInput.e,
      Mod3BranchCoreInput.p] using hroot)
    hu1 hu2 hu3
    (by simpa [y, Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
      Mod3BranchCoreInput.b3] using hproduct)

/-- A negative Householder map that closes one sign-reversing branch must
instead have root norm `2 mod 3`. -/
theorem negative_branch_reversal_forces_norm_two_mod3 :
    ∀ x : Mod3BranchConverseInput,
      (x.e = 1 ∨ x.e = 2) → x.p ≠ 0 → x.c * x.e = 2 →
      x.w1 ^ 2 + x.w2 ^ 2 + x.w3 ^ 2 = x.e * x.p →
      x.u1 = -(branchSign3 x.b1 - x.c * x.t * x.w1) →
      x.u2 = -(branchSign3 x.b2 - x.c * x.t * x.w2) →
      x.u3 = -(branchSign3 x.b3 - x.c * x.t * x.w3) →
      x.u1 ≠ 0 → x.u2 ≠ 0 → x.u3 ≠ 0 →
      x.u1 * x.u2 * x.u3 =
        -(branchSign3 x.b1 * branchSign3 x.b2 * branchSign3 x.b3) →
      x.e * x.p = 2 := by
  intro x he hp hc hroot h1 h2 h3 hu1 hu2 hu3 hproduct
  let y : Mod3BranchCoreInput := ⟨x.epc, x.root, x.bits⟩
  have h1' : x.u1 = y.nu1 := by simpa [y, Mod3BranchCoreInput.nu1,
    Mod3BranchCoreInput.pu1, Mod3BranchCoreInput.t,
    Mod3BranchCoreInput.p, Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1,
    Mod3BranchCoreInput.w2, Mod3BranchCoreInput.w3,
    Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h1
  have h2' : x.u2 = y.nu2 := by simpa [y, Mod3BranchCoreInput.nu2,
    Mod3BranchCoreInput.pu2, Mod3BranchCoreInput.t,
    Mod3BranchCoreInput.p, Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1,
    Mod3BranchCoreInput.w2, Mod3BranchCoreInput.w3,
    Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h2
  have h3' : x.u3 = y.nu3 := by simpa [y, Mod3BranchCoreInput.nu3,
    Mod3BranchCoreInput.pu3, Mod3BranchCoreInput.t,
    Mod3BranchCoreInput.p, Mod3BranchCoreInput.c, Mod3BranchCoreInput.w1,
    Mod3BranchCoreInput.w2, Mod3BranchCoreInput.w3,
    Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
    Mod3BranchCoreInput.b3] using h3
  rw [h1'] at hu1 hproduct
  rw [h2'] at hu2 hproduct
  rw [h3'] at hu3 hproduct
  exact negative_branch_core_forces_norm_two_mod3 y
    (by simpa [y, Mod3BranchCoreInput.e] using he)
    (by simpa [y, Mod3BranchCoreInput.p] using hp)
    (by simpa [y, Mod3BranchCoreInput.c, Mod3BranchCoreInput.e] using hc)
    (by simpa [y, Mod3BranchCoreInput.w1, Mod3BranchCoreInput.w2,
      Mod3BranchCoreInput.w3, Mod3BranchCoreInput.e,
      Mod3BranchCoreInput.p] using hroot)
    hu1 hu2 hu3
    (by simpa [y, Mod3BranchCoreInput.b1, Mod3BranchCoreInput.b2,
      Mod3BranchCoreInput.b3] using hproduct)

lemma zmod3_square_eq_one_of_ne_zero (u : ZMod 3) (hu : u ≠ 0) :
    u * u = 1 := by
  have hall : ∀ v : ZMod 3, v ≠ 0 → v * v = 1 := by decide
  exact hall u hu

lemma quintLatticeCoord_cast_zmod3
    (b : Bool) (p i n : ℤ) :
    ((quintLatticeCoord b p i n : ℤ) : ZMod 3) =
      (p : ZMod 3) * branchSign3 b := by
  cases b
  · simp only [quintLatticeCoord, branchSign3]
    push_cast
    ring_nf
    change -(p : ZMod 3) + (p : ZMod 3) * (n : ZMod 3) * (6 : ZMod 3) +
        (i : ZMod 3) * (6 : ZMod 3) = -(p : ZMod 3)
    rw [show (6 : ZMod 3) = 0 by decide]
    ring
  · simp only [quintLatticeCoord, branchSign3, if_true]
    push_cast
    ring_nf
    change (p : ZMod 3) + (p : ZMod 3) * (n : ZMod 3) * (6 : ZMod 3) +
        (i : ZMod 3) * (6 : ZMod 3) = (p : ZMod 3)
    rw [show (6 : ZMod 3) = 0 by decide]
    ring

/-- Positive integral branch closure, divided by the nonzero modulus class,
in the exact form consumed by the finite converse. -/
lemma positive_shortRoot_branch_closure_mod3
    (b b' : Bool) (p c t w i n n' : ℤ)
    (hp3 : (p : ZMod 3) ≠ 0)
    (hclosure : quintLatticeCoord b' p i n' =
      shortRootReflectCoord c t w (quintLatticeCoord b p i n)) :
    branchSign3 b' = branchSign3 b -
      (c : ZMod 3) * ((p : ZMod 3) * (t : ZMod 3)) * (w : ZMod 3) := by
  have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hclosure
  change ((quintLatticeCoord b' p i n' : ℤ) : ZMod 3) =
    ((shortRootReflectCoord c t w (quintLatticeCoord b p i n) : ℤ) : ZMod 3)
      at hcast
  simp only [shortRootReflectCoord] at hcast
  push_cast at hcast
  rw [quintLatticeCoord_cast_zmod3,
    quintLatticeCoord_cast_zmod3] at hcast
  change (p : ZMod 3) * branchSign3 b' =
    (p : ZMod 3) * branchSign3 b - (c : ZMod 3) * t * w at hcast
  have hpSq := zmod3_square_eq_one_of_ne_zero (p : ZMod 3) hp3
  calc
    branchSign3 b' = 1 * branchSign3 b' := by simp
    _ = ((p : ZMod 3) * p) * branchSign3 b' := by rw [hpSq]
    _ = (p : ZMod 3) * ((p : ZMod 3) * branchSign3 b') := by ring
    _ = (p : ZMod 3) *
        ((p : ZMod 3) * branchSign3 b - (c : ZMod 3) * t * w) := by rw [hcast]
    _ = ((p : ZMod 3) * p) * branchSign3 b -
        (c : ZMod 3) * ((p : ZMod 3) * t) * w := by ring
    _ = branchSign3 b -
        (c : ZMod 3) * ((p : ZMod 3) * t) * w := by rw [hpSq]; ring

/-- The corresponding mod-three formula for negative Householder closure. -/
lemma negative_shortRoot_branch_closure_mod3
    (b b' : Bool) (p c t w i n n' : ℤ)
    (hp3 : (p : ZMod 3) ≠ 0)
    (hclosure : quintLatticeCoord b' p i n' =
      -shortRootReflectCoord c t w (quintLatticeCoord b p i n)) :
    branchSign3 b' = -(branchSign3 b -
      (c : ZMod 3) * ((p : ZMod 3) * (t : ZMod 3)) * (w : ZMod 3)) := by
  have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hclosure
  change ((quintLatticeCoord b' p i n' : ℤ) : ZMod 3) =
    ((-shortRootReflectCoord c t w (quintLatticeCoord b p i n) : ℤ) : ZMod 3)
      at hcast
  simp only [shortRootReflectCoord] at hcast
  push_cast at hcast
  rw [quintLatticeCoord_cast_zmod3,
    quintLatticeCoord_cast_zmod3] at hcast
  change (p : ZMod 3) * branchSign3 b' =
    -((p : ZMod 3) * branchSign3 b - (c : ZMod 3) * t * w) at hcast
  have hpSq := zmod3_square_eq_one_of_ne_zero (p : ZMod 3) hp3
  calc
    branchSign3 b' = 1 * branchSign3 b' := by simp
    _ = ((p : ZMod 3) * p) * branchSign3 b' := by rw [hpSq]
    _ = (p : ZMod 3) * ((p : ZMod 3) * branchSign3 b') := by ring
    _ = (p : ZMod 3) *
        (-((p : ZMod 3) * branchSign3 b - (c : ZMod 3) * t * w)) := by rw [hcast]
    _ = -(((p : ZMod 3) * p) * branchSign3 b -
        (c : ZMod 3) * ((p : ZMod 3) * t) * w) := by ring
    _ = -(branchSign3 b -
        (c : ZMod 3) * ((p : ZMod 3) * t) * w) := by rw [hpSq]; ring

lemma branchSign_cast_zmod3 (b : Bool) :
    ((branchSign b : ℤ) : ZMod 3) = branchSign3 b := by
  cases b <;> simp [branchSign, branchSign3]

/-- Integer branch closure for one positive short-root reflection already
selects the norm-`1 mod 3` case.  This is the bridge from the exhaustive
finite calculation to the coherent integral Householder map. -/
theorem positive_integral_branch_reversal_forces_norm_one_mod3
    (b1 b2 b3 b1' b2' b3' : Bool)
    (p e c t w1 w2 w3 i j k n1 n2 n3 n1' n2' n3' : ℤ)
    (he : e = 1 ∨ e = 2) (hp3 : (p : ZMod 3) ≠ 0)
    (hcoefficient : c * e = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hdot : ternaryDot
      (quintLatticeCoord b1 p i n1)
      (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) w1 w2 w3 = p * t)
    (hclosure1 : quintLatticeCoord b1' p i n1' =
      shortRootReflectCoord c t w1 (quintLatticeCoord b1 p i n1))
    (hclosure2 : quintLatticeCoord b2' p j n2' =
      shortRootReflectCoord c t w2 (quintLatticeCoord b2 p j n2))
    (hclosure3 : quintLatticeCoord b3' p k n3' =
      shortRootReflectCoord c t w3 (quintLatticeCoord b3 p k n3))
    (hweight : branchSign b1' * branchSign b2' * branchSign b3' =
      -(branchSign b1 * branchSign b2 * branchSign b3)) :
    (((e * p : ℤ) : ZMod 3)) = 1 := by
  let z : Mod3BranchConverseInput :=
    ⟨((e : ZMod 3), (p : ZMod 3), (c : ZMod 3)),
      ((w1 : ZMod 3), (w2 : ZMod 3), (w3 : ZMod 3)),
      (branchSign3 b1', branchSign3 b2', branchSign3 b3'),
      (b1, b2, b3)⟩
  have hdot3 := congrArg (fun q : ℤ => (q : ZMod 3)) hdot
  simp only [ternaryDot] at hdot3
  push_cast at hdot3
  rw [quintLatticeCoord_cast_zmod3, quintLatticeCoord_cast_zmod3,
    quintLatticeCoord_cast_zmod3] at hdot3
  have ht : (p : ZMod 3) * (t : ZMod 3) = (p : ZMod 3) *
      (branchSign3 b1 * (w1 : ZMod 3) + branchSign3 b2 * w2 +
        branchSign3 b3 * w3) := by
    calc
      (p : ZMod 3) * (t : ZMod 3) =
          (p : ZMod 3) * branchSign3 b1 * w1 +
            (p : ZMod 3) * branchSign3 b2 * w2 +
            (p : ZMod 3) * branchSign3 b3 * w3 := hdot3.symm
      _ = (p : ZMod 3) *
          (branchSign3 b1 * w1 + branchSign3 b2 * w2 +
            branchSign3 b3 * w3) := by ring
  push_cast
  change z.e * z.p = 1
  apply positive_branch_reversal_forces_norm_one_mod3 z
  · rcases he with rfl | rfl <;> simp [z, Mod3BranchConverseInput.e]
  · simpa [z, Mod3BranchConverseInput.p] using hp3
  · dsimp [z, Mod3BranchConverseInput.c, Mod3BranchConverseInput.e]
    have h := congrArg (fun q : ℤ => (q : ZMod 3)) hcoefficient
    push_cast at h
    exact h
  · dsimp [z, Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.w3, Mod3BranchConverseInput.e,
      Mod3BranchConverseInput.p]
    have h := congrArg (fun q : ℤ => (q : ZMod 3))
      (by simpa [ternaryNorm] using hroot)
    push_cast at h
    exact h
  · dsimp [z, Mod3BranchConverseInput.u1, Mod3BranchConverseInput.b1,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w1,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w2, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.b2, Mod3BranchConverseInput.b3]
    rw [positive_shortRoot_branch_closure_mod3 b1 b1' p c t w1 i n1 n1'
      hp3 hclosure1, ← ht]
  · dsimp [z, Mod3BranchConverseInput.u2, Mod3BranchConverseInput.b2,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.b1, Mod3BranchConverseInput.b3]
    rw [positive_shortRoot_branch_closure_mod3 b2 b2' p c t w2 j n2 n2'
      hp3 hclosure2, ← ht]
  · dsimp [z, Mod3BranchConverseInput.u3, Mod3BranchConverseInput.b3,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.b1, Mod3BranchConverseInput.b2]
    rw [positive_shortRoot_branch_closure_mod3 b3 b3' p c t w3 k n3 n3'
      hp3 hclosure3, ← ht]
  · cases b1' <;> simp [z, Mod3BranchConverseInput.u1, branchSign3]
  · cases b2' <;> simp [z, Mod3BranchConverseInput.u2, branchSign3]
  · cases b3' <;> simp [z, Mod3BranchConverseInput.u3, branchSign3]
  · have hweight3 := congrArg (fun q : ℤ => (q : ZMod 3)) hweight
    push_cast at hweight3
    simpa [z, Mod3BranchConverseInput.u1, Mod3BranchConverseInput.u2,
      Mod3BranchConverseInput.u3, Mod3BranchConverseInput.b1,
      Mod3BranchConverseInput.b2, Mod3BranchConverseInput.b3,
      branchSign_cast_zmod3] using hweight3

/-- The same integer bridge for a negative Householder map selects the
norm-`2 mod 3` case. -/
theorem negative_integral_branch_reversal_forces_norm_two_mod3
    (b1 b2 b3 b1' b2' b3' : Bool)
    (p e c t w1 w2 w3 i j k n1 n2 n3 n1' n2' n3' : ℤ)
    (he : e = 1 ∨ e = 2) (hp3 : (p : ZMod 3) ≠ 0)
    (hcoefficient : c * e = 2)
    (hroot : ternaryNorm w1 w2 w3 = e * p)
    (hdot : ternaryDot
      (quintLatticeCoord b1 p i n1)
      (quintLatticeCoord b2 p j n2)
      (quintLatticeCoord b3 p k n3) w1 w2 w3 = p * t)
    (hclosure1 : quintLatticeCoord b1' p i n1' =
      -shortRootReflectCoord c t w1 (quintLatticeCoord b1 p i n1))
    (hclosure2 : quintLatticeCoord b2' p j n2' =
      -shortRootReflectCoord c t w2 (quintLatticeCoord b2 p j n2))
    (hclosure3 : quintLatticeCoord b3' p k n3' =
      -shortRootReflectCoord c t w3 (quintLatticeCoord b3 p k n3))
    (hweight : branchSign b1' * branchSign b2' * branchSign b3' =
      -(branchSign b1 * branchSign b2 * branchSign b3)) :
    (((e * p : ℤ) : ZMod 3)) = 2 := by
  let z : Mod3BranchConverseInput :=
    ⟨((e : ZMod 3), (p : ZMod 3), (c : ZMod 3)),
      ((w1 : ZMod 3), (w2 : ZMod 3), (w3 : ZMod 3)),
      (branchSign3 b1', branchSign3 b2', branchSign3 b3'),
      (b1, b2, b3)⟩
  have hdot3 := congrArg (fun q : ℤ => (q : ZMod 3)) hdot
  simp only [ternaryDot] at hdot3
  push_cast at hdot3
  rw [quintLatticeCoord_cast_zmod3, quintLatticeCoord_cast_zmod3,
    quintLatticeCoord_cast_zmod3] at hdot3
  have ht : (p : ZMod 3) * (t : ZMod 3) = (p : ZMod 3) *
      (branchSign3 b1 * (w1 : ZMod 3) + branchSign3 b2 * w2 +
        branchSign3 b3 * w3) := by
    calc
      (p : ZMod 3) * (t : ZMod 3) =
          (p : ZMod 3) * branchSign3 b1 * w1 +
            (p : ZMod 3) * branchSign3 b2 * w2 +
            (p : ZMod 3) * branchSign3 b3 * w3 := hdot3.symm
      _ = (p : ZMod 3) *
          (branchSign3 b1 * w1 + branchSign3 b2 * w2 +
            branchSign3 b3 * w3) := by ring
  push_cast
  change z.e * z.p = 2
  apply negative_branch_reversal_forces_norm_two_mod3 z
  · rcases he with rfl | rfl <;> simp [z, Mod3BranchConverseInput.e]
  · simpa [z, Mod3BranchConverseInput.p] using hp3
  · dsimp [z, Mod3BranchConverseInput.c, Mod3BranchConverseInput.e]
    have h := congrArg (fun q : ℤ => (q : ZMod 3)) hcoefficient
    push_cast at h
    exact h
  · dsimp [z, Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.w3, Mod3BranchConverseInput.e,
      Mod3BranchConverseInput.p]
    have h := congrArg (fun q : ℤ => (q : ZMod 3))
      (by simpa [ternaryNorm] using hroot)
    push_cast at h
    exact h
  · dsimp [z, Mod3BranchConverseInput.u1, Mod3BranchConverseInput.b1,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w1,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w2, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.b2, Mod3BranchConverseInput.b3]
    rw [negative_shortRoot_branch_closure_mod3 b1 b1' p c t w1 i n1 n1'
      hp3 hclosure1, ← ht]
  · dsimp [z, Mod3BranchConverseInput.u2, Mod3BranchConverseInput.b2,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.b1, Mod3BranchConverseInput.b3]
    rw [negative_shortRoot_branch_closure_mod3 b2 b2' p c t w2 j n2 n2'
      hp3 hclosure2, ← ht]
  · dsimp [z, Mod3BranchConverseInput.u3, Mod3BranchConverseInput.b3,
      Mod3BranchConverseInput.c, Mod3BranchConverseInput.w3,
      Mod3BranchConverseInput.t, Mod3BranchConverseInput.p,
      Mod3BranchConverseInput.w1, Mod3BranchConverseInput.w2,
      Mod3BranchConverseInput.b1, Mod3BranchConverseInput.b2]
    rw [negative_shortRoot_branch_closure_mod3 b3 b3' p c t w3 k n3 n3'
      hp3 hclosure3, ← ht]
  · cases b1' <;> simp [z, Mod3BranchConverseInput.u1, branchSign3]
  · cases b2' <;> simp [z, Mod3BranchConverseInput.u2, branchSign3]
  · cases b3' <;> simp [z, Mod3BranchConverseInput.u3, branchSign3]
  · have hweight3 := congrArg (fun q : ℤ => (q : ZMod 3)) hweight
    push_cast at hweight3
    simpa [z, Mod3BranchConverseInput.u1, Mod3BranchConverseInput.u2,
      Mod3BranchConverseInput.u3, Mod3BranchConverseInput.b1,
      Mod3BranchConverseInput.b2, Mod3BranchConverseInput.b3,
      branchSign_cast_zmod3] using hweight3

/-- Full denominator classification obtained from coherence.  Before the
coordinate/permutation cases are excluded, the primitive normal norm is one
of `1`, `2`, `p`, or `2p`. -/
theorem primitive_householder_norm_cases_of_coherent
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 = 1 ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 ∨
      ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p := by
  obtain ⟨⟨y1, hmap1⟩, ⟨y2, hmap2⟩, ⟨y3, hmap3⟩⟩ :=
    T.exists_integral_images_of_p_basis hadmissible hR
  obtain ⟨z1, z2, z3, hh1, hh2, hh3⟩ :
      ∃ z1 z2 z3 : TernaryIntIndex,
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis1)) =
          ternaryIntIndexToRat z1 ∧
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis2)) =
          ternaryIntIndexToRat z2 ∧
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis3)) =
          ternaryIntIndexToRat z3 := by
    rcases hT with hpositive | hnegative
    · exact ⟨y1, y2, y3,
        (hpositive _).symm.trans hmap1,
        (hpositive _).symm.trans hmap2,
        (hpositive _).symm.trans hmap3⟩
    · have hneg1 := congrArg Neg.neg ((hnegative _).symm.trans hmap1)
      have hneg2 := congrArg Neg.neg ((hnegative _).symm.trans hmap2)
      have hneg3 := congrArg Neg.neg ((hnegative _).symm.trans hmap3)
      exact ⟨-y1, -y2, -y3,
        by simpa [ternaryIntIndexToRat] using hneg1,
        by simpa [ternaryIntIndexToRat] using hneg2,
        by simpa [ternaryIntIndexToRat] using hneg3⟩
  have hdiv1 := householder_integral_p_basis1_norm_dvd p w z1 hw hh1
  have hdiv2 := householder_integral_p_basis2_norm_dvd p w z2 hw hh2
  have hdiv3 := householder_integral_p_basis3_norm_dvd p w z3 hw hh3
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormpos : 0 < ternaryNorm w.1.1 w.1.2 w.2 := by
    have hqpos := ternaryRatNorm_pos hcast_ne
    rw [ternaryRatNorm_intIndexToRat] at hqpos
    exact_mod_cast hqpos
  let n : ℕ := (ternaryNorm w.1.1 w.1.2 w.2).toNat
  have hnormn : ternaryNorm w.1.1 w.1.2 w.2 = (n : ℤ) := by
    exact (Int.toNat_of_nonneg (le_of_lt hnormpos)).symm
  have hn_dvd : n ∣ 2 * p := by
    apply primitive_reflection_norm_dvd_two_mul p n
      w.1.1 w.1.2 w.2 b1 b2 b3 hprimitive
    · simpa [hnormn] using hdiv1
    · simpa [hnormn] using hdiv2
    · simpa [hnormn] using hdiv3
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  rcases eq_one_or_two_or_prime_or_two_prime_of_dvd hp hn_dvd with
    hn | hn | hn | hn
  · exact Or.inl (by rw [hnormn, hn]; norm_num)
  · exact Or.inr (Or.inl (by rw [hnormn, hn]; norm_num))
  · exact Or.inr (Or.inr (Or.inl (by rw [hnormn, hn])))
  · exact Or.inr (Or.inr (Or.inr (by
      calc
        ternaryNorm w.1.1 w.1.2 w.2 = (n : ℤ) := hnormn
        _ = ((2 * p : ℕ) : ℤ) := by exact_mod_cast hn
        _ = 2 * (p : ℤ) := by push_cast; rfl)))

set_option maxHeartbeats 1000000 in
/-- Canonical nonzero, pairwise-distinct indices exclude every globally
integral signed-coordinate or signed-swap Householder symmetry.  Coherence
maps the three elementary kernel vectors to the same congruence lattice;
the norm-one and norm-two reflections would respectively force `p` to divide
`2ab` or `b²-a²` for canonical coordinates `0 < a < b < p/2`. -/
theorem CoherentThetaInvolution.primitive_householder_norm_ne_one_two
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 ≠ 1 ∧
      ternaryNorm w.1.1 w.1.2 w.2 ≠ 2 := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hj : 0 < j := by omega
  have hk : 0 < k := by omega
  have hip : i < p := by omega
  have hjp : j < p := by omega
  have hkp : k < p := by omega
  have hp2 : 2 < p := by omega
  have hnot12prod : ¬(p : ℤ) ∣ 2 * (i : ℤ) * (j : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hi hj hip hjp hp2
  have hnot13prod : ¬(p : ℤ) ∣ 2 * (i : ℤ) * (k : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hi hk hip hkp hp2
  have hnot23prod : ¬(p : ℤ) ∣ 2 * (j : ℤ) * (k : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hj hk hjp hkp hp2
  have hnot12diff : ¬(p : ℤ) ∣ (j : ℤ) ^ 2 - (i : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hi hij (by omega)
  have hik : i < k := by omega
  have hnot13diff : ¬(p : ℤ) ∣ (k : ℤ) ^ 2 - (i : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hi hik hpk
  have hnot23diff : ¬(p : ℤ) ∣ (k : ℤ) ^ 2 - (j : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hj hjk hpk
  let d12 : TernaryIntIndex := (((j : ℤ), -(i : ℤ)), 0)
  let d13 : TernaryIntIndex := (((k : ℤ), 0), -(i : ℤ))
  let d23 : TernaryIntIndex := ((0, (k : ℤ)), -(j : ℤ))
  have hd12 : InThetaIndexLattice p i j k d12 := by
    refine ⟨0, ?_⟩
    simp [d12, affineIndexDot]
    ring
  have hd13 : InThetaIndexLattice p i j k d13 := by
    refine ⟨0, ?_⟩
    simp [d13, affineIndexDot]
    ring
  have hd23 : InThetaIndexLattice p i j k d23 := by
    refine ⟨0, ?_⟩
    simp [d23, affineIndexDot]
    ring
  obtain ⟨z12, ⟨q12, hq12⟩, hmap12⟩ :=
    T.maps_admissible_thetaIndexLattice
      ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩ hR d12 hd12
  obtain ⟨z13, ⟨q13, hq13⟩, hmap13⟩ :=
    T.maps_admissible_thetaIndexLattice
      ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩ hR d13 hd13
  obtain ⟨z23, ⟨q23, hq23⟩, hmap23⟩ :=
    T.maps_admissible_thetaIndexLattice
      ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩ hR d23 hd23
  have hdot12 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d12)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d12)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d12)).2 =
        (p : ℚ) * (q12 : ℚ) := by
    rw [hmap12]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq12
  have hdot13 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d13)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d13)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d13)).2 =
        (p : ℚ) * (q13 : ℚ) := by
    rw [hmap13]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq13
  have hdot23 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d23)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d23)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d23)).2 =
        (p : ℚ) * (q23 : ℚ) := by
    rw [hmap23]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq23
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  have hsmall_impossible :
      ternaryNorm w1 w2 w3 = 1 ∨ ternaryNorm w1 w2 w3 = 2 → False := by
    intro hsmall
    have hsquares : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 ≤ 2 := by
      rcases hsmall with hnorm | hnorm <;>
        simp only [ternaryNorm] at hnorm <;> omega
    have hw1lo : -2 < w1 := by nlinarith [sq_nonneg w2, sq_nonneg w3]
    have hw1hi : w1 < 2 := by nlinarith [sq_nonneg w2, sq_nonneg w3]
    have hw2lo : -2 < w2 := by nlinarith [sq_nonneg w1, sq_nonneg w3]
    have hw2hi : w2 < 2 := by nlinarith [sq_nonneg w1, sq_nonneg w3]
    have hw3lo : -2 < w3 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have hw3hi : w3 < 2 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have hsupport :
        (w2 = 0 ∧ w3 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w1 = 0 ∧ w3 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w1 = 0 ∧ w2 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w3 = 0 ∧ ternaryNorm w1 w2 w3 = 2) ∨
        (w2 = 0 ∧ ternaryNorm w1 w2 w3 = 2) ∨
        (w1 = 0 ∧ ternaryNorm w1 w2 w3 = 2) := by
      interval_cases w1 <;> interval_cases w2 <;> interval_cases w3
      all_goals norm_num [ternaryNorm] at hsmall
      all_goals norm_num [ternaryNorm]
    obtain ⟨r12, r13, r23, hHdot12, hHdot13, hHdot23⟩ :
        ∃ r12 r13 r23 : ℤ,
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d12)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d12)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d12)).2 = (p : ℚ) * r12 ∧
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d13)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d13)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d13)).2 = (p : ℚ) * r13 ∧
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d23)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d23)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d23)).2 = (p : ℚ) * r23 := by
      rcases hT with hpositive | hnegative
      · exact ⟨q12, q13, q23,
          by simpa only [hpositive] using hdot12,
          by simpa only [hpositive] using hdot13,
          by simpa only [hpositive] using hdot23⟩
      · rw [hnegative] at hdot12 hdot13 hdot23
        refine ⟨-q12, -q13, -q23, ?_, ?_, ?_⟩ <;>
          simp at hdot12 hdot13 hdot23 ⊢ <;> nlinarith
    rcases hsupport with haxis1 | haxis2 | haxis3 | hpair12 | hpair13 | hpair23
    · rcases haxis1 with ⟨rfl, rfl, hnorm⟩
      interval_cases w1 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (j : ℤ)) r12 <;>
        first
        | left; push_cast; nlinarith only [hHdot12]
        | right; push_cast; nlinarith only [hHdot12]
    · rcases haxis2 with ⟨rfl, rfl, hnorm⟩
      interval_cases w2 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (j : ℤ)) r12 <;>
        left <;> push_cast <;> nlinarith only [hHdot12]
    · rcases haxis3 with ⟨rfl, rfl, hnorm⟩
      interval_cases w3 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d13, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot13 <;>
        apply hnot13prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (k : ℤ)) r13 <;>
        left <;> push_cast <;> nlinarith only [hHdot13]
    · rcases hpair12 with ⟨rfl, hnorm⟩
      interval_cases w1 <;> interval_cases w2 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((j : ℤ) ^ 2 - (i : ℤ) ^ 2) r12 <;>
        first
        | left; push_cast; nlinarith only [hHdot12]
        | right; push_cast; nlinarith only [hHdot12]
    · rcases hpair13 with ⟨rfl, hnorm⟩
      interval_cases w1 <;> interval_cases w3 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d13, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot13 <;>
        apply hnot13diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((k : ℤ) ^ 2 - (i : ℤ) ^ 2) r13 <;>
        first
        | left; push_cast; nlinarith only [hHdot13]
        | right; push_cast; nlinarith only [hHdot13]
    · rcases hpair23 with ⟨rfl, hnorm⟩
      interval_cases w2 <;> interval_cases w3 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d23, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot23 <;>
        apply hnot23diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((k : ℤ) ^ 2 - (j : ℤ) ^ 2) r23 <;>
        first
        | left; push_cast; nlinarith only [hHdot23]
        | right; push_cast; nlinarith only [hHdot23]
  constructor
  · intro hnorm
    exact hsmall_impossible (Or.inl hnorm)
  · intro hnorm
    exact hsmall_impossible (Or.inr hnorm)

/-- The finite stabilizer exclusion sharpens the denominator list to the two
short-root norms. -/
theorem CoherentThetaInvolution.primitive_householder_norm_eq_prime_or_two_prime
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p := by
  have hcases := primitive_householder_norm_cases_of_coherent T
    hadmissible hR w hw b1 b2 b3 hprimitive hT
  have hsmall := T.primitive_householder_norm_ne_one_two
    hadmissible hR w hT
  rcases hcases with hnorm | hnorm | hnorm | hnorm
  · exact (hsmall.1 hnorm).elim
  · exact (hsmall.2 hnorm).elim
  · exact Or.inl hnorm
  · exact Or.inr hnorm

/-- If a primitive integral Householder image is integral, the squared norm
of the normal divides twice its dot product with the source vector.  The
square-Bézout certificate combines the three coordinate integrality equations
without any coprimality black box. -/
theorem householder_integral_image_norm_dvd_two_dot
    (w x y : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hmap : ternaryRatHouseholder (ternaryIntIndexToRat w)
        (ternaryIntIndexToRat x) = ternaryIntIndexToRat y) :
    ternaryNorm w.1.1 w.1.2 w.2 ∣
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 := by
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormq : (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) ≠ 0 := by
    rw [← ternaryRatNorm_intIndexToRat]
    exact ne_of_gt (ternaryRatNorm_pos hcast_ne)
  have hnormexpand :
      ((w.1.1 : ℚ) ^ 2 + (w.1.2 : ℚ) ^ 2 + (w.2 : ℚ) ^ 2) =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) := by
    simp [ternaryNorm]
  have hcoord1 := congrArg (fun z : TernaryRatPoint => z.1.1) hmap
  have hcoord2 := congrArg (fun z : TernaryRatPoint => z.1.2) hmap
  have hcoord3 := congrArg (fun z : TernaryRatPoint => z.2) hmap
  simp [ternaryRatHouseholder, ternaryIntIndexToRat,
    ternaryRatDot, ternaryRatNorm] at hcoord1 hcoord2 hcoord3
  rw [hnormexpand] at hcoord1 hcoord2 hcoord3
  field_simp [hnormq] at hcoord1 hcoord2 hcoord3
  have hdiv1 :
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.1.1 =
        ternaryNorm w.1.1 w.1.2 w.2 * (x.1.1 - y.1.1) := by
    exact_mod_cast (show
      2 * ((w.1.1 : ℚ) * x.1.1 + (w.1.2 : ℚ) * x.1.2 +
          (w.2 : ℚ) * x.2) * w.1.1 =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * (x.1.1 - y.1.1) by
          linear_combination -hcoord1)
  have hdiv2 :
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.1.2 =
        ternaryNorm w.1.1 w.1.2 w.2 * (x.1.2 - y.1.2) := by
    exact_mod_cast (show
      2 * ((w.1.1 : ℚ) * x.1.1 + (w.1.2 : ℚ) * x.1.2 +
          (w.2 : ℚ) * x.2) * w.1.2 =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * (x.1.2 - y.1.2) by
          linear_combination -hcoord2)
  have hdiv3 :
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.2 =
        ternaryNorm w.1.1 w.1.2 w.2 * (x.2 - y.2) := by
    exact_mod_cast (show
      2 * ((w.1.1 : ℚ) * x.1.1 + (w.1.2 : ℚ) * x.1.2 +
          (w.2 : ℚ) * x.2) * w.2 =
        (ternaryNorm w.1.1 w.1.2 w.2 : ℚ) * (x.2 - y.2) by
          linear_combination -hcoord3)
  refine ⟨b1 * w.1.1 * (x.1.1 - y.1.1) +
      b2 * w.1.2 * (x.1.2 - y.1.2) +
      b3 * w.2 * (x.2 - y.2), ?_⟩
  calc
    2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 =
        2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 *
          (b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2) := by
            rw [hprimitive]
            ring
    _ = b1 * w.1.1 *
          (2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.1.1) +
        b2 * w.1.2 *
          (2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.1.2) +
        b3 * w.2 *
          (2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 * w.2) := by ring
    _ = ternaryNorm w.1.1 w.1.2 w.2 *
        (b1 * w.1.1 * (x.1.1 - y.1.1) +
          b2 * w.1.2 * (x.1.2 - y.1.2) +
          b3 * w.2 * (x.2 - y.2)) := by
            rw [hdiv1, hdiv2, hdiv3]
            ring

/-- On a short root, the rational Householder formula is exactly the
division-free integral reflection in all three coordinates. -/
theorem ternaryRatHouseholder_int_eq_shortRootReflect
    (p e c t : ℤ) (w x : TernaryIntIndex) (hp : p ≠ 0)
    (hroot : ternaryNorm w.1.1 w.1.2 w.2 = e * p)
    (hdot : ternaryDot x.1.1 x.1.2 x.2 w.1.1 w.1.2 w.2 = p * t)
    (hcoefficient : c * e = 2) :
    ternaryRatHouseholder (ternaryIntIndexToRat w)
        (ternaryIntIndexToRat x) =
      ternaryIntIndexToRat
        ((shortRootReflectCoord c t w.1.1 x.1.1,
          shortRootReflectCoord c t w.1.2 x.1.2),
          shortRootReflectCoord c t w.2 x.2) := by
  have he : e ≠ 0 := by
    intro hezero
    rw [hezero] at hcoefficient
    norm_num at hcoefficient
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hdotq : ternaryRatDot (ternaryIntIndexToRat x)
      (ternaryIntIndexToRat w) = (p : ℚ) * (t : ℚ) := by
    rcases w with ⟨⟨w1, w2⟩, w3⟩
    rcases x with ⟨⟨x1, x2⟩, x3⟩
    simp only [ternaryDot] at hdot
    simp [ternaryRatDot, ternaryIntIndexToRat]
    exact_mod_cast hdot
  have hnormq : ternaryRatNorm (ternaryIntIndexToRat w) =
      (e : ℚ) * (p : ℚ) := by
    rw [ternaryRatNorm_intIndexToRat]
    exact_mod_cast hroot
  have hcoefficientq : (c : ℚ) * (e : ℚ) = 2 := by
    exact_mod_cast hcoefficient
  have hscalar :
      2 * ternaryRatDot (ternaryIntIndexToRat x) (ternaryIntIndexToRat w) /
          ternaryRatNorm (ternaryIntIndexToRat w) = (c : ℚ) * t := by
    rw [hdotq, hnormq, div_eq_iff (mul_ne_zero heq hpq)]
    rw [← hcoefficientq]
    ring
  rw [ternaryRatHouseholder, hscalar]
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  simp [ternaryIntIndexToRat, shortRootReflectCoord]

/-- Bézout inverses modulo the same modulus multiply constructively. -/
lemma bezout_product_modulus
    (p a b ap aa bp bb : ℤ)
    (ha : ap * p + aa * a = 1) (hb : bp * p + bb * b = 1) :
    (ap + aa * a * bp) * p + (aa * bb) * (a * b) = 1 := by
  linear_combination ha + aa * a * hb

/-- A primitive projective lift has projective scalar invertible modulo the
modulus.  The primitive square certificate gives the inverse explicitly. -/
lemma primitive_projective_lift_lambda_bezout
    (p lambda i j k w1 w2 w3 a1 a2 a3 b1 b2 b3 : ℤ)
    (hw1 : w1 = lambda * i + p * a1)
    (hw2 : w2 = lambda * j + p * a2)
    (hw3 : w3 = lambda * k + p * a3)
    (hprimitive : b1 * w1 ^ 2 + b2 * w2 ^ 2 + b3 * w3 ^ 2 = 1) :
    ∃ bp bl : ℤ, bp * p + bl * lambda = 1 := by
  refine ⟨2 * lambda * (b1 * i * a1 + b2 * j * a2 + b3 * k * a3) +
      p * (b1 * a1 ^ 2 + b2 * a2 ^ 2 + b3 * a3 ^ 2),
    lambda * (b1 * i ^ 2 + b2 * j ^ 2 + b3 * k ^ 2), ?_⟩
  rw [hw1, hw2, hw3] at hprimitive
  nlinarith [hprimitive]

/-- On admissible data, either short-root coefficient (`2` for norm `p`,
`1` for norm `2p`) is invertible modulo `p`. -/
lemma short_root_coefficient_bezout
    {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (e c : ℤ)
    (he : e = 1 ∨ e = 2) (hcoefficient : c * e = 2) :
    ∃ bp bc : ℤ, bp * (p : ℤ) + bc * c = 1 := by
  have hpoddNat : Odd p := hp.odd_of_ne_two hp2
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  rcases he with rfl | rfl
  · have hc : c = 2 := by omega
    obtain ⟨z, hz⟩ := hpodd
    refine ⟨1, -z, ?_⟩
    rw [hc]
    omega
  · have hc : c = 1 := by omega
    exact ⟨0, 1, by simp [hc]⟩

lemma admissible_modulus_ne_zero_zmod3
    {p i j k : ℕ} (hadmissible : AdmissibleSparseTriple p i j k) :
    ((p : ℤ) : ZMod 3) ≠ 0 := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  intro hzero
  have hdivInt := (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) 3).mp hzero
  have hdivNat : 3 ∣ p := by exact_mod_cast hdivInt
  rcases (Nat.dvd_prime hp).mp hdivNat with hthreeone | hthreep
  · norm_num at hthreeone
  · exact hp3 hthreep.symm

/-- Every admissible progression residue has at least one Watson branch point
in its complete affine fiber. -/
lemma admissible_exists_theta_residue_point
    {p i j k R : ℕ} (hadmissible : AdmissibleSparseTriple p i j k) :
    ∃ x : TripleQuintBranchIndex, InThetaResidueFiber p i j k R x := by
  obtain ⟨bp, bv, hunit⟩ :=
    admissibleSparseTriple_exists_three_i_bezout hadmissible
  have hzero : InThetaIndexLattice p i j k (0 : TernaryIntIndex) := by
    exact ⟨0, by simp [affineIndexDot]⟩
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    thetaIndexLattice_difference_spanning_of_bezout
      p i j k R (0 : TernaryIntIndex) bp bv hunit hzero
  exact ⟨x, hx⟩

/-- For a coherent short reflection, every vector in the index-`p` kernel
has dot product divisible by `p` against the primitive normal.  The short
norm contributes a factor `p`; oddness cancels the remaining factor two. -/
theorem CoherentThetaInvolution.short_normal_dot_dvd_on_thetaIndexLattice
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 e : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hnorm : ternaryNorm w.1.1 w.1.2 w.2 = e * (p : ℤ))
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x))
    (x : TernaryIntIndex) (hx : InThetaIndexLattice p i j k x) :
    (p : ℤ) ∣ ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 := by
  obtain ⟨y, hy, hmap⟩ :=
    T.maps_admissible_thetaIndexLattice hadmissible hR x hx
  obtain ⟨z, hhouse⟩ : ∃ z : TernaryIntIndex,
      ternaryRatHouseholder (ternaryIntIndexToRat w)
          (ternaryIntIndexToRat x) = ternaryIntIndexToRat z := by
    rcases hT with hpositive | hnegative
    · exact ⟨y, (hpositive _).symm.trans hmap⟩
    · have hneg := congrArg Neg.neg ((hnegative _).symm.trans hmap)
      exact ⟨-y, by simpa [ternaryIntIndexToRat] using hneg⟩
  have hdiv := householder_integral_image_norm_dvd_two_dot
    w x z hw b1 b2 b3 hprimitive hhouse
  obtain ⟨q, hq⟩ := hdiv
  have hpdiv : (p : ℤ) ∣
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 := by
    refine ⟨e * q, ?_⟩
    calc
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 =
          ternaryNorm w.1.1 w.1.2 w.2 * q := hq
      _ = (p : ℤ) * (e * q) := by rw [hnorm]; ring
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  exact int_dvd_of_dvd_two_mul_of_odd (p : ℤ)
    (ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2) hpodd hpdiv

/-- **Projective extraction from coherence.**  A primitive coherent normal
of norm `p` or `2p` is forced to be a projective lift of the original
isotropic index vector. -/
theorem CoherentThetaInvolution.primitive_short_normal_projective_lift
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hnorm : ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ∃ e lambda a1 a2 a3 : ℤ,
      (e = 1 ∨ e = 2) ∧
      ternaryNorm w.1.1 w.1.2 w.2 = e * p ∧
      w.1.1 = lambda * i + p * a1 ∧
      w.1.2 = lambda * j + p * a2 ∧
      w.2 = lambda * k + p * a3 := by
  obtain ⟨e, he, hnorme⟩ : ∃ e : ℤ, (e = 1 ∨ e = 2) ∧
      ternaryNorm w.1.1 w.1.2 w.2 = e * p := by
    rcases hnorm with hnorm | hnorm
    · exact ⟨1, Or.inl rfl, by simpa using hnorm⟩
    · exact ⟨2, Or.inr rfl, by simpa using hnorm⟩
  obtain ⟨bp, bv, hunit3⟩ :=
    admissibleSparseTriple_exists_three_i_bezout hadmissible
  have hunit : bp * (p : ℤ) + (3 * bv) * (i : ℤ) = 1 := by
    linear_combination hunit3
  have hkernel : ∀ x1 x2 x3 : ℤ,
      (p : ℤ) ∣ ternaryDot i j k x1 x2 x3 →
        (p : ℤ) ∣ ternaryDot w.1.1 w.1.2 w.2 x1 x2 x3 := by
    intro x1 x2 x3 hx
    let x : TernaryIntIndex := ((x1, x2), x3)
    have hxL : InThetaIndexLattice p i j k x := by
      obtain ⟨q, hq⟩ := hx
      refine ⟨q, ?_⟩
      simpa [x, affineIndexDot, ternaryDot] using hq
    simpa [x] using T.short_normal_dot_dvd_on_thetaIndexLattice
      hadmissible hR w hw b1 b2 b3 e hprimitive hnorme hT x hxL
  obtain ⟨lambda, a1, a2, a3, hw1, hw2, hw3⟩ :=
    congruence_kernel_forces_projective_lift (p : ℤ)
      i j k w.1.1 w.1.2 w.2 bp (3 * bv) hunit hkernel
  exact ⟨e, lambda, a1, a2, a3, he, hnorme, hw1, hw2, hw3⟩

/-- **Primitive arithmetic extraction from coherence.**  Every coherent theta
involution has a primitive integral Householder normal, its linear part is the
corresponding reflection or negative reflection, and the squared norm of that
normal is forced into the sharp denominator list `1, 2, p, 2p`.

The first two cases are precisely the integral signed-coordinate/permutation
reflections.  The theorem below excludes their stabilizers under admissibility;
the denominator argument itself makes no hidden genericity assumption. -/
theorem CoherentThetaInvolution.exists_primitive_householder_with_norm_cases
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p) :
    ∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        (ternaryNorm w.1.1 w.1.2 w.2 = 1 ∨
          ternaryNorm w.1.1 w.1.2 w.2 = 2 ∨
          ternaryNorm w.1.1 w.1.2 w.2 = p ∨
          ternaryNorm w.1.1 w.1.2 w.2 = 2 * p) ∧
        ((∀ x, T.linear x =
            ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
          (∀ x, T.linear x =
            -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) := by
  rcases T.exists_primitive_integral_householder_or_neg with
    hpositive | hnegative
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hpositive
    have hcases := primitive_householder_norm_cases_of_coherent T
      hadmissible hR w hw b1 b2 b3 hprimitive (Or.inl hT)
    exact ⟨w, hw, b1, b2, b3, hprimitive, hcases, Or.inl hT⟩
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hnegative
    have hcases := primitive_householder_norm_cases_of_coherent T
      hadmissible hR w hw b1 b2 b3 hprimitive (Or.inr hT)
    exact ⟨w, hw, b1, b2, b3, hprimitive, hcases, Or.inr hT⟩

/-- **Short projective-root extraction from coherence.**  This packages the
closed arithmetic converse: a coherent theta involution supplies a primitive
integral normal of norm `p` or `2p`, projectively congruent to `(i,j,k)`
modulo `p`, and realizes the involution as its Householder reflection or
negative reflection. -/
theorem CoherentThetaInvolution.exists_primitive_short_projective_householder
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p) :
    ∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 e lambda a1 a2 a3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        (e = 1 ∨ e = 2) ∧
        ternaryNorm w.1.1 w.1.2 w.2 = e * p ∧
        w.1.1 = lambda * i + p * a1 ∧
        w.1.2 = lambda * j + p * a2 ∧
        w.2 = lambda * k + p * a3 ∧
        ((∀ x, T.linear x =
            ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
          (∀ x, T.linear x =
            -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) := by
  rcases T.exists_primitive_integral_householder_or_neg with
    hpositive | hnegative
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hpositive
    have hsign :
        (∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
        (∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := Or.inl hT
    have hnorm := T.primitive_householder_norm_eq_prime_or_two_prime
      hadmissible hR w hw b1 b2 b3 hprimitive hsign
    obtain ⟨e, lambda, a1, a2, a3, he, hroot, hw1, hw2, hw3⟩ :=
      T.primitive_short_normal_projective_lift hadmissible hR
        w hw b1 b2 b3 hprimitive hnorm hsign
    exact ⟨w, hw, b1, b2, b3, e, lambda, a1, a2, a3,
      hprimitive, he, hroot, hw1, hw2, hw3, hsign⟩
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hnegative
    have hsign :
        (∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
        (∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := Or.inr hT
    have hnorm := T.primitive_householder_norm_eq_prime_or_two_prime
      hadmissible hR w hw b1 b2 b3 hprimitive hsign
    obtain ⟨e, lambda, a1, a2, a3, he, hroot, hw1, hw2, hw3⟩ :=
      T.primitive_short_normal_projective_lift hadmissible hR
        w hw b1 b2 b3 hprimitive hnorm hsign
    exact ⟨w, hw, b1, b2, b3, e, lambda, a1, a2, a3,
      hprimitive, he, hroot, hw1, hw2, hw3, hsign⟩

/-- **Branch-target extraction from coherence.**  Once the primitive short
projective normal has been extracted, closure of one actual Watson point and
weight reversal force the correct mod-three sign and the corresponding exact
positive or negative projective target congruence. -/
theorem CoherentThetaInvolution.short_projective_householder_target_case
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (w : TernaryIntIndex) (b1 b2 b3 e lambda a1 a2 a3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm w.1.1 w.1.2 w.2 = e * p)
    (hw1 : w.1.1 = lambda * i + p * a1)
    (hw2 : w.1.2 = lambda * j + p * a2)
    (hw3 : w.2 = lambda * k + p * a3)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ∃ c u : ℤ,
      c * e = 2 ∧
      ternaryDot i j k w.1.1 w.1.2 w.2 = p * u ∧
      (((((e * (p : ℤ) : ℤ) : ZMod 3) = 1) ∧
          ∃ h : ℤ, 2 * lambda * R =
            w.1.1 + w.1.2 + w.2 - 6 * u + p * h) ∨
        ((((e * (p : ℤ) : ℤ) : ZMod 3) = 2) ∧
          ∃ base h : ℤ,
            base = 2 * lambda * R - (w.1.1 + w.1.2 + w.2) + 6 * u ∧
            c * lambda * base = 12 + p * h)) := by
  let c : ℤ := 3 - e
  have hcoefficient : c * e = 2 := by
    rcases he with rfl | rfl <;> simp [c]
  obtain ⟨isotropicQ, hisotropicQ⟩ := hadmissible.2.2.2.2.2.2
  let u : ℤ := lambda * isotropicQ + ternaryDot i j k a1 a2 a3
  have hvw : ternaryDot i j k w.1.1 w.1.2 w.2 = p * u := by
    exact projectiveLift_is_in_lattice p lambda i j k w.1.1 w.1.2 w.2
      a1 a2 a3 isotropicQ hw1 hw2 hw3 hisotropicQ
  obtain ⟨x, hxfiber⟩ := admissible_exists_theta_residue_point
    (R := R) hadmissible
  have had := hadmissible
  rcases had with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  have hxprog := (onThetaProgression_iff_inThetaResidueFiber
    p i j k R x hi hpi hj hpj hk hpk hpodd hR).mpr hxfiber
  obtain ⟨q, hresidue⟩ := hxfiber
  let base : ℤ :=
    2 * lambda * R - (w.1.1 + w.1.2 + w.2) + 6 * u
  let m : ℤ := 2 * lambda * q +
    2 * projectiveLiftBranchCorrection
      (pointB1 x) (pointB2 x) (pointB3 x) a1 a2 a3
      (pointN1 x) (pointN2 x) (pointN3 x)
  have hdot : ternaryDot
      (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
      w.1.1 w.1.2 w.2 = p * (base + p * m) := by
    have hquot := projectiveRoot_reflection_quotient
      (pointB1 x) (pointB2 x) (pointB3 x)
      p lambda i j k w.1.1 w.1.2 w.2 a1 a2 a3 u
      (pointN1 x) (pointN2 x) (pointN3 x) R q
      hw1 hw2 hw3 hvw (by simpa [pointLinearResidue] using hresidue)
    simpa [pointCoord1, pointCoord2, pointCoord3, base, m] using hquot
  have hhouse := ternaryRatHouseholder_int_eq_shortRootReflect
    p e c (base + p * m) w (pointThetaVector p i j k x)
    (by omega) hroot (by simpa [pointThetaVector, ternaryDot] using hdot)
    hcoefficient
  let y := T.partner x
  have hweightReverse := T.weight_reverse x hxprog
  have hweight : branchSign (pointB1 y) * branchSign (pointB2 y) *
      branchSign (pointB3 y) =
      -(branchSign (pointB1 x) * branchSign (pointB2 x) *
        branchSign (pointB3 x)) := by
    dsimp [y] at hweightReverse ⊢
    simp only [pointBranchWeight] at hweightReverse
    linear_combination -hweightReverse
  have hpmod3 : ((p : ℤ) : ZMod 3) ≠ 0 :=
    admissible_modulus_ne_zero_zmod3 hadmissible
  obtain ⟨bpi, bi3, hi3unit⟩ :=
    admissibleSparseTriple_exists_three_i_bezout hadmissible
  have hiunit : bpi * (p : ℤ) + (3 * bi3) * (i : ℤ) = 1 := by
    linear_combination hi3unit
  rcases hT with hpositive | hnegative
  · have hcast : ternaryIntIndexToRat (pointThetaVector p i j k y) =
        ternaryIntIndexToRat
          ((shortRootReflectCoord c (base + p * m) w.1.1 (pointCoord1 p i x),
            shortRootReflectCoord c (base + p * m) w.1.2 (pointCoord2 p j x)),
            shortRootReflectCoord c (base + p * m) w.2 (pointCoord3 p k x)) := by
      calc
        ternaryIntIndexToRat (pointThetaVector p i j k y) =
            T.linear (pointThetaVectorRat p i j k x) :=
          (T.coordinate_transport x hxprog).symm
        _ = ternaryRatHouseholder (ternaryIntIndexToRat w)
            (pointThetaVectorRat p i j k x) := hpositive _
        _ = _ := by simpa [pointThetaVectorRat, pointThetaVector] using hhouse
    have hint := ternaryIntIndexToRat_injective hcast
    have hclosure1 : pointCoord1 p i y =
        shortRootReflectCoord c (base + p * m) w.1.1 (pointCoord1 p i x) :=
      congrArg (fun z : TernaryIntIndex => z.1.1) hint
    have hclosure2 : pointCoord2 p j y =
        shortRootReflectCoord c (base + p * m) w.1.2 (pointCoord2 p j x) :=
      congrArg (fun z : TernaryIntIndex => z.1.2) hint
    have hclosure3 : pointCoord3 p k y =
        shortRootReflectCoord c (base + p * m) w.2 (pointCoord3 p k x) :=
      congrArg (fun z : TernaryIntIndex => z.2) hint
    have hmod := positive_integral_branch_reversal_forces_norm_one_mod3
      (pointB1 x) (pointB2 x) (pointB3 x)
      (pointB1 y) (pointB2 y) (pointB3 y)
      p e c (base + p * m) w.1.1 w.1.2 w.2 i j k
      (pointN1 x) (pointN2 x) (pointN3 x)
      (pointN1 y) (pointN2 y) (pointN3 y)
      he hpmod3 hcoefficient hroot
      (by simpa [pointCoord1, pointCoord2, pointCoord3] using hdot)
      (by simpa [pointCoord1] using hclosure1)
      (by simpa [pointCoord2] using hclosure2)
      (by simpa [pointCoord3] using hclosure3) hweight
    obtain ⟨bpl, bl, hlunit⟩ := primitive_projective_lift_lambda_bezout
      p lambda i j k w.1.1 w.1.2 w.2 a1 a2 a3 b1 b2 b3
      hw1 hw2 hw3 hprimitive
    obtain ⟨bpc, bc, hcunit⟩ := short_root_coefficient_bezout hp
      (by omega) e c he hcoefficient
    have hclunit := bezout_product_modulus (p : ℤ) c lambda
      bpc bc bpl bl hcunit hlunit
    have hcliunit := bezout_product_modulus (p : ℤ) (c * lambda) i
      (bpc + bc * c * bpl) (bc * bl) bpi (3 * bi3) hclunit hiunit
    obtain ⟨h, hbase⟩ :=
      projectiveRoot_positive_target_necessary_of_coordinate_closure
        (pointB1 x) (pointB1 y) p c lambda base i w.1.1 a1 m
        (pointN1 x) (pointN1 y)
        (bpc + bc * c * bpl + (bc * bl) * (c * lambda) * bpi)
        ((bc * bl) * (3 * bi3)) hw1 hcliunit
        (by simpa [pointCoord1] using hclosure1)
    refine ⟨c, u, hcoefficient, hvw, Or.inl ⟨hmod, ?_⟩⟩
    exact ⟨h, by dsimp [base] at hbase; linear_combination hbase⟩
  · have hcast : ternaryIntIndexToRat (pointThetaVector p i j k y) =
        ternaryIntIndexToRat
          (-((shortRootReflectCoord c (base + p * m) w.1.1 (pointCoord1 p i x),
            shortRootReflectCoord c (base + p * m) w.1.2 (pointCoord2 p j x)),
            shortRootReflectCoord c (base + p * m) w.2 (pointCoord3 p k x))) := by
      calc
        ternaryIntIndexToRat (pointThetaVector p i j k y) =
            T.linear (pointThetaVectorRat p i j k x) :=
          (T.coordinate_transport x hxprog).symm
        _ = -ternaryRatHouseholder (ternaryIntIndexToRat w)
            (pointThetaVectorRat p i j k x) := hnegative _
        _ = _ := by
          change -ternaryRatHouseholder (ternaryIntIndexToRat w)
              (ternaryIntIndexToRat (pointThetaVector p i j k x)) =
            ternaryIntIndexToRat
              (-((shortRootReflectCoord c (base + p * m) w.1.1
                    (pointThetaVector p i j k x).1.1,
                  shortRootReflectCoord c (base + p * m) w.1.2
                    (pointThetaVector p i j k x).1.2),
                shortRootReflectCoord c (base + p * m) w.2
                  (pointThetaVector p i j k x).2))
          rw [hhouse]
          simp [ternaryIntIndexToRat]
    have hint := ternaryIntIndexToRat_injective hcast
    have hclosure1 : pointCoord1 p i y =
        -shortRootReflectCoord c (base + p * m) w.1.1 (pointCoord1 p i x) :=
      congrArg (fun z : TernaryIntIndex => z.1.1) hint
    have hclosure2 : pointCoord2 p j y =
        -shortRootReflectCoord c (base + p * m) w.1.2 (pointCoord2 p j x) :=
      congrArg (fun z : TernaryIntIndex => z.1.2) hint
    have hclosure3 : pointCoord3 p k y =
        -shortRootReflectCoord c (base + p * m) w.2 (pointCoord3 p k x) :=
      congrArg (fun z : TernaryIntIndex => z.2) hint
    have hmod := negative_integral_branch_reversal_forces_norm_two_mod3
      (pointB1 x) (pointB2 x) (pointB3 x)
      (pointB1 y) (pointB2 y) (pointB3 y)
      p e c (base + p * m) w.1.1 w.1.2 w.2 i j k
      (pointN1 x) (pointN2 x) (pointN3 x)
      (pointN1 y) (pointN2 y) (pointN3 y)
      he hpmod3 hcoefficient hroot
      (by simpa [pointCoord1, pointCoord2, pointCoord3] using hdot)
      (by simpa [pointCoord1] using hclosure1)
      (by simpa [pointCoord2] using hclosure2)
      (by simpa [pointCoord3] using hclosure3) hweight
    obtain ⟨h, htarget⟩ :=
      projectiveRoot_negative_target_necessary_of_coordinate_closure
        (pointB1 x) (pointB1 y) p c lambda base i w.1.1 a1 m
        (pointN1 x) (pointN1 y) bpi (3 * bi3) hw1 hiunit
        (by simpa [pointCoord1] using hclosure1)
    refine ⟨c, u, hcoefficient, hvw, Or.inr ⟨hmod, base, h, rfl, htarget⟩⟩

/-- **Arithmetic classification is closed.**  Every coherent theta
involution on admissible Watson data produces the complete short projective
root certificate, including the forced branch target law. -/
theorem CoherentThetaInvolution.hasProjectiveRootTarget
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p) :
    HasProjectiveRootTarget p i j k R := by
  obtain ⟨w, hw, b1, b2, b3, e, lambda, a1, a2, a3,
    hprimitive, he, hroot, hw1, hw2, hw3, hT⟩ :=
      T.exists_primitive_short_projective_householder hadmissible hR
  obtain ⟨c, u, hcoefficient, hvw, hcase⟩ :=
    T.short_projective_householder_target_case hadmissible hR w
      b1 b2 b3 e lambda a1 a2 a3 hprimitive he hroot hw1 hw2 hw3 hT
  exact ⟨{
    lambda := lambda
    e := e
    c := c
    w1 := w.1.1
    w2 := w.1.2
    w3 := w.2
    a1 := a1
    a2 := a2
    a3 := a3
    u := u
    he := he
    hw1 := hw1
    hw2 := hw2
    hw3 := hw3
    hvw := hvw
    hroot := hroot
    hcoefficient := hcoefficient
    hcase := hcase }⟩

/-- The arithmetic-classification proposition isolated upstream is now a
theorem, not a remaining hypothesis. -/
theorem admissibleThetaInvolutionClassification_proved
    (p i j k R : ℕ) :
    AdmissibleThetaInvolutionClassification p i j k R := by
  intro hadmissible hR hT
  exact hT.some.hasProjectiveRootTarget hadmissible hR

/-- **One-frontier reduction.**  With arithmetic classification closed,
spectral coherence alone implies admissible theta-coset rigidity. -/
theorem admissibleThetaCosetRigidity_of_geometricCoherence
    (p i j k R : ℕ)
    (hcoherence : AdmissibleThetaGeometricCoherence p i j k R) :
    AdmissibleThetaCosetRigidity p i j k R :=
  admissibleThetaCosetRigidity_of_geometricCoherence_of_classification
    p i j k R hcoherence
      (admissibleThetaInvolutionClassification_proved p i j k R)

/-- Consequently spectral coherence is the sole remaining implication needed
for the corrected admissible Root--Vanishing equivalence. -/
theorem admissibleRootVanishingRigidity_of_geometricCoherence
    (p i j k R : ℕ)
    (hcoherence : AdmissibleThetaGeometricCoherence p i j k R) :
    AdmissibleRootVanishingRigidity p i j k R :=
  admissibleRootVanishingRigidity_of_theta_geometry p i j k R hcoherence
    (admissibleThetaInvolutionClassification_proved p i j k R)

/-! ### Converse geometry: a root certificate produces coherence -/

/-- The Householder formula as a rational linear map. -/
def ternaryRatHouseholderLinear (w : TernaryRatPoint) :
    TernaryRatPoint →ₗ[ℚ] TernaryRatPoint where
  toFun := ternaryRatHouseholder w
  map_add' := by
    intro x y
    rcases w with ⟨⟨w1, w2⟩, w3⟩
    rcases x with ⟨⟨x1, x2⟩, x3⟩
    rcases y with ⟨⟨y1, y2⟩, y3⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ternaryRatHouseholder, ternaryRatDot, ternaryRatNorm] <;> ring
    · simp [ternaryRatHouseholder, ternaryRatDot, ternaryRatNorm]
      ring
  map_smul' := by
    intro c x
    rcases w with ⟨⟨w1, w2⟩, w3⟩
    rcases x with ⟨⟨x1, x2⟩, x3⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ternaryRatHouseholder, ternaryRatDot, ternaryRatNorm] <;> ring
    · simp [ternaryRatHouseholder, ternaryRatDot, ternaryRatNorm]
      ring

@[simp] lemma ternaryRatHouseholderLinear_apply
    (w x : TernaryRatPoint) :
    ternaryRatHouseholderLinear w x = ternaryRatHouseholder w x := rfl

lemma ternaryRatHouseholder_dot_normal
    (w x : TernaryRatPoint) (hw : w ≠ 0) :
    ternaryRatDot (ternaryRatHouseholder w x) w = -ternaryRatDot x w := by
  have hnorm : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hw)
  rw [ternaryRatHouseholder, ternaryRatDot_sub_left,
    ternaryRatDot_smul_left, ternaryRatDot_self]
  field_simp [hnorm]
  ring

lemma ternaryRatHouseholder_norm
    (w x : TernaryRatPoint) (hw : w ≠ 0) :
    ternaryRatNorm (ternaryRatHouseholder w x) = ternaryRatNorm x := by
  have hnorm : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hw)
  rw [ternaryRatHouseholder, sub_eq_add_neg, ← neg_smul,
    ternaryRatNorm_add, ternaryRatDot_smul_right, ternaryRatNorm_smul]
  field_simp [hnorm]
  ring

lemma ternaryRatHouseholder_involutive
    (w x : TernaryRatPoint) (hw : w ≠ 0) :
    ternaryRatHouseholder w (ternaryRatHouseholder w x) = x := by
  rw [ternaryRatHouseholder,
    ternaryRatHouseholder_dot_normal w x hw]
  dsimp [ternaryRatHouseholder]
  have hnorm : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hw)
  field_simp [hnorm]
  module

lemma ternaryRatHouseholder_normal
    (w : TernaryRatPoint) (hw : w ≠ 0) :
    ternaryRatHouseholder w w = -w := by
  rw [ternaryRatHouseholder, ternaryRatDot_self]
  have hnorm : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hw)
  field_simp [hnorm]
  module

lemma ternaryRatHouseholder_fixed_of_orthogonal
    (w x : TernaryRatPoint) (horthogonal : ternaryRatDot x w = 0) :
    ternaryRatHouseholder w x = x := by
  simp [ternaryRatHouseholder, horthogonal]

lemma ternaryRatPoint_eq_zero_of_eq_neg
    (x : TernaryRatPoint) (h : x = -x) : x = 0 := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  apply Prod.ext
  · apply Prod.ext
    · have h1 := congrArg (fun z : TernaryRatPoint => z.1.1) h
      dsimp at h1 ⊢
      linarith
    · have h2 := congrArg (fun z : TernaryRatPoint => z.1.2) h
      dsimp at h2 ⊢
      linarith
  · have h3 := congrArg (fun z : TernaryRatPoint => z.2) h
    dsimp at h3 ⊢
    linarith

/-- Every nonzero ternary normal has a nonzero rational orthogonal vector. -/
lemma exists_nonzero_ternaryRatPoint_orthogonal
    (w : TernaryRatPoint) (hw : w ≠ 0) :
    ∃ x : TernaryRatPoint, x ≠ 0 ∧ ternaryRatDot x w = 0 := by
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  by_cases h12 : w1 = 0 ∧ w2 = 0
  · refine ⟨((1, 0), 0), by norm_num, ?_⟩
    simp [ternaryRatDot, h12.1, h12.2]
  · refine ⟨((w2, -w1), 0), ?_, ?_⟩
    · intro hzero
      apply h12
      constructor
      · have h1 := congrArg (fun z : TernaryRatPoint => z.1.2) hzero
        dsimp at h1
        exact neg_eq_zero.mp h1
      · have h2 := congrArg (fun z : TernaryRatPoint => z.1.1) hzero
        simpa using h2
    · simp [ternaryRatDot]
      ring

/-- A nonzero rational Householder reflection is a noncentral orthogonal
involution in the exact structure used by theta coherence. -/
def rationalTernaryHouseholderInvolution
    (w : TernaryRatPoint) (hw : w ≠ 0) :
    RationalTernaryOrthogonalInvolution where
  linear := ternaryRatHouseholderLinear w
  norm_preserving := fun x => ternaryRatHouseholder_norm w x hw
  involutive := fun x => ternaryRatHouseholder_involutive w x hw
  not_identity := ⟨w, by
    rw [ternaryRatHouseholderLinear_apply, ternaryRatHouseholder_normal w hw]
    intro h
    exact hw (ternaryRatPoint_eq_zero_of_eq_neg w h.symm)⟩
  not_neg_identity := by
    obtain ⟨x, hx, horthogonal⟩ := exists_nonzero_ternaryRatPoint_orthogonal w hw
    refine ⟨x, ?_⟩
    rw [ternaryRatHouseholderLinear_apply,
      ternaryRatHouseholder_fixed_of_orthogonal w x horthogonal]
    intro h
    exact hx (ternaryRatPoint_eq_zero_of_eq_neg x h)

/-- The negative of a nonzero Householder reflection is the other noncentral
orthogonal involution type. -/
def rationalTernaryNegHouseholderInvolution
    (w : TernaryRatPoint) (hw : w ≠ 0) :
    RationalTernaryOrthogonalInvolution where
  linear := -ternaryRatHouseholderLinear w
  norm_preserving := by
    intro x
    change ternaryRatNorm (-ternaryRatHouseholder w x) = ternaryRatNorm x
    rw [show ternaryRatNorm (-ternaryRatHouseholder w x) =
      ternaryRatNorm (ternaryRatHouseholder w x) by
        rcases ternaryRatHouseholder w x with ⟨⟨x1, x2⟩, x3⟩
        simp [ternaryRatNorm]]
    exact ternaryRatHouseholder_norm w x hw
  involutive := by
    intro x
    change -ternaryRatHouseholder w (-ternaryRatHouseholder w x) = x
    have hneg := map_neg (ternaryRatHouseholderLinear w)
      (ternaryRatHouseholder w x)
    change ternaryRatHouseholder w (-ternaryRatHouseholder w x) =
      -ternaryRatHouseholder w (ternaryRatHouseholder w x) at hneg
    rw [hneg, ternaryRatHouseholder_involutive w x hw]
    simp
  not_identity := by
    obtain ⟨x, hx, horthogonal⟩ := exists_nonzero_ternaryRatPoint_orthogonal w hw
    refine ⟨x, ?_⟩
    change -ternaryRatHouseholder w x ≠ x
    rw [ternaryRatHouseholder_fixed_of_orthogonal w x horthogonal]
    intro h
    exact hx (ternaryRatPoint_eq_zero_of_eq_neg x h.symm)
  not_neg_identity := ⟨w, by
    change -ternaryRatHouseholder w w ≠ -w
    rw [ternaryRatHouseholder_normal w hw]
    intro h
    apply hw
    apply ternaryRatPoint_eq_zero_of_eq_neg w
    simpa using h⟩

/-- A positive projective-root target constructs one fixed Householder map and
one partner function on the entire progression, not merely separate
shellwise bijections. -/
theorem ProjectiveRootTargetCertificate.nonempty_coherent_of_positive
    {p i j k R : ℕ} (root : ProjectiveRootTargetCertificate p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hpositive : (((root.e * (p : ℤ) : ℤ) : ZMod 3) = 1 ∧
      ∃ h : ℤ, 2 * root.lambda * R =
        root.w1 + root.w2 + root.w3 - 6 * root.u + p * h)) :
    Nonempty (CoherentThetaInvolution p i j k R) := by
  classical
  obtain ⟨hep, h, htarget⟩ := hpositive
  have had := hadmissible
  rcases had with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  have hpne : (p : ℤ) ≠ 0 := by omega
  let w : TernaryIntIndex := ((root.w1, root.w2), root.w3)
  have hw : w ≠ 0 := by
    intro hwzero
    have hnormzero : ternaryNorm w.1.1 w.1.2 w.2 = 0 := by
      rw [hwzero]
      simp [ternaryNorm]
    dsimp [w] at hnormzero
    rw [root.hroot] at hnormzero
    rcases root.he with he | he
    · rw [he] at hnormzero
      omega
    · rw [he] at hnormzero
      omega
  let M : TripleQuintBranchIndex → ℤ := fun x =>
    h + 2 * root.lambda * pointResidueQuotient p i j k R x +
      2 * projectiveLiftBranchCorrection
        (pointB1 x) (pointB2 x) (pointB3 x)
        root.a1 root.a2 root.a3 (pointN1 x) (pointN2 x) (pointN3 x)
  let PartnerSpec : TripleQuintBranchIndex → TripleQuintBranchIndex → Prop :=
    fun x y =>
      pointBranchWeight y = -pointBranchWeight x ∧
      ternaryDot (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        root.w1 root.w2 root.w3 = (p : ℤ) ^ 2 * M x ∧
      pointThetaVector p i j k y =
        ((shortRootReflectCoord root.c ((p : ℤ) * M x) root.w1
            (pointCoord1 p i x),
          shortRootReflectCoord root.c ((p : ℤ) * M x) root.w2
            (pointCoord2 p j x)),
          shortRootReflectCoord root.c ((p : ℤ) * M x) root.w3
            (pointCoord3 p k x))
  have hexists : ∀ x, OnThetaProgression p i j k R x →
      ∃ y, PartnerSpec x y := by
    intro x hxprog
    have hxfiber := (onThetaProgression_iff_inThetaResidueFiber
      p i j k R x hi hpi hj hpj hk hpk hpodd hR).mp hxprog
    obtain ⟨q, hresidue⟩ := hxfiber
    have hxExists : ∃ qx : ℤ,
        pointLinearResidue i j k x = R + (p : ℤ) * qx := ⟨q, hresidue⟩
    have hxquot := pointLinearResidue_eq_add_mul_quotient
      p i j k R x hxExists
    have hqx : pointResidueQuotient p i j k R x = q := by
      apply mul_left_cancel₀ hpne
      calc
        (p : ℤ) * pointResidueQuotient p i j k R x =
            pointLinearResidue i j k x - R := by linarith [hxquot]
        _ = (p : ℤ) * q := by
          linear_combination hresidue
    have hpair := projectiveRoot_positive_target_pairing
      (pointB1 x) (pointB2 x) (pointB3 x)
      p root.lambda i j k root.w1 root.w2 root.w3
      root.a1 root.a2 root.a3 root.u
      (pointN1 x) (pointN2 x) (pointN3 x) R q h
      root.hw1 root.hw2 root.hw3 root.hvw
      (by simpa [pointLinearResidue] using hresidue) htarget
    have hpairM : ternaryDot
        (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        root.w1 root.w2 root.w3 = (p : ℤ) ^ 2 * M x := by
      simpa [pointCoord1, pointCoord2, pointCoord3, M, hqx] using hpair
    obtain ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
        hcoord1, hcoord2, hcoord3, hexponent, hreturn1, hreturn2, hreturn3⟩ :=
      shortRoot_positive_eight_branch_matching
        (pointB1 x) (pointB2 x) (pointB3 x)
        p root.e root.c i j k root.w1 root.w2 root.w3 (M x)
        (pointN1 x) (pointN2 x) (pointN3 x) hpodd root.he hep
        root.hroot root.hcoefficient hpairM
    let y : TripleQuintBranchIndex :=
      (((b1', pointN1 x + z1), (b2', pointN2 x + z2)),
        (b3', pointN3 x + z3))
    refine ⟨y, ?_, hpairM, ?_⟩
    · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
      rw [hproduct]
      simp [pointB1, pointB2, pointB3]
    · apply Prod.ext
      · apply Prod.ext
        · simpa [pointThetaVector, pointCoord1, y, pointB1, pointN1] using hcoord1
        · simpa [pointThetaVector, pointCoord2, y, pointB2, pointN2] using hcoord2
      · simpa [pointThetaVector, pointCoord3, y, pointB3, pointN3] using hcoord3
  let partner : TripleQuintBranchIndex → TripleQuintBranchIndex := fun x =>
    if hx : OnThetaProgression p i j k R x then
      Classical.choose (hexists x hx)
    else x
  have partner_spec : ∀ x, OnThetaProgression p i j k R x →
      PartnerSpec x (partner x) := by
    intro x hx
    dsimp [partner]
    simp only [dif_pos hx]
    exact Classical.choose_spec (hexists x hx)
  let geo := rationalTernaryHouseholderInvolution
    (ternaryIntIndexToRat w) (by
      intro hzero
      apply hw
      apply ternaryIntIndexToRat_injective
      simpa using hzero)
  exact ⟨{
    toRationalTernaryOrthogonalInvolution := geo
    partner := partner
    weight_reverse := fun x hx => (partner_spec x hx).1
    coordinate_transport := by
      intro x hx
      have hs := partner_spec x hx
      have hhouse := ternaryRatHouseholder_int_eq_shortRootReflect
        p root.e root.c ((p : ℤ) * M x) w
        (pointThetaVector p i j k x) hpne root.hroot
        (by
          calc
            ternaryDot (pointThetaVector p i j k x).1.1
                (pointThetaVector p i j k x).1.2
                (pointThetaVector p i j k x).2 w.1.1 w.1.2 w.2 =
              (p : ℤ) ^ 2 * M x := by
                simpa [pointThetaVector, w] using hs.2.1
            _ = (p : ℤ) * ((p : ℤ) * M x) := by ring)
        root.hcoefficient
      change ternaryRatHouseholder (ternaryIntIndexToRat w)
          (pointThetaVectorRat p i j k x) =
        pointThetaVectorRat p i j k (partner x)
      rw [show pointThetaVectorRat p i j k x =
          ternaryIntIndexToRat (pointThetaVector p i j k x) by rfl,
        hhouse]
      apply congrArg ternaryIntIndexToRat
      simpa [w] using hs.2.2.symm }⟩

/-- A negative projective-root target likewise constructs one fixed negative
Householder map and a progression-wide coherent partner. -/
theorem ProjectiveRootTargetCertificate.nonempty_coherent_of_negative
    {p i j k R : ℕ} (root : ProjectiveRootTargetCertificate p i j k R)
    (hadmissible : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hnegative : (((root.e * (p : ℤ) : ℤ) : ZMod 3) = 2 ∧
      ∃ base h : ℤ,
        base = 2 * root.lambda * R -
          (root.w1 + root.w2 + root.w3) + 6 * root.u ∧
        root.c * root.lambda * base = 12 + p * h)) :
    Nonempty (CoherentThetaInvolution p i j k R) := by
  classical
  obtain ⟨hep, base, h, hbase, htarget⟩ := hnegative
  have had := hadmissible
  rcases had with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  have hpne : (p : ℤ) ≠ 0 := by omega
  let w : TernaryIntIndex := ((root.w1, root.w2), root.w3)
  have hw : w ≠ 0 := by
    intro hwzero
    have hnormzero : ternaryNorm w.1.1 w.1.2 w.2 = 0 := by
      rw [hwzero]
      simp [ternaryNorm]
    dsimp [w] at hnormzero
    rw [root.hroot] at hnormzero
    rcases root.he with he | he
    · rw [he] at hnormzero
      omega
    · rw [he] at hnormzero
      omega
  let M : TripleQuintBranchIndex → ℤ := fun x =>
    2 * root.lambda * pointResidueQuotient p i j k R x +
      2 * projectiveLiftBranchCorrection
        (pointB1 x) (pointB2 x) (pointB3 x)
        root.a1 root.a2 root.a3 (pointN1 x) (pointN2 x) (pointN3 x)
  obtain ⟨hoffset1, hoffset2, hoffset3⟩ :=
    projectiveRoot_negative_coordinate_offsets
      p root.c root.lambda base i j k root.w1 root.w2 root.w3
      root.a1 root.a2 root.a3 h root.hw1 root.hw2 root.hw3 htarget
  let PartnerSpec : TripleQuintBranchIndex → TripleQuintBranchIndex → Prop :=
    fun x y =>
      pointBranchWeight y = -pointBranchWeight x ∧
      ternaryDot (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        root.w1 root.w2 root.w3 = (p : ℤ) * (base + (p : ℤ) * M x) ∧
      pointThetaVector p i j k y =
        (-((shortRootReflectCoord root.c (base + (p : ℤ) * M x) root.w1
            (pointCoord1 p i x),
          shortRootReflectCoord root.c (base + (p : ℤ) * M x) root.w2
            (pointCoord2 p j x)),
          shortRootReflectCoord root.c (base + (p : ℤ) * M x) root.w3
            (pointCoord3 p k x)))
  have hexists : ∀ x, OnThetaProgression p i j k R x →
      ∃ y, PartnerSpec x y := by
    intro x hxprog
    have hxfiber := (onThetaProgression_iff_inThetaResidueFiber
      p i j k R x hi hpi hj hpj hk hpk hpodd hR).mp hxprog
    obtain ⟨q, hresidue⟩ := hxfiber
    have hxExists : ∃ qx : ℤ,
        pointLinearResidue i j k x = R + (p : ℤ) * qx := ⟨q, hresidue⟩
    have hxquot := pointLinearResidue_eq_add_mul_quotient
      p i j k R x hxExists
    have hqx : pointResidueQuotient p i j k R x = q := by
      apply mul_left_cancel₀ hpne
      calc
        (p : ℤ) * pointResidueQuotient p i j k R x =
            pointLinearResidue i j k x - R := by linarith [hxquot]
        _ = (p : ℤ) * q := by
          linear_combination hresidue
    have hpair := projectiveRoot_reflection_quotient
      (pointB1 x) (pointB2 x) (pointB3 x)
      p root.lambda i j k root.w1 root.w2 root.w3
      root.a1 root.a2 root.a3 root.u
      (pointN1 x) (pointN2 x) (pointN3 x) R q
      root.hw1 root.hw2 root.hw3 root.hvw
      (by simpa [pointLinearResidue] using hresidue)
    rw [← hbase] at hpair
    have hpairM : ternaryDot
        (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)
        root.w1 root.w2 root.w3 = (p : ℤ) * (base + (p : ℤ) * M x) := by
      simpa [pointCoord1, pointCoord2, pointCoord3, M, hqx] using hpair
    obtain ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
        hcoord1, hcoord2, hcoord3, hexponent, hreturn1, hreturn2, hreturn3⟩ :=
      shortRoot_negative_eight_branch_matching
        (pointB1 x) (pointB2 x) (pointB3 x)
        p root.e root.c i j k root.w1 root.w2 root.w3 base (M x)
        (h * i + root.c * base * root.a1)
        (h * j + root.c * base * root.a2)
        (h * k + root.c * base * root.a3)
        (pointN1 x) (pointN2 x) (pointN3 x) hpodd root.he hep
        root.hroot root.hcoefficient hpairM hoffset1 hoffset2 hoffset3
    let y : TripleQuintBranchIndex :=
      (((b1', -pointN1 x + z1), (b2', -pointN2 x + z2)),
        (b3', -pointN3 x + z3))
    refine ⟨y, ?_, hpairM, ?_⟩
    · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
      rw [hproduct]
      simp [pointB1, pointB2, pointB3]
    · apply Prod.ext
      · apply Prod.ext
        · simpa [pointThetaVector, pointCoord1, y, pointB1, pointN1] using hcoord1
        · simpa [pointThetaVector, pointCoord2, y, pointB2, pointN2] using hcoord2
      · simpa [pointThetaVector, pointCoord3, y, pointB3, pointN3] using hcoord3
  let partner : TripleQuintBranchIndex → TripleQuintBranchIndex := fun x =>
    if hx : OnThetaProgression p i j k R x then
      Classical.choose (hexists x hx)
    else x
  have partner_spec : ∀ x, OnThetaProgression p i j k R x →
      PartnerSpec x (partner x) := by
    intro x hx
    dsimp [partner]
    simp only [dif_pos hx]
    exact Classical.choose_spec (hexists x hx)
  let geo := rationalTernaryNegHouseholderInvolution
    (ternaryIntIndexToRat w) (by
      intro hzero
      apply hw
      apply ternaryIntIndexToRat_injective
      simpa using hzero)
  exact ⟨{
    toRationalTernaryOrthogonalInvolution := geo
    partner := partner
    weight_reverse := fun x hx => (partner_spec x hx).1
    coordinate_transport := by
      intro x hx
      have hs := partner_spec x hx
      have hhouse := ternaryRatHouseholder_int_eq_shortRootReflect
        p root.e root.c (base + (p : ℤ) * M x) w
        (pointThetaVector p i j k x) hpne root.hroot
        (by simpa [pointThetaVector, w] using hs.2.1)
        root.hcoefficient
      change -ternaryRatHouseholder (ternaryIntIndexToRat w)
          (pointThetaVectorRat p i j k x) =
        pointThetaVectorRat p i j k (partner x)
      rw [show pointThetaVectorRat p i j k x =
          ternaryIntIndexToRat (pointThetaVector p i j k x) by rfl,
        hhouse]
      have hv := congrArg ternaryIntIndexToRat hs.2.2.symm
      simp [w, ternaryIntIndexToRat] at hv ⊢
      apply Prod.ext
      · apply Prod.ext
        · exact hv.1.1
        · exact hv.1.2
      · exact hv.2 }⟩

/-- **Exact coherent/root equivalence.**  On admissible data, complete
projective-root targets and progression-wide coherent orthogonal involutions
are the same structure, in both directions. -/
theorem hasProjectiveRootTarget_iff_nonempty_coherentThetaInvolution
    (p i j k R : ℕ) (hadmissible : AdmissibleSparseTriple p i j k)
    (hR : R < p) :
    HasProjectiveRootTarget p i j k R ↔
      Nonempty (CoherentThetaInvolution p i j k R) := by
  constructor
  · rintro ⟨root⟩
    rcases root.hcase with hpositive | hnegative
    · exact root.nonempty_coherent_of_positive hadmissible hR hpositive
    · exact root.nonempty_coherent_of_negative hadmissible hR hnegative
  · rintro ⟨T⟩
    exact T.hasProjectiveRootTarget hadmissible hR

/-- **Exact spectral-frontier identification.**  Once the explicit converse
geometry is available, asking every persistent signed theta identity to arise
from one coherent involution is exactly the theta-coset rigidity proposition.
There is no residual arithmetic hypothesis in either direction. -/
theorem admissibleThetaGeometricCoherence_iff_thetaCosetRigidity
    (p i j k R : ℕ) :
    AdmissibleThetaGeometricCoherence p i j k R ↔
      AdmissibleThetaCosetRigidity p i j k R := by
  constructor
  · exact admissibleThetaCosetRigidity_of_geometricCoherence p i j k R
  · intro hrigidity hadmissible hR htheta
    exact (hasProjectiveRootTarget_iff_nonempty_coherentThetaInvolution
      p i j k R hadmissible hR).mp
        (hrigidity hadmissible hR htheta)

/-- **Final one-conjecture normal form.**  Spectral coherence is logically
equivalent to the corrected admissible Root--Vanishing rigidity conjecture.
Thus proving either statement proves the other, rather than merely providing
a sufficient route to it. -/
theorem admissibleThetaGeometricCoherence_iff_rootVanishingRigidity
    (p i j k R : ℕ) :
    AdmissibleThetaGeometricCoherence p i j k R ↔
      AdmissibleRootVanishingRigidity p i j k R := by
  rw [admissibleThetaGeometricCoherence_iff_thetaCosetRigidity,
    admissibleThetaCosetRigidity_iff_rootVanishingRigidity]

end Ramanujan.MultiQuintuple
