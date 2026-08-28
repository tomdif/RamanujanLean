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

/-- **Primitive arithmetic extraction from coherence.**  Every coherent theta
involution has a primitive integral Householder normal, its linear part is the
corresponding reflection or negative reflection, and the squared norm of that
normal is forced into the sharp denominator list `1, 2, p, 2p`.

The first two cases are precisely the integral signed-coordinate/permutation
reflections.  Excluding their stabilizers is a separate modular rigidity step;
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

end Ramanujan.MultiQuintuple
