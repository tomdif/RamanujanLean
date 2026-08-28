/-
# The geometric coherence bridge for eight-coset theta vanishings

The signed theta identity reduces persistent triple-quintuple vanishing to a
spectral equality among eight shifted ternary cosets.  A shell-by-shell
bijection is too weak: arbitrary bijections can be chosen independently and
then glued.  The genuinely geometric object is one fixed rational orthogonal
linear involution acting on the completed-square coordinates on every shell.

This file defines that object, proves that it produces persistent vanishing,
and factors the reverse Root--Vanishing theorem through two explicit
interfaces:

1. spectral equality forces a coherent rational orthogonal involution;
2. every such admissible involution is one of the projective short-root maps.

No unproved claim is assumed.  `MultiQuintupleThetaArithmetic` discharges the
second interface; the first is the exact theorem to which ternary
lattice-coset theta rigidity must be applied.
-/
import RamanujanTau.MultiQuintupleThetaCosets

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- Rational ambient space for the completed ternary coordinates. -/
abbrev TernaryRatPoint := (ℚ × ℚ) × ℚ

/-- Cast an integral ternary point into the rational quadratic space. -/
def ternaryIntPointToRat (x : TernaryIntPoint) : TernaryRatPoint :=
  (((x.1.1 : ℚ), (x.1.2 : ℚ)), (x.2 : ℚ))

/-- The rational Euclidean ternary norm. -/
def ternaryRatNorm (x : TernaryRatPoint) : ℚ :=
  x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2

/-- Rational Euclidean dot product. -/
def ternaryRatDot (x y : TernaryRatPoint) : ℚ :=
  x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2

lemma ternaryRatNorm_add (x y : TernaryRatPoint) :
    ternaryRatNorm (x + y) =
      ternaryRatNorm x + 2 * ternaryRatDot x y + ternaryRatNorm y := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  simp [ternaryRatNorm, ternaryRatDot]
  ring

lemma ternaryRatDot_self (x : TernaryRatPoint) :
    ternaryRatDot x x = ternaryRatNorm x := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  simp [ternaryRatDot, ternaryRatNorm, pow_two]

lemma ternaryRatDot_smul_left (c : ℚ) (x y : TernaryRatPoint) :
    ternaryRatDot (c • x) y = c * ternaryRatDot x y := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  simp [ternaryRatDot]
  ring

lemma ternaryRatDot_add_left (x y z : TernaryRatPoint) :
    ternaryRatDot (x + y) z = ternaryRatDot x z + ternaryRatDot y z := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  rcases z with ⟨⟨z1, z2⟩, z3⟩
  simp [ternaryRatDot]
  ring

lemma ternaryRatDot_sub_left (x y z : TernaryRatPoint) :
    ternaryRatDot (x - y) z = ternaryRatDot x z - ternaryRatDot y z := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  rcases z with ⟨⟨z1, z2⟩, z3⟩
  simp [ternaryRatDot]
  ring

lemma ternaryRatDot_neg_right (x y : TernaryRatPoint) :
    ternaryRatDot x (-y) = -ternaryRatDot x y := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  rcases y with ⟨⟨y1, y2⟩, y3⟩
  simp [ternaryRatDot]
  ring

lemma ternaryRatNorm_pos {x : TernaryRatPoint} (hx : x ≠ 0) :
    0 < ternaryRatNorm x := by
  rcases x with ⟨⟨x1, x2⟩, x3⟩
  have hcoord : x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    simp [h.1, h.2.1, h.2.2]
  simp only [ternaryRatNorm]
  rcases hcoord with h1 | h2 | h3
  · nlinarith [mul_self_pos.mpr h1, sq_nonneg x2, sq_nonneg x3]
  · nlinarith [mul_self_pos.mpr h2, sq_nonneg x1, sq_nonneg x3]
  · nlinarith [mul_self_pos.mpr h3, sq_nonneg x1, sq_nonneg x2]

/-- The rational Householder reflection with normal `w`. -/
def ternaryRatHouseholder (w x : TernaryRatPoint) : TernaryRatPoint :=
  x - (2 * ternaryRatDot x w / ternaryRatNorm w) • w

/-- Completed coordinates of a branch point in the rational ambient space. -/
def pointThetaVectorRat (p i j k : ℕ)
    (x : TripleQuintBranchIndex) : TernaryRatPoint :=
  ternaryIntPointToRat (pointThetaVector p i j k x)

lemma ternaryIntPointToRat_injective :
    Function.Injective ternaryIntPointToRat := by
  rintro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ h
  simp only [ternaryIntPointToRat, Prod.mk.injEq] at h ⊢
  constructor
  · constructor
    · exact_mod_cast h.1.1
    · exact_mod_cast h.1.2
  · exact_mod_cast h.2

lemma ternaryRatNorm_intPointToRat (x : TernaryIntPoint) :
    ternaryRatNorm (ternaryIntPointToRat x) =
      (ternaryNorm x.1.1 x.1.2 x.2 : ℚ) := by
  simp [ternaryRatNorm, ternaryIntPointToRat, ternaryNorm]

lemma ternaryRatNorm_pointThetaVectorRat
    (p i j k : ℕ) (x : TripleQuintBranchIndex) :
    ternaryRatNorm (pointThetaVectorRat p i j k x) =
      (pointThetaNorm p i j k x : ℚ) := by
  simp [pointThetaVectorRat, ternaryRatNorm_intPointToRat,
    pointThetaVector, pointThetaNorm, ternaryNorm]

/-- The completed-coordinate map is injective when the modulus is nonzero. -/
lemma pointThetaVector_injective
    (p i j k : ℕ) (hp : 0 < p) :
    Function.Injective (pointThetaVector p i j k) := by
  intro x y h
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  apply Prod.ext
  · apply Prod.ext
    · apply quintBranchIndex_eq_of_coord_eq p i hpz
      exact congrArg (fun z : TernaryIntPoint => z.1.1) h
    · apply quintBranchIndex_eq_of_coord_eq p j hpz
      exact congrArg (fun z : TernaryIntPoint => z.1.2) h
  · apply quintBranchIndex_eq_of_coord_eq p k hpz
    exact congrArg (fun z : TernaryIntPoint => z.2) h

lemma pointThetaVectorRat_injective
    (p i j k : ℕ) (hp : 0 < p) :
    Function.Injective (pointThetaVectorRat p i j k) := by
  intro x y h
  apply pointThetaVector_injective p i j k hp
  apply ternaryIntPointToRat_injective
  exact h

/-- A branch point lies on one of the exponent shells in the progression
`p*N+R`. -/
def OnThetaProgression
    (p i j k R : ℕ) (x : TripleQuintBranchIndex) : Prop :=
  ∃ N : ℕ,
    pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ)

/-- The affine index-`p` residue fiber underlying the coefficient
progression. -/
def InThetaResidueFiber
    (p i j k R : ℕ) (x : TripleQuintBranchIndex) : Prop :=
  ∃ q : ℤ, pointLinearResidue i j k x = R + (p : ℤ) * q

/-- **Progression shells fill the complete affine residue fiber.**

The forward implication was used by the root construction.  The converse is
equally important for rigidity: canonical nonnegativity and `R < p` show that
every integral branch point in the residue fiber occurs on a unique
nonnegative coefficient shell in the progression. -/
theorem onThetaProgression_iff_inThetaResidueFiber
    (p i j k R : ℕ) (x : TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (hR : R < p) :
    OnThetaProgression p i j k R x ↔ InThetaResidueFiber p i j k R x := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨q, hq⟩ := tripleLinearResidue_eq_progression
      (pointB1 x) (pointB2 x) (pointB3 x) p i j k N R
      (pointN1 x) (pointN2 x) (pointN3 x) hpodd (by
        simpa [pointTripleExp2] using hN)
    exact ⟨q, by simpa [pointLinearResidue] using hq⟩
  · rintro ⟨q, hq⟩
    obtain ⟨u, hu⟩ := tripleQuintExp2_eq_two_residue_add_p_mul
      (pointB1 x) (pointB2 x) (pointB3 x) p i j k
      (pointN1 x) (pointN2 x) (pointN3 x)
    have heven : Even (pointTripleExp2 p i j k x) := by
      change Even (quintExp2 (pointB1 x) p i (pointN1 x) +
        quintExp2 (pointB2 x) p j (pointN2 x) +
        quintExp2 (pointB3 x) p k (pointN3 x))
      exact ((quintExp2_even (pointB1 x) p i (pointN1 x)).add
        (quintExp2_even (pointB2 x) p j (pointN2 x))).add
          (quintExp2_even (pointB3 x) p k (pointN3 x))
    obtain ⟨t, ht⟩ := heven
    obtain ⟨a, ha⟩ := hpodd
    have hueven : Even u := by
      refine ⟨t - pointLinearResidue i j k x - a * u, ?_⟩
      have hu' : pointTripleExp2 p i j k x =
          2 * pointLinearResidue i j k x + (p : ℤ) * u := by
        simpa [pointTripleExp2, pointLinearResidue] using hu
      linear_combination ht - hu' - u * ha
    obtain ⟨v, hv⟩ := hueven
    have hexp : pointTripleExp2 p i j k x =
        2 * ((p : ℤ) * (q + v) + R) := by
      have hu' : pointTripleExp2 p i j k x =
          2 * pointLinearResidue i j k x + (p : ℤ) * u := by
        simpa [pointTripleExp2, pointLinearResidue] using hu
      rw [hq, hv] at hu'
      linear_combination hu'
    have hnonneg1 := quintExp2_nonneg (pointB1 x) p i (pointN1 x) hi hpi
    have hnonneg2 := quintExp2_nonneg (pointB2 x) p j (pointN2 x) hj hpj
    have hnonneg3 := quintExp2_nonneg (pointB3 x) p k (pointN3 x) hk hpk
    have htargetNonneg : 0 ≤ (p : ℤ) * (q + v) + R := by
      have htotal : 0 ≤ pointTripleExp2 p i j k x := by
        dsimp [pointTripleExp2, tripleQuintExp2]
        omega
      omega
    have hqv : 0 ≤ q + v := by
      by_contra hnegative
      have hle : q + v ≤ -1 := by omega
      have hpnonneg : (0 : ℤ) ≤ p := by positivity
      have hmul : (p : ℤ) * (q + v) ≤ (p : ℤ) * (-1) :=
        Int.mul_le_mul_of_nonneg_left hle hpnonneg
      have hRz : (R : ℤ) < p := by exact_mod_cast hR
      omega
    refine ⟨(q + v).toNat, ?_⟩
    push_cast
    rw [Int.toNat_of_nonneg hqv]
    exact hexp

/-- One fixed rational orthogonal linear involution of ternary space. -/
structure RationalTernaryOrthogonalInvolution where
  linear : TernaryRatPoint →ₗ[ℚ] TernaryRatPoint
  norm_preserving : ∀ y, ternaryRatNorm (linear y) = ternaryRatNorm y
  involutive : ∀ y, linear (linear y) = y
  not_identity : ∃ y, linear y ≠ y
  not_neg_identity : ∃ y, linear y ≠ -y

/-- Norm preservation plus linearity gives preservation of the full polar
bilinear form. -/
lemma RationalTernaryOrthogonalInvolution.dot_preserving
    (T : RationalTernaryOrthogonalInvolution) (x y : TernaryRatPoint) :
    ternaryRatDot (T.linear x) (T.linear y) = ternaryRatDot x y := by
  have hsum := T.norm_preserving (x + y)
  have hx := T.norm_preserving x
  have hy := T.norm_preserving y
  rw [map_add, ternaryRatNorm_add, ternaryRatNorm_add, hx, hy] at hsum
  linarith

/-- Fixed and anti-fixed vector predicates for the involution. -/
def IsThetaFixed (T : RationalTernaryOrthogonalInvolution)
    (x : TernaryRatPoint) : Prop := T.linear x = x

def IsThetaAntiFixed (T : RationalTernaryOrthogonalInvolution)
    (x : TernaryRatPoint) : Prop := T.linear x = -x

/-- The noncentrality hypotheses produce a nonzero anti-fixed direction. -/
lemma RationalTernaryOrthogonalInvolution.exists_nonzero_antiFixed
    (T : RationalTernaryOrthogonalInvolution) :
    ∃ w : TernaryRatPoint, w ≠ 0 ∧ IsThetaAntiFixed T w := by
  obtain ⟨y, hy⟩ := T.not_identity
  refine ⟨y - T.linear y, sub_ne_zero.mpr hy.symm, ?_⟩
  dsimp [IsThetaAntiFixed]
  rw [map_sub, T.involutive]
  module

/-- The noncentrality hypotheses also produce a nonzero fixed direction. -/
lemma RationalTernaryOrthogonalInvolution.exists_nonzero_fixed
    (T : RationalTernaryOrthogonalInvolution) :
    ∃ v : TernaryRatPoint, v ≠ 0 ∧ IsThetaFixed T v := by
  obtain ⟨y, hy⟩ := T.not_neg_identity
  have hnonzero : y + T.linear y ≠ 0 := by
    intro hzero
    exact hy (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hzero))
  refine ⟨y + T.linear y, hnonzero, ?_⟩
  dsimp [IsThetaFixed]
  rw [map_add, T.involutive]
  ac_rfl

/-- Fixed and anti-fixed directions are orthogonal. -/
lemma RationalTernaryOrthogonalInvolution.fixed_dot_antiFixed_eq_zero
    (T : RationalTernaryOrthogonalInvolution) (v w : TernaryRatPoint)
    (hv : IsThetaFixed T v) (hw : IsThetaAntiFixed T w) :
    ternaryRatDot v w = 0 := by
  have hdot := T.dot_preserving v w
  rw [hv, hw] at hdot
  have hneg : ternaryRatDot v (-w) = -ternaryRatDot v w := by
    rcases v with ⟨⟨v1, v2⟩, v3⟩
    rcases w with ⟨⟨w1, w2⟩, w3⟩
    simp [ternaryRatDot]
    ring
  rw [hneg] at hdot
  linarith

/-- Canonical projection to the fixed eigenspace. -/
def thetaFixedPart (T : RationalTernaryOrthogonalInvolution)
    (x : TernaryRatPoint) : TernaryRatPoint :=
  (1 / 2 : ℚ) • (x + T.linear x)

/-- Canonical projection to the anti-fixed eigenspace. -/
def thetaAntiFixedPart (T : RationalTernaryOrthogonalInvolution)
    (x : TernaryRatPoint) : TernaryRatPoint :=
  (1 / 2 : ℚ) • (x - T.linear x)

lemma RationalTernaryOrthogonalInvolution.fixedPart_isFixed
    (T : RationalTernaryOrthogonalInvolution) (x : TernaryRatPoint) :
    IsThetaFixed T (thetaFixedPart T x) := by
  simp [IsThetaFixed, thetaFixedPart, map_add, T.involutive,
    add_comm]

lemma RationalTernaryOrthogonalInvolution.antiFixedPart_isAntiFixed
    (T : RationalTernaryOrthogonalInvolution) (x : TernaryRatPoint) :
    IsThetaAntiFixed T (thetaAntiFixedPart T x) := by
  simp [IsThetaAntiFixed, thetaAntiFixedPart, map_sub, T.involutive]
  module

/-- Every rational ternary vector splits canonically as fixed plus
anti-fixed.  The remaining geometric classification is therefore the
rank-three dichotomy `(dim fixed, dim anti) = (2,1)` or `(1,2)`. -/
lemma RationalTernaryOrthogonalInvolution.fixedPart_add_antiFixedPart
    (T : RationalTernaryOrthogonalInvolution) (x : TernaryRatPoint) :
    thetaFixedPart T x + thetaAntiFixedPart T x = x := by
  simp [thetaFixedPart, thetaAntiFixedPart]
  module

/-- The `+1` eigenspace. -/
def thetaFixedSubspace (T : RationalTernaryOrthogonalInvolution) :
    Submodule ℚ TernaryRatPoint where
  carrier := {x | IsThetaFixed T x}
  zero_mem' := by simp [IsThetaFixed]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, IsThetaFixed] at hx hy ⊢
    rw [map_add, hx, hy]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, IsThetaFixed] at hx ⊢
    rw [map_smul, hx]

/-- The `-1` eigenspace. -/
def thetaAntiFixedSubspace (T : RationalTernaryOrthogonalInvolution) :
    Submodule ℚ TernaryRatPoint where
  carrier := {x | IsThetaAntiFixed T x}
  zero_mem' := by simp [IsThetaAntiFixed]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, IsThetaAntiFixed] at hx hy ⊢
    rw [map_add, hx, hy]
    module
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, IsThetaAntiFixed] at hx ⊢
    rw [map_smul, hx]
    module

@[simp] lemma mem_thetaFixedSubspace_iff
    (T : RationalTernaryOrthogonalInvolution) (x : TernaryRatPoint) :
    x ∈ thetaFixedSubspace T ↔ IsThetaFixed T x := Iff.rfl

@[simp] lemma mem_thetaAntiFixedSubspace_iff
    (T : RationalTernaryOrthogonalInvolution) (x : TernaryRatPoint) :
    x ∈ thetaAntiFixedSubspace T ↔ IsThetaAntiFixed T x := Iff.rfl

/-- The two eigenspaces intersect trivially. -/
lemma thetaFixedSubspace_disjoint_thetaAntiFixedSubspace
    (T : RationalTernaryOrthogonalInvolution) :
    Disjoint (thetaFixedSubspace T) (thetaAntiFixedSubspace T) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have hfixed : T.linear x = x := hx
  have hanti : T.linear x = -x := hy
  have hneg : x = -x := hfixed.symm.trans hanti
  apply Prod.ext
  · apply Prod.ext
    · have h := congrArg (fun z : TernaryRatPoint => z.1.1) hneg
      dsimp at h ⊢
      linarith
    · have h := congrArg (fun z : TernaryRatPoint => z.1.2) hneg
      dsimp at h ⊢
      linarith
  · have h := congrArg (fun z : TernaryRatPoint => z.2) hneg
    dsimp at h ⊢
    linarith

/-- The fixed and anti-fixed eigenspaces span all rational ternary space. -/
lemma thetaFixedSubspace_sup_thetaAntiFixedSubspace
    (T : RationalTernaryOrthogonalInvolution) :
    thetaFixedSubspace T ⊔ thetaAntiFixedSubspace T = ⊤ := by
  apply top_unique
  intro x hx
  rw [← T.fixedPart_add_antiFixedPart x]
  apply Submodule.add_mem
  · exact (show thetaFixedSubspace T ≤
      thetaFixedSubspace T ⊔ thetaAntiFixedSubspace T from le_sup_left)
        (T.fixedPart_isFixed x)
  · exact (show thetaAntiFixedSubspace T ≤
      thetaFixedSubspace T ⊔ thetaAntiFixedSubspace T from le_sup_right)
        (T.antiFixedPart_isAntiFixed x)

/-- **Three-dimensional involution dichotomy.**  A noncentral rational
orthogonal involution has eigenspace dimensions `(2,1)` or `(1,2)`.  These are
respectively the Householder and negative-Householder cases. -/
theorem RationalTernaryOrthogonalInvolution.finrank_fixed_antiFixed_dichotomy
    (T : RationalTernaryOrthogonalInvolution) :
    (Module.finrank ℚ (thetaFixedSubspace T) = 2 ∧
        Module.finrank ℚ (thetaAntiFixedSubspace T) = 1) ∨
      (Module.finrank ℚ (thetaFixedSubspace T) = 1 ∧
        Module.finrank ℚ (thetaAntiFixedSubspace T) = 2) := by
  have hfixed_ne : thetaFixedSubspace T ≠ ⊥ := by
    rintro hbot
    obtain ⟨v, hvne, hv⟩ := T.exists_nonzero_fixed
    have hmem : v ∈ thetaFixedSubspace T := hv
    rw [hbot] at hmem
    exact hvne (by simpa using hmem)
  have hanti_ne : thetaAntiFixedSubspace T ≠ ⊥ := by
    rintro hbot
    obtain ⟨w, hwne, hw⟩ := T.exists_nonzero_antiFixed
    have hmem : w ∈ thetaAntiFixedSubspace T := hw
    rw [hbot] at hmem
    exact hwne (by simpa using hmem)
  have hfixed_pos : 1 ≤ Module.finrank ℚ (thetaFixedSubspace T) :=
    Submodule.one_le_finrank_iff.mpr hfixed_ne
  have hanti_pos : 1 ≤ Module.finrank ℚ (thetaAntiFixedSubspace T) :=
    Submodule.one_le_finrank_iff.mpr hanti_ne
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (thetaFixedSubspace T) (thetaAntiFixedSubspace T)
  rw [thetaFixedSubspace_sup_thetaAntiFixedSubspace,
    (thetaFixedSubspace_disjoint_thetaAntiFixedSubspace T).eq_bot] at hdim
  have hambient : Module.finrank ℚ TernaryRatPoint = 3 := by
    simp [TernaryRatPoint, Module.finrank_prod]
  simp only [finrank_top, finrank_bot, add_zero] at hdim
  rw [hambient] at hdim
  omega

/-- If the anti-fixed eigenspace is one-dimensional, the involution is exactly
the Householder reflection in any nonzero anti-fixed normal. -/
theorem RationalTernaryOrthogonalInvolution.eq_householder_of_antiFixed_finrank_one
    (T : RationalTernaryOrthogonalInvolution)
    (hdim : Module.finrank ℚ (thetaAntiFixedSubspace T) = 1) :
    ∃ w : TernaryRatPoint, w ≠ 0 ∧ IsThetaAntiFixed T w ∧
      ∀ x, T.linear x = ternaryRatHouseholder w x := by
  obtain ⟨w, hwne, hwanti⟩ := T.exists_nonzero_antiFixed
  let ws : thetaAntiFixedSubspace T := ⟨w, hwanti⟩
  have hwsne : ws ≠ 0 := by
    intro hzero
    apply hwne
    exact congrArg Subtype.val hzero
  have hspan := (finrank_eq_one_iff_of_nonzero' ws hwsne).mp hdim
  refine ⟨w, hwne, hwanti, ?_⟩
  intro x
  let d : TernaryRatPoint := x - T.linear x
  have hdanti : IsThetaAntiFixed T d := by
    dsimp [d, IsThetaAntiFixed]
    rw [map_sub, T.involutive]
    module
  obtain ⟨c, hc⟩ := hspan ⟨d, hdanti⟩
  have hcval : c • w = d := congrArg Subtype.val hc
  have hTdot : ternaryRatDot (T.linear x) w = -ternaryRatDot x w := by
    have hpres := T.dot_preserving x w
    rw [hwanti, ternaryRatDot_neg_right] at hpres
    linarith
  have hdotd : ternaryRatDot d w = 2 * ternaryRatDot x w := by
    dsimp [d]
    rw [ternaryRatDot_sub_left, hTdot]
    ring
  have hcdot := congrArg (fun z : TernaryRatPoint => ternaryRatDot z w) hcval
  change ternaryRatDot (c • w) w = ternaryRatDot d w at hcdot
  rw [ternaryRatDot_smul_left, ternaryRatDot_self, hdotd] at hcdot
  have hnormne : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hwne)
  have hceq : c = 2 * ternaryRatDot x w / ternaryRatNorm w :=
    (eq_div_iff hnormne).mpr hcdot
  change T.linear x = x -
    (2 * ternaryRatDot x w / ternaryRatNorm w) • w
  rw [← hceq, hcval]
  dsimp [d]
  module

/-- If the fixed eigenspace is one-dimensional, the involution is the negative
of a Householder reflection with fixed normal. -/
theorem RationalTernaryOrthogonalInvolution.eq_neg_householder_of_fixed_finrank_one
    (T : RationalTernaryOrthogonalInvolution)
    (hdim : Module.finrank ℚ (thetaFixedSubspace T) = 1) :
    ∃ w : TernaryRatPoint, w ≠ 0 ∧ IsThetaFixed T w ∧
      ∀ x, T.linear x = -ternaryRatHouseholder w x := by
  obtain ⟨w, hwne, hwfixed⟩ := T.exists_nonzero_fixed
  let ws : thetaFixedSubspace T := ⟨w, hwfixed⟩
  have hwsne : ws ≠ 0 := by
    intro hzero
    apply hwne
    exact congrArg Subtype.val hzero
  have hspan := (finrank_eq_one_iff_of_nonzero' ws hwsne).mp hdim
  refine ⟨w, hwne, hwfixed, ?_⟩
  intro x
  let d : TernaryRatPoint := x + T.linear x
  have hdfixed : IsThetaFixed T d := by
    dsimp [d, IsThetaFixed]
    rw [map_add, T.involutive]
    ac_rfl
  obtain ⟨c, hc⟩ := hspan ⟨d, hdfixed⟩
  have hcval : c • w = d := congrArg Subtype.val hc
  have hTdot : ternaryRatDot (T.linear x) w = ternaryRatDot x w := by
    have hpres := T.dot_preserving x w
    rwa [hwfixed] at hpres
  have hdotd : ternaryRatDot d w = 2 * ternaryRatDot x w := by
    dsimp [d]
    rw [ternaryRatDot_add_left, hTdot]
    ring
  have hcdot := congrArg (fun z : TernaryRatPoint => ternaryRatDot z w) hcval
  change ternaryRatDot (c • w) w = ternaryRatDot d w at hcdot
  rw [ternaryRatDot_smul_left, ternaryRatDot_self, hdotd] at hcdot
  have hnormne : ternaryRatNorm w ≠ 0 := ne_of_gt (ternaryRatNorm_pos hwne)
  have hceq : c = 2 * ternaryRatDot x w / ternaryRatNorm w :=
    (eq_div_iff hnormne).mpr hcdot
  change T.linear x =
    -(x - (2 * ternaryRatDot x w / ternaryRatNorm w) • w)
  rw [← hceq, hcval]
  dsimp [d]
  module

/-- **Complete rational geometric classification.**  Every noncentral
orthogonal involution of ternary rational space is a Householder reflection or
the negative of one. -/
theorem RationalTernaryOrthogonalInvolution.exists_householder_or_neg_householder
    (T : RationalTernaryOrthogonalInvolution) :
    (∃ w : TernaryRatPoint, w ≠ 0 ∧ IsThetaAntiFixed T w ∧
      ∀ x, T.linear x = ternaryRatHouseholder w x) ∨
    (∃ w : TernaryRatPoint, w ≠ 0 ∧ IsThetaFixed T w ∧
      ∀ x, T.linear x = -ternaryRatHouseholder w x) := by
  rcases T.finrank_fixed_antiFixed_dichotomy with hpositive | hnegative
  · exact Or.inl (T.eq_householder_of_antiFixed_finrank_one hpositive.2)
  · exact Or.inr (T.eq_neg_householder_of_fixed_finrank_one hnegative.1)

/-- A single rational orthogonal involution coherently pairs every Watson
branch point in the requested progression.  In contrast with abstract
shellwise balance, the same linear map acts on every norm shell. -/
structure CoherentThetaInvolution (p i j k R : ℕ)
    extends RationalTernaryOrthogonalInvolution where
  partner : TripleQuintBranchIndex → TripleQuintBranchIndex
  weight_reverse : ∀ x, OnThetaProgression p i j k R x →
    pointBranchWeight (partner x) = -pointBranchWeight x
  coordinate_transport : ∀ x, OnThetaProgression p i j k R x →
    linear (pointThetaVectorRat p i j k x) =
      pointThetaVectorRat p i j k (partner x)

/-- The linear part of every coherent cancellation is already completely
classified over `ℚ`: it is a Householder reflection or its negative.  What
remains after this theorem is the arithmetic extraction of an integral
projective normal and the spectral proof that such a coherent map exists. -/
theorem CoherentThetaInvolution.exists_householder_or_neg_householder
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R) :
    (∃ w : TernaryRatPoint, w ≠ 0 ∧
      IsThetaAntiFixed T.toRationalTernaryOrthogonalInvolution w ∧
      ∀ x, T.linear x = ternaryRatHouseholder w x) ∨
    (∃ w : TernaryRatPoint, w ≠ 0 ∧
      IsThetaFixed T.toRationalTernaryOrthogonalInvolution w ∧
      ∀ x, T.linear x = -ternaryRatHouseholder w x) :=
  T.toRationalTernaryOrthogonalInvolution.exists_householder_or_neg_householder

/-- Coherent coordinate transport preserves the integral ternary norm. -/
lemma CoherentThetaInvolution.pointThetaNorm_partner
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (x : TripleQuintBranchIndex) (hx : OnThetaProgression p i j k R x) :
    pointThetaNorm p i j k (T.partner x) = pointThetaNorm p i j k x := by
  have hcoord := T.coordinate_transport x hx
  have hnorm := T.norm_preserving (pointThetaVectorRat p i j k x)
  rw [hcoord, ternaryRatNorm_pointThetaVectorRat,
    ternaryRatNorm_pointThetaVectorRat] at hnorm
  exact_mod_cast hnorm

/-- Hence the partner preserves the original doubled quintuple exponent. -/
lemma CoherentThetaInvolution.pointTripleExp2_partner
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hp : 0 < p) (x : TripleQuintBranchIndex)
    (hx : OnThetaProgression p i j k R x) :
    pointTripleExp2 p i j k (T.partner x) = pointTripleExp2 p i j k x := by
  have hnorm := T.pointThetaNorm_partner x hx
  rw [pointThetaNorm_eq_squareCompletion,
    pointThetaNorm_eq_squareCompletion] at hnorm
  have hmul :
      12 * (p : ℤ) * pointTripleExp2 p i j k (T.partner x) =
        12 * (p : ℤ) * pointTripleExp2 p i j k x := by
    linear_combination hnorm
  exact mul_left_cancel₀
    (mul_ne_zero (by norm_num : (12 : ℤ) ≠ 0) (by exact_mod_cast hp.ne')) hmul

/-- The partner of a progression point remains in the same progression. -/
lemma CoherentThetaInvolution.partner_onThetaProgression
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hp : 0 < p) (x : TripleQuintBranchIndex)
    (hx : OnThetaProgression p i j k R x) :
    OnThetaProgression p i j k R (T.partner x) := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, (T.pointTripleExp2_partner hp x ⟨N, hN⟩).trans hN⟩

/-- The branch partner is involutive because it is induced by an injective
coordinate encoding and an involutive rational linear map. -/
lemma CoherentThetaInvolution.partner_involutive
    {p i j k R : ℕ} (T : CoherentThetaInvolution p i j k R)
    (hp : 0 < p) (x : TripleQuintBranchIndex)
    (hx : OnThetaProgression p i j k R x) :
    T.partner (T.partner x) = x := by
  apply pointThetaVectorRat_injective p i j k hp
  have hy := T.partner_onThetaProgression hp x hx
  calc
    pointThetaVectorRat p i j k (T.partner (T.partner x)) =
        T.linear (pointThetaVectorRat p i j k (T.partner x)) :=
      (T.coordinate_transport (T.partner x) hy).symm
    _ = T.linear (T.linear (pointThetaVectorRat p i j k x)) := by
      rw [T.coordinate_transport x hx]
    _ = pointThetaVectorRat p i j k x := T.involutive _

/-- **Coherent geometry implies persistent vanishing.**  A single rational
orthogonal involution pairing the eight cosets cancels every coefficient in
the progression. -/
theorem coherentThetaInvolution_implies_persistentThetaCosetVanishing
    (p i j k R : ℕ) (T : CoherentThetaInvolution p i j k R)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    PersistentThetaCosetVanishing p i j k R := by
  apply (persistentThetaCosetVanishing_iff_persistentTripleVanishing
    p i j k R hi hpi hj hpj hk hpk).mpr
  intro N
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_expInvolution
    p i j k (p * N + R) T.partner hi hpi hj hpj hk hpk
  · intro x hexp
    exact T.weight_reverse x ⟨N, hexp⟩
  · intro x hexp
    exact T.pointTripleExp2_partner (by omega) x ⟨N, hexp⟩
  · intro x hexp
    exact T.partner_involutive (by omega) x ⟨N, hexp⟩

/-! ### The spectral and arithmetic interfaces -/

/-- Spectral coherence: a persistent identity between the eight ternary-coset
theta components is induced by one rational orthogonal involution. -/
def AdmissibleThetaGeometricCoherence (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    PersistentThetaCosetVanishing p i j k R →
      Nonempty (CoherentThetaInvolution p i j k R)

/-- Arithmetic classification interface: every coherent involution on
admissible Watson cosets yields an integral projective short-root target.  The
rational Householder-or-negative-Householder classification itself is proved
above, and `MultiQuintupleThetaArithmetic` proves this full interface. -/
def AdmissibleThetaInvolutionClassification (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    Nonempty (CoherentThetaInvolution p i j k R) →
      HasProjectiveRootTarget p i j k R

/-- **Breakthrough factorization.**  Spectral coherence plus classification of
the resulting rational orthogonal involution proves the full remaining
admissible theta/root rigidity theorem. -/
theorem admissibleThetaCosetRigidity_of_geometricCoherence_of_classification
    (p i j k R : ℕ)
    (hcoherence : AdmissibleThetaGeometricCoherence p i j k R)
    (hclassification : AdmissibleThetaInvolutionClassification p i j k R) :
    AdmissibleThetaCosetRigidity p i j k R := by
  intro hadmissible hR htheta
  exact hclassification hadmissible hR
    (hcoherence hadmissible hR htheta)

/-- Consequently the two geometric claims close the original admissible
Root--Vanishing rigidity proposition. -/
theorem admissibleRootVanishingRigidity_of_theta_geometry
    (p i j k R : ℕ)
    (hcoherence : AdmissibleThetaGeometricCoherence p i j k R)
    (hclassification : AdmissibleThetaInvolutionClassification p i j k R) :
    AdmissibleRootVanishingRigidity p i j k R := by
  exact (admissibleThetaCosetRigidity_iff_rootVanishingRigidity
    p i j k R).mp
      (admissibleThetaCosetRigidity_of_geometricCoherence_of_classification
        p i j k R hcoherence hclassification)

end Ramanujan.MultiQuintuple
