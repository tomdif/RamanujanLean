/-
# The ternary-character theta form of the triple quintuple product

Writing a Watson branch index as `m = 3n+b`, its sign is the value of the
shifted nontrivial character modulo three

  `chi(m) = 1`  if `m = 0 (mod 3)`,
  `chi(m) = -1` if `m = 1 (mod 3)`,
  `chi(m) = 0`  if `m = 2 (mod 3)`.

Thus the apparent difference of two four-coset theta unions is one ternary
theta series weighted by `chi(m1)chi(m2)chi(m3)`.  This is the natural form
for a Weil-representation, Hecke, or cusp-order attack on the remaining
spectral-separation theorem.
-/
import RamanujanTau.MultiQuintupleThetaArithmetic

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- The shifted quadratic character modulo three carried by one Watson
index.  It is the nontrivial character evaluated at `m+1`. -/
def shiftedCharacterThree (m : ℤ) : ℤ :=
  if ((m : ZMod 3) = 0) then 1
  else if ((m : ZMod 3) = 1) then -1
  else 0

@[simp] lemma shiftedCharacterThree_three_mul_add_branchBit
    (n : ℤ) (b : Bool) :
    shiftedCharacterThree (3 * n + branchBitInt b) = -branchSign b := by
  cases b
  · have hzero : (((3 * n : ℤ) : ZMod 3)) = 0 := by
      rw [Int.cast_mul]
      rw [show ((3 : ℤ) : ZMod 3) = 0 by decide]
      simp
    simp [shiftedCharacterThree, branchBitInt, branchSign, hzero]
  · have hone : (((3 * n + 1 : ℤ) : ZMod 3)) = 1 := by
      rw [Int.cast_add, Int.cast_mul]
      rw [show ((3 : ℤ) : ZMod 3) = 0 by decide]
      simp
    simp [shiftedCharacterThree, branchBitInt, branchSign, hone]

/-- Product of the three shifted mod-three characters. -/
def ternaryWatsonCharacter (m : TernaryIntIndex) : ℤ :=
  shiftedCharacterThree m.1.1 * shiftedCharacterThree m.1.2 *
    shiftedCharacterThree m.2

/-- The original Watson branch sign is exactly the threefold character of its
affine index. -/
theorem pointBranchWeight_eq_ternaryWatsonCharacter
    (x : TripleQuintBranchIndex) :
    pointBranchWeight x = ternaryWatsonCharacter (pointAffineIndex x) := by
  rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
  simp [pointBranchWeight, pointAffineIndex, pointB1, pointB2, pointB3,
    pointN1, pointN2, pointN3, ternaryWatsonCharacter]

/-- Finite coefficient shell written with the single ternary character rather
than eight separately signed branches. -/
theorem coeff_tripleQuintupleSpecialized_eq_characterBox
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) =
      ∑ x ∈ tripleQuintBranchBox K,
        if pointTripleExp2 p i j k x = 2 * (K : ℤ)
        then ternaryWatsonCharacter (pointAffineIndex x) else 0 := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K
    hi hpi hj hpj hk hpk]
  apply Finset.sum_congr rfl
  intro x hx
  rw [pointContribution, pointBranchWeight_eq_ternaryWatsonCharacter]

/-- The character-weighted affine theta series, indexed in the original
quintuple-product degree. -/
noncomputable def affineCharacterTheta
    (p i j k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun K =>
    ∑ x ∈ tripleQuintBranchBox K,
      if pointTripleExp2 p i j k x = 2 * (K : ℤ)
      then ternaryWatsonCharacter (pointAffineIndex x) else 0

@[simp] theorem coeff_affineCharacterTheta
    (p i j k K : ℕ) :
    coeff K (affineCharacterTheta p i j k) =
      ∑ x ∈ tripleQuintBranchBox K,
        if pointTripleExp2 p i j k x = 2 * (K : ℤ)
        then ternaryWatsonCharacter (pointAffineIndex x) else 0 := by
  simp [affineCharacterTheta]

/-- **Exact ternary-character normal form.**  The actual stabilized product of
three specialized quintuple products is one character-weighted ternary theta
series. -/
theorem affineCharacterTheta_eq_tripleQuintupleSpecialized
    (p i j k : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    affineCharacterTheta p i j k =
      quintupleSpecialized p i * quintupleSpecialized p j *
        quintupleSpecialized p k := by
  ext K
  rw [coeff_affineCharacterTheta,
    coeff_tripleQuintupleSpecialized_eq_characterBox p i j k K
      hi hpi hj hpj hk hpk]

/-- The single character theta and the earlier signed eight-coset theta are
the same series, not merely two models with matching vanishing sets. -/
theorem affineCharacterTheta_eq_signedWatsonCosetTheta
    (p i j k : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    affineCharacterTheta p i j k = signedWatsonCosetTheta p i j k := by
  rw [affineCharacterTheta_eq_tripleQuintupleSpecialized p i j k
      hi hpi hj hpj hk hpk,
    signedWatsonCosetTheta_eq_tripleQuintupleSpecialized p i j k
      hi hpi hj hpj hk hpk]

/-- Persistent vanishing stated directly for the ternary-character theta
series. -/
def PersistentAffineCharacterVanishing
    (p i j k R : ℕ) : Prop :=
  ∀ N : ℕ, coeff (p * N + R) (affineCharacterTheta p i j k) = 0

/-- The ternary-character and actual-product formulations are identical on
canonical specializations. -/
theorem persistentAffineCharacterVanishing_iff_persistentTripleVanishing
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    PersistentAffineCharacterVanishing p i j k R ↔
      PersistentTripleVanishing p i j k R := by
  rw [PersistentAffineCharacterVanishing, PersistentTripleVanishing,
    affineCharacterTheta_eq_tripleQuintupleSpecialized p i j k
      hi hpi hj hpj hk hpk]

end Ramanujan.MultiQuintuple
