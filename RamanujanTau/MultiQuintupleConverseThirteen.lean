/-
# The full sparse converse at the short-generator exception p = 13

Actual product coefficients are evaluated through the already proved finite
Watson formula.  These evaluations are kernel checked; no external arithmetic
oracle is a premise.
-/
import RamanujanTau.MultiQuintupleRootVanishingClassification

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- Finite coefficient evaluation using two ordinary Cauchy products. -/
noncomputable def tripleBilateralCoeff (p i j k K : ℕ) : ℤ :=
  ∑ ab ∈ Finset.antidiagonal K,
    (∑ cd ∈ Finset.antidiagonal ab.1,
      quintBilateralCoeff p i cd.1 * quintBilateralCoeff p j cd.2) *
        quintBilateralCoeff p k ab.2

theorem coeff_triple_eq_tripleBilateralCoeff
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2*i < p) (hj : 0 < j) (hpj : 2*j < p)
    (hk : 0 < k) (hpk : 2*k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = tripleBilateralCoeff p i j k K := by
  simp only [tripleBilateralCoeff, coeff_mul,
    coeff_quintupleSpecialized_eq_bilateral p i _ hi hpi,
    coeff_quintupleSpecialized_eq_bilateral p j _ hj hpj,
    coeff_quintupleSpecialized_eq_bilateral p k _ hk hpk]

private theorem root13_134_4 : HasProjectiveRootTarget 13 1 3 4 4 := by
  refine ⟨{
    lambda := 1
    e := 2
    c := 1
    w1 := 1
    w2 := 3
    w3 := 4
    a1 := 0
    a2 := 0
    a3 := 0
    u := 2
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 12, 0, ?_, ?_⟩ <;> norm_num

private theorem root13_134_10 : HasProjectiveRootTarget 13 1 3 4 10 := by
  refine ⟨{
    lambda := 3
    e := 2
    c := 1
    w1 := 3
    w2 := -4
    w3 := -1
    a1 := 0
    a2 := -1
    a3 := -1
    u := -1
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 56, 12, ?_, ?_⟩ <;> norm_num

private theorem root13_134_2 : HasProjectiveRootTarget 13 1 3 4 2 := by
  refine ⟨{
    lambda := 4
    e := 2
    c := 1
    w1 := 4
    w2 := -1
    w3 := 3
    a1 := 0
    a2 := -1
    a3 := -1
    u := 1
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 16, 4, ?_, ?_⟩ <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_0 : tripleBilateralCoeff 13 1 3 4 0 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_1 : tripleBilateralCoeff 13 1 3 4 1 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_3 : tripleBilateralCoeff 13 1 3 4 3 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_5 : tripleBilateralCoeff 13 1 3 4 31 = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_6 : tripleBilateralCoeff 13 1 3 4 6 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_7 : tripleBilateralCoeff 13 1 3 4 20 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_8 : tripleBilateralCoeff 13 1 3 4 8 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_9 : tripleBilateralCoeff 13 1 3 4 9 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_11 : tripleBilateralCoeff 13 1 3 4 24 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_134_12 : tripleBilateralCoeff 13 1 3 4 38 = (-1) := by
  decide +kernel

/-- Every residue at this exceptional triple has an exact root certificate
or a kernel-checked nonzero coefficient of the actual infinite product. -/
theorem root_or_witness13_134 (R : ℕ) (hR : R < 13) :
    HasProjectiveRootTarget 13 1 3 4 R ∨
      ∃ N : ℕ, coeff (13*N+R) (quintupleSpecialized 13 1 *
        quintupleSpecialized 13 3 * quintupleSpecialized 13 4) ≠ 0 := by
  interval_cases R
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_0 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_1 (by norm_num : (-1 : ℤ) ≠ 0)
  · exact Or.inl root13_134_2
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_3 (by norm_num : (-1 : ℤ) ≠ 0)
  · exact Or.inl root13_134_4
  · right
    refine ⟨2, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_5 (by norm_num : (2 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_6 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨1, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_7 (by norm_num : (-1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_8 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_9 (by norm_num : (-1 : ℤ) ≠ 0)
  · exact Or.inl root13_134_10
  · right
    refine ⟨1, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_11 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨2, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 1 3 4 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_134_12 (by norm_num : (-1 : ℤ) ≠ 0)

private theorem root13_256_3 : HasProjectiveRootTarget 13 2 5 6 3 := by
  refine ⟨{
    lambda := 2
    e := 2
    c := 1
    w1 := 4
    w2 := -3
    w3 := -1
    a1 := 0
    a2 := -1
    a3 := -1
    u := -1
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 6, 0, ?_, ?_⟩ <;> norm_num

private theorem root13_256_11 : HasProjectiveRootTarget 13 2 5 6 11 := by
  refine ⟨{
    lambda := 7
    e := 2
    c := 1
    w1 := 1
    w2 := -4
    w3 := 3
    a1 := -1
    a2 := -3
    a3 := -3
    u := 0
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 154, 82, ?_, ?_⟩ <;> norm_num

private theorem root13_256_9 : HasProjectiveRootTarget 13 2 5 6 9 := by
  refine ⟨{
    lambda := 8
    e := 2
    c := 1
    w1 := 3
    w2 := 1
    w3 := -4
    a1 := -1
    a2 := -3
    a3 := -4
    u := -1
    he := Or.inr rfl
    hw1 := by norm_num
    hw2 := by norm_num
    hw3 := by norm_num
    hvw := by norm_num [ternaryDot]
    hroot := by norm_num [ternaryNorm]
    hcoefficient := by norm_num
    hcase := ?_
  }⟩
  right
  refine ⟨by decide +kernel, 138, 84, ?_, ?_⟩ <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_0 : tripleBilateralCoeff 13 2 5 6 0 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_1 : tripleBilateralCoeff 13 2 5 6 1 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_2 : tripleBilateralCoeff 13 2 5 6 2 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_4 : tripleBilateralCoeff 13 2 5 6 4 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_5 : tripleBilateralCoeff 13 2 5 6 18 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_6 : tripleBilateralCoeff 13 2 5 6 6 = (-1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_7 : tripleBilateralCoeff 13 2 5 6 7 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_8 : tripleBilateralCoeff 13 2 5 6 8 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_10 : tripleBilateralCoeff 13 2 5 6 36 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient13_256_12 : tripleBilateralCoeff 13 2 5 6 25 = (-1) := by
  decide +kernel

/-- Every residue at this exceptional triple has an exact root certificate
or a kernel-checked nonzero coefficient of the actual infinite product. -/
theorem root_or_witness13_256 (R : ℕ) (hR : R < 13) :
    HasProjectiveRootTarget 13 2 5 6 R ∨
      ∃ N : ℕ, coeff (13*N+R) (quintupleSpecialized 13 2 *
        quintupleSpecialized 13 5 * quintupleSpecialized 13 6) ≠ 0 := by
  interval_cases R
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_0 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_1 (by norm_num : (-1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_2 (by norm_num : (-1 : ℤ) ≠ 0)
  · exact Or.inl root13_256_3
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_4 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨1, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_5 (by norm_num : (-1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_6 (by norm_num : (-1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_7 (by norm_num : (1 : ℤ) ≠ 0)
  · right
    refine ⟨0, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_8 (by norm_num : (1 : ℤ) ≠ 0)
  · exact Or.inl root13_256_9
  · right
    refine ⟨2, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_10 (by norm_num : (1 : ℤ) ≠ 0)
  · exact Or.inl root13_256_11
  · right
    refine ⟨1, ?_⟩
    rw [coeff_triple_eq_tripleBilateralCoeff 13 2 5 6 _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    simpa using ne_of_eq_of_ne coefficient13_256_12 (by norm_num : (-1 : ℤ) ≠ 0)

private theorem admissible13_finite :
    ∀ i j k : Fin 7, (0 < i.val ∧ i.val < j.val ∧ j.val < k.val ∧
      (13 : ℤ) ∣ ternaryNorm i.val j.val k.val) →
        (i.val = 1 ∧ j.val = 3 ∧ k.val = 4) ∨
        (i.val = 2 ∧ j.val = 5 ∧ k.val = 6) := by
  decide +kernel

/-- The short-generator exceptional prime has the full unconditional
admissible converse, including actual coefficient witnesses for every miss. -/
theorem admissible_root_vanishing_converse_thirteen
    (i j k R : ℕ) (ha : AdmissibleSparseTriple 13 i j k) (hR : R < 13)
    (hz : PersistentTripleVanishing 13 i j k R) :
    HasProjectiveRootTarget 13 i j k R := by
  rcases ha with ⟨hp, hp3, hi, hij, hjk, hpk, hnorm⟩
  have hic : i < 7 := by omega
  have hjc : j < 7 := by omega
  have hkc : k < 7 := by omega
  rcases admissible13_finite ⟨i,hic⟩ ⟨j,hjc⟩ ⟨k,hkc⟩ ⟨hi,hij,hjk,hnorm⟩ with h | h
  · rcases h with ⟨rfl,rfl,rfl⟩
    rcases root_or_witness13_134 R hR with hroot | ⟨N,hN⟩
    · exact hroot
    · exact False.elim (hN (hz N))
  · rcases h with ⟨rfl,rfl,rfl⟩
    rcases root_or_witness13_256 R hR with hroot | ⟨N,hN⟩
    · exact hroot
    · exact False.elim (hN (hz N))

/-- The complete Root--Vanishing equivalence at modulus thirteen, for all
admissible triples and every canonical residue. -/
theorem admissible_root_vanishing_equivalence_thirteen
    (i j k R : ℕ) (ha : AdmissibleSparseTriple 13 i j k) (hR : R < 13) :
    HasProjectiveRootTarget 13 i j k R ↔ PersistentTripleVanishing 13 i j k R := by
  constructor
  · rcases ha with ⟨_, _, hi, hij, hjk, hpk, _⟩
    exact hasProjectiveRootTarget_implies_persistentTripleVanishing 13 i j k R
      hi (by omega) (by omega) (by omega) (by omega) hpk (by decide)
  · exact admissible_root_vanishing_converse_thirteen i j k R ha hR

end Ramanujan.MultiQuintuple
