/-
# Finite-witness normal form for theta rigidity

The remaining spectral-coherence theorem can be attacked without reconstructing
an orthogonal map directly from an infinite theta identity.  Its exact
contrapositive is certificate-theoretic: for every admissible residue, either
there is a short projective root targeting that residue, or one finite
coefficient in the progression is nonzero.

Both alternatives have finite, independently checkable data.  This file proves
that the resulting root-or-witness dichotomy is logically equivalent to theta
coset rigidity, geometric coherence, and corrected Root--Vanishing rigidity.
It also isolates bounded witness versions suitable for exact census and a
future effective geometry-of-numbers or Sturm-bound argument.
-/
import RamanujanTau.MultiQuintupleThetaArithmetic

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- A concrete coefficient disproving persistent vanishing of the signed
eight-coset theta projection. -/
def ThetaNonvanishingWitness (p i j k R : ℕ) : Prop :=
  ∃ N : ℕ,
    coeff (p * N + R) (signedWatsonCosetTheta p i j k) ≠ 0

/-- A finite witness is exactly the negation of persistent theta vanishing. -/
theorem thetaNonvanishingWitness_iff_not_persistentThetaCosetVanishing
    (p i j k R : ℕ) :
    ThetaNonvanishingWitness p i j k R ↔
      ¬PersistentThetaCosetVanishing p i j k R := by
  classical
  simp [ThetaNonvanishingWitness, PersistentThetaCosetVanishing]

/-- The same witness stated directly for the actual triple product. -/
def TripleProductNonvanishingWitness (p i j k R : ℕ) : Prop :=
  ∃ N : ℕ,
    coeff (p * N + R)
      (quintupleSpecialized p i * quintupleSpecialized p j *
        quintupleSpecialized p k) ≠ 0

/-- On admissible canonical data, the spectral and actual-product witnesses
are identical coefficient certificates. -/
theorem thetaNonvanishingWitness_iff_tripleProductNonvanishingWitness
    (p i j k R : ℕ) (hadmissible : AdmissibleSparseTriple p i j k) :
    ThetaNonvanishingWitness p i j k R ↔
      TripleProductNonvanishingWitness p i j k R := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rwa [signedWatsonCosetTheta_eq_tripleQuintupleSpecialized
      p i j k hi hpi hj hpj hk hpk] at hN
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rwa [signedWatsonCosetTheta_eq_tripleQuintupleSpecialized
      p i j k hi hpi hj hpj hk hpk]

/-- The operational form of the remaining conjecture: admissible data have
either a projective-root target or one finite theta coefficient witness. -/
def AdmissibleRootOrThetaWitness (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    HasProjectiveRootTarget p i j k R ∨
      ThetaNonvanishingWitness p i j k R

/-- **Exact certificate normal form.**  The root-or-finite-witness dichotomy
is neither weaker nor stronger than theta-coset rigidity. -/
theorem admissibleRootOrThetaWitness_iff_thetaCosetRigidity
    (p i j k R : ℕ) :
    AdmissibleRootOrThetaWitness p i j k R ↔
      AdmissibleThetaCosetRigidity p i j k R := by
  constructor
  · intro hdichotomy hadmissible hR hpersistent
    rcases hdichotomy hadmissible hR with hroot | ⟨N, hnonzero⟩
    · exact hroot
    · exact (hnonzero (hpersistent N)).elim
  · intro hrigidity hadmissible hR
    by_cases hpersistent : PersistentThetaCosetVanishing p i j k R
    · exact Or.inl (hrigidity hadmissible hR hpersistent)
    · exact Or.inr
        ((thetaNonvanishingWitness_iff_not_persistentThetaCosetVanishing
          p i j k R).mpr hpersistent)

/-- The computable version uses coefficients of the actual triple quintuple
product rather than the theta wrapper. -/
def AdmissibleRootOrProductWitness (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    HasProjectiveRootTarget p i j k R ∨
      TripleProductNonvanishingWitness p i j k R

theorem admissibleRootOrProductWitness_iff_rootOrThetaWitness
    (p i j k R : ℕ) :
    AdmissibleRootOrProductWitness p i j k R ↔
      AdmissibleRootOrThetaWitness p i j k R := by
  constructor
  · intro hproduct hadmissible hR
    rcases hproduct hadmissible hR with hroot | hwitness
    · exact Or.inl hroot
    · exact Or.inr
        ((thetaNonvanishingWitness_iff_tripleProductNonvanishingWitness
          p i j k R hadmissible).mpr hwitness)
  · intro htheta hadmissible hR
    rcases htheta hadmissible hR with hroot | hwitness
    · exact Or.inl hroot
    · exact Or.inr
        ((thetaNonvanishingWitness_iff_tripleProductNonvanishingWitness
          p i j k R hadmissible).mp hwitness)

/-- **Exact finite-certificate frontier.**  Proving that every admissible
residue has either a root certificate or one nonzero product coefficient is
equivalent to the corrected Root--Vanishing rigidity theorem. -/
theorem admissibleRootOrProductWitness_iff_rootVanishingRigidity
    (p i j k R : ℕ) :
    AdmissibleRootOrProductWitness p i j k R ↔
      AdmissibleRootVanishingRigidity p i j k R := by
  rw [admissibleRootOrProductWitness_iff_rootOrThetaWitness,
    admissibleRootOrThetaWitness_iff_thetaCosetRigidity,
    admissibleThetaCosetRigidity_iff_rootVanishingRigidity]

/-- The same certificate dichotomy is exactly spectral geometric coherence,
using the proved projective-root/coherent-involution equivalence. -/
theorem admissibleRootOrProductWitness_iff_thetaGeometricCoherence
    (p i j k R : ℕ) :
    AdmissibleRootOrProductWitness p i j k R ↔
      AdmissibleThetaGeometricCoherence p i j k R := by
  rw [admissibleRootOrProductWitness_iff_rootOrThetaWitness,
    admissibleRootOrThetaWitness_iff_thetaCosetRigidity,
    admissibleThetaGeometricCoherence_iff_thetaCosetRigidity]

/-! ### Effective finite cutoffs -/

/-- A nonzero actual-product coefficient no later than progression index
`B`. -/
def TripleProductNonvanishingWitnessThrough
    (B p i j k R : ℕ) : Prop :=
  ∃ N : ℕ, N ≤ B ∧
    coeff (p * N + R)
      (quintupleSpecialized p i * quintupleSpecialized p j *
        quintupleSpecialized p k) ≠ 0

lemma tripleProductNonvanishingWitnessThrough_mono
    {B C p i j k R : ℕ} (hBC : B ≤ C) :
    TripleProductNonvanishingWitnessThrough B p i j k R →
      TripleProductNonvanishingWitnessThrough C p i j k R := by
  rintro ⟨N, hNB, hnonzero⟩
  exact ⟨N, hNB.trans hBC, hnonzero⟩

lemma tripleProductNonvanishingWitness_of_through
    {B p i j k R : ℕ} :
    TripleProductNonvanishingWitnessThrough B p i j k R →
      TripleProductNonvanishingWitness p i j k R := by
  rintro ⟨N, hNB, hnonzero⟩
  exact ⟨N, hnonzero⟩

/-- A bounded, fully finite certificate target.  Any universal proof of this
statement at an explicit bound closes the original rigidity conjecture. -/
def AdmissibleRootOrProductWitnessThrough
    (B p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    HasProjectiveRootTarget p i j k R ∨
      TripleProductNonvanishingWitnessThrough B p i j k R

theorem admissibleRootOrProductWitness_of_through
    (B p i j k R : ℕ)
    (hfinite : AdmissibleRootOrProductWitnessThrough B p i j k R) :
    AdmissibleRootOrProductWitness p i j k R := by
  intro hadmissible hR
  rcases hfinite hadmissible hR with hroot | hwitness
  · exact Or.inl hroot
  · exact Or.inr (tripleProductNonvanishingWitness_of_through hwitness)

/-- A bounded root-or-witness theorem immediately proves spectral coherence. -/
theorem admissibleThetaGeometricCoherence_of_rootOrProductWitnessThrough
    (B p i j k R : ℕ)
    (hfinite : AdmissibleRootOrProductWitnessThrough B p i j k R) :
    AdmissibleThetaGeometricCoherence p i j k R :=
  (admissibleRootOrProductWitness_iff_thetaGeometricCoherence
    p i j k R).mp
      (admissibleRootOrProductWitness_of_through B p i j k R hfinite)

/-- Consequently any explicit bounded certificate theorem closes corrected
Root--Vanishing rigidity as well. -/
theorem admissibleRootVanishingRigidity_of_rootOrProductWitnessThrough
    (B p i j k R : ℕ)
    (hfinite : AdmissibleRootOrProductWitnessThrough B p i j k R) :
    AdmissibleRootVanishingRigidity p i j k R :=
  (admissibleRootOrProductWitness_iff_rootVanishingRigidity
    p i j k R).mp
      (admissibleRootOrProductWitness_of_through B p i j k R hfinite)

end Ramanujan.MultiQuintuple
