import RamanujanTau.MultiQuintupleFourWitness17

/-! Necessary lower bounds for universal four-factor first-witness cutoffs.
These statements concern four factors; the original triple-product conjecture is separate. -/
namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- A linear first-witness bound for every distinct canonical isotropic four-tuple. -/
def FourWitnessLinearBound (c : ℝ) : Prop :=
  ∀ p i j k l R : ℕ, Nat.Prime p → 0 < i → i < j → j < k → k < l → 2*l < p →
    p ∣ i^2+j^2+k^2+l^2 → R < p →
    (∃ N : ℕ, coeff (p*N+R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k * quintupleSpecialized p l) ≠ 0) →
    ∃ N : ℕ, (N : ℝ) ≤ c*p ∧ coeff (p*N+R) (quintupleSpecialized p i *
      quintupleSpecialized p j * quintupleSpecialized p k * quintupleSpecialized p l) ≠ 0

/-- Any such universal coefficient must be at least 7/17. This does not assert sufficiency. -/
theorem fourWitnessLinearBound_ge (c : ℝ) (h : FourWitnessLinearBound c) : 7/17 ≤ c := by
  obtain ⟨N,hN,hne⟩ := h 17 2 3 5 8 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨7,by rw [first_witness_four17.2]; norm_num⟩
  have h7 : 7 ≤ N := by
    by_contra hh
    exact hne (first_witness_four17.1 N (by omega))
  have h7real : (7 : ℝ) ≤ N := by exact_mod_cast h7
  norm_num at hN
  linarith

/-- The quarter-prime bound cannot hold for all admissible four-factor products. -/
theorem not_fourWitnessQuarterBound : ¬ FourWitnessLinearBound (1/4) := by
  intro h
  have hh := fourWitnessLinearBound_ge (1/4) h
  norm_num at hh

/-- Increasing the coefficient to two fifths still cannot give a universal bound. -/
theorem not_fourWitnessTwoFifthsBound : ¬ FourWitnessLinearBound (2/5) := by
  intro h
  have hh := fourWitnessLinearBound_ge (2/5) h
  norm_num at hh

end Ramanujan.MultiQuintuple
