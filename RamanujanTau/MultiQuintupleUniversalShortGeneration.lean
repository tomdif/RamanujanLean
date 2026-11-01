/-
# Universal short generation, with the separately classified modulus 13 removed
-/
import RamanujanTau.MultiQuintupleFiniteGenerators
import RamanujanTau.MultiQuintupleLargePrimeGeneration

namespace Ramanujan.MultiQuintuple

theorem short_generation_below_1250 {p i j k : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hp : p < 1250) (hp13 : p ≠ 13) :
    Submodule.span ℤ (shortSupportedDualSet p (((i : ℤ),(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) := by
  letI : Fact p.Prime := ⟨ha.1⟩
  apply short_generation_of_normalized ha
  intro a b ha hab hbp hiso
  exact short_generation_normalized_below_1250 hp hp13 a b ha hab hbp hiso

/-- Every admissible dual lattice except modulus 13 is integrally generated
by supported vectors of squared norm strictly less than p²/2. The finite
and infinite ranges are both checked in Lean. -/
theorem admissible_short_dual_generation {p i j k : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hp13 : p ≠ 13) :
    Submodule.span ℤ (shortSupportedDualSet p (((i : ℤ),(j : ℤ)),(k : ℤ))) =
      projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) := by
  rcases lt_or_ge p 1250 with hp | hp
  · exact short_generation_below_1250 ha hp hp13
  · exact short_generation_above_1250 ha hp

end Ramanujan.MultiQuintuple
