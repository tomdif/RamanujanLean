import RamanujanTau.MultiQuintupleCancellation

/-!
# An explicit infinite family of sparse quintuple-product vanishings

For every `t`, set `p = 9*t^2 + 15*t + 7`. The triple `(1,3*t+2,3*t+3)`
has squared norm `2*p`, and the negative reflection targets residue `3*t+3`.
Every coefficient in that progression vanishes. No primality assumption is
needed: the first moduli are 7, 31, 73, 133, 211.

This is a specialization of the existing short-root cancellation theorem.
It does not prove the converse from vanishing to lattice symmetry.
-/

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- The Eisenstein norm `1 + (3*t+2) + (3*t+2)^2`. -/
def eisensteinFamilyModulus (t : ℕ) : ℕ := 9 * t ^ 2 + 15 * t + 7

/-- An unconditional infinite family of full coefficient progressions that
vanish in the actual stabilized triple quintuple product, including composite
moduli. The short root is the index triple itself. -/
theorem coeff_eisensteinFamily_zero (t N : ℕ) :
    coeff (eisensteinFamilyModulus t * N + (3 * t + 3))
      (quintupleSpecialized (eisensteinFamilyModulus t) 1 *
        quintupleSpecialized (eisensteinFamilyModulus t) (3 * t + 2) *
        quintupleSpecialized (eisensteinFamilyModulus t) (3 * t + 3)) = 0 := by
  have hpodd : Odd (eisensteinFamilyModulus t : ℤ) := by
    obtain ⟨z, hz⟩ := Int.even_mul_succ_self (t : ℤ)
    refine ⟨9 * z + 3 * (t : ℤ) + 3, ?_⟩
    dsimp [eisensteinFamilyModulus]
    nlinarith
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_negative_shortRoot
    (eisensteinFamilyModulus t) 1 (3 * t + 2) (3 * t + 3) N (3 * t + 3)
    2 1 0
  · omega
  · dsimp [eisensteinFamilyModulus]; nlinarith
  · omega
  · dsimp [eisensteinFamilyModulus]; nlinarith
  · omega
  · dsimp [eisensteinFamilyModulus]; nlinarith
  · exact hpodd
  · exact Or.inr rfl
  · dsimp [eisensteinFamilyModulus]
    push_cast
    rw [show (9 : ZMod 3) = 0 by decide +kernel,
      show (15 : ZMod 3) = 0 by decide +kernel,
      show (7 : ZMod 3) = 1 by decide +kernel]
    ring
  · simp only [ternaryNorm, eisensteinFamilyModulus]
    push_cast
    ring
  · norm_num
  · push_cast
    ring

end Ramanujan.MultiQuintuple
