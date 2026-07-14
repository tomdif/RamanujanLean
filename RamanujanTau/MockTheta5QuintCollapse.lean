/-
# Quintuple product, stone 3 (capstone): the pentagonal collapse — sign lemmas

Toward `zProj N (thetaA·thetaB) = qfac2Inf · zProj N (quintTheta)`. The per-term shift signs
`(−1)^{(N±2(m+1)).natAbs}` are all equal to `(−1)^{N.natAbs}` (shifting by an even number preserves
parity, and `natAbs` preserves parity), so they factor out of the m-sum as the constant `(−1)^{N.natAbs}`,
leaving the pentagonal-shaped theta-A sum. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintConv3
import RamanujanTau.MockTheta5QuintThetaProj

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- shifting by `2j` preserves the `natAbs`-parity sign. -/
lemma neg_one_natAbs_sub (N : ℤ) (j : ℤ) :
    ((-1 : ℤ)) ^ (N - 2 * j).natAbs = ((-1 : ℤ)) ^ N.natAbs := by
  rcases Int.even_or_odd N with hN | hN
  · rw [Even.neg_one_pow (Int.natAbs_even.mpr (hN.sub (even_two_mul j))),
        Even.neg_one_pow (Int.natAbs_even.mpr hN)]
  · rw [Odd.neg_one_pow (Int.natAbs_odd.mpr (hN.sub_even (even_two_mul j))),
        Odd.neg_one_pow (Int.natAbs_odd.mpr hN)]

/-- shifting by `2j` preserves the `natAbs`-parity sign (additive version). -/
lemma neg_one_natAbs_add (N : ℤ) (j : ℤ) :
    ((-1 : ℤ)) ^ (N + 2 * j).natAbs = ((-1 : ℤ)) ^ N.natAbs := by
  rcases Int.even_or_odd N with hN | hN
  · rw [Even.neg_one_pow (Int.natAbs_even.mpr (hN.add (even_two_mul j))),
        Even.neg_one_pow (Int.natAbs_even.mpr hN)]
  · rw [Odd.neg_one_pow (Int.natAbs_odd.mpr (hN.add_even (even_two_mul j))),
        Odd.neg_one_pow (Int.natAbs_odd.mpr hN)]

end MockTheta5.JTP
