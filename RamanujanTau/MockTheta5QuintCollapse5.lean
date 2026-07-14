/-
# Quintuple product, stone 3 (capstone): the general-N per-term

For general `N`, `zProj_thetaA` at the shifts `N ∓ 2(m+1)` carries the sign `(−1)^{N.natAbs}` (constant in `m`,
by the parity/sign lemmas). Factoring it out, the per-term is

  `zProj N (thetaA·thetaBTerm m) = (−1)^{N.natAbs} · (−1)^{m+1}
      · (q^{(m+1)² + e₋(N,m)} + q^{(m+1)² + e₊(N,m)})`,

where `e∓(N,m) = ⌊(N∓2(m+1))(N∓2(m+1)+1)/2⌋`. Summed over `m` (with `zProj N thetaA`) this is the
pentagonal-shaped theta-A sum that (after the residue-dependent reindex) collapses to
`qfac2Inf · zProj N quintTheta`. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintCollapse
import RamanujanTau.MockTheta5QuintConv2
import RamanujanTau.MockTheta5QuintBracket1

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- `zProj (N − 2(m+1)) thetaA` with the sign factored to `(−1)^{N.natAbs}`. -/
lemma zProj_thetaA_sub (N : ℤ) (m : ℕ) :
    zProj (N - 2 * ((m : ℤ) + 1)) thetaA
      = PowerSeries.C ((-1 : ℤ) ^ N.natAbs)
        * X ^ (((N - 2 * ((m : ℤ) + 1)) * ((N - 2 * ((m : ℤ) + 1)) + 1) / 2).toNat) := by
  rw [zProj_thetaA, neg_one_natAbs_sub]

/-- `zProj (N + 2(m+1)) thetaA` with the sign factored to `(−1)^{N.natAbs}`. -/
lemma zProj_thetaA_add (N : ℤ) (m : ℕ) :
    zProj (N + 2 * ((m : ℤ) + 1)) thetaA
      = PowerSeries.C ((-1 : ℤ) ^ N.natAbs)
        * X ^ (((N + 2 * ((m : ℤ) + 1)) * ((N + 2 * ((m : ℤ) + 1)) + 1) / 2).toNat) := by
  rw [zProj_thetaA, neg_one_natAbs_add]

/-- **the general-N per-term.** -/
lemma per_term_general (N : ℤ) (m : ℕ) :
    zProj N (thetaA * thetaBTerm m)
      = PowerSeries.C ((-1 : ℤ) ^ N.natAbs) * (PowerSeries.C ((-1 : ℤ) ^ (m + 1))
        * (X ^ ((m + 1) ^ 2 + ((N - 2 * ((m : ℤ) + 1)) * ((N - 2 * ((m : ℤ) + 1)) + 1) / 2).toNat)
          + X ^ ((m + 1) ^ 2 + ((N + 2 * ((m : ℤ) + 1)) * ((N + 2 * ((m : ℤ) + 1)) + 1) / 2).toNat))) := by
  rw [zProj_thetaA_mul_thetaBTerm, zProj_thetaA_sub, zProj_thetaA_add,
      show X ^ ((m + 1) ^ 2) * (PowerSeries.C ((-1 : ℤ) ^ (m + 1))
            * (PowerSeries.C ((-1 : ℤ) ^ N.natAbs)
                * X ^ (((N - 2 * ((m : ℤ) + 1)) * ((N - 2 * ((m : ℤ) + 1)) + 1) / 2).toNat)
              + PowerSeries.C ((-1 : ℤ) ^ N.natAbs)
                * X ^ (((N + 2 * ((m : ℤ) + 1)) * ((N + 2 * ((m : ℤ) + 1)) + 1) / 2).toNat)))
          = PowerSeries.C ((-1 : ℤ) ^ N.natAbs) * (PowerSeries.C ((-1 : ℤ) ^ (m + 1))
            * (X ^ ((m + 1) ^ 2) * X ^ (((N - 2 * ((m : ℤ) + 1)) * ((N - 2 * ((m : ℤ) + 1)) + 1) / 2).toNat)
              + X ^ ((m + 1) ^ 2) * X ^ (((N + 2 * ((m : ℤ) + 1)) * ((N + 2 * ((m : ℤ) + 1)) + 1) / 2).toNat)))
        from by ring,
      ← pow_add, ← pow_add]

end MockTheta5.JTP
