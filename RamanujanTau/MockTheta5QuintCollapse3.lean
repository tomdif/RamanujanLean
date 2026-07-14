/-
# Quintuple product, stone 3 (capstone): the per-term = E2(pentTermP) correspondence

The crux of the N=0 pentagonal collapse: term by term,

  `zProj 0 (thetaA · thetaBTerm m) = E2 (map evm1 (pentTermP m))`.

Both sides equal `(−1)^{m+1}(q^{(m+1)(3m+2)} + q^{(m+1)(3m+4)})`: the left by `per_term_zero`, the right by
evaluating `pentTermP m` at `z = −1` (`evm1`, sending `T(±(m+1)) ↦ (−1)^{m+1}`) and doubling the exponent
(`E2`). Summed over `m`, `Σ E2(map evm1 (pentTermP m)) = E2(pentSeries − 1)`, whence
`zProj 0 (thetaA·thetaB) = E2(pentSeries) = (q²;q²)_∞`. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintCollapse2
import RamanujanTau.MockTheta5PentTheta
import RamanujanTau.MockTheta5AltTheta
import RamanujanTau.MockTheta5JacobiCauchy

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- `E2` fixes constants. -/
lemma E2_C (c : ℤ) : E2 (PowerSeries.C c) = PowerSeries.C c := by
  ext k
  rw [coeff_E2, PowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    split_ifs with h1 h2
    · exfalso; omega
    · rfl
    · rfl

/-- `map evm1 (pentTermP m) = (−1)^{m+1}(q^{(m+1)(3m+2)/2} + q^{(m+1)(3m+4)/2})`. -/
lemma map_evm1_pentTermP (m : ℕ) :
    PowerSeries.map evm1 (pentTermP m)
      = PowerSeries.C ((-1 : ℤ) ^ (m + 1))
        * (X ^ ((m + 1) * (3 * m + 2) / 2) + X ^ ((m + 1) * (3 * m + 4) / 2)) := by
  rw [pentTermP, map_add, map_mul, map_mul,
      show PowerSeries.map evm1 (X ^ ((m + 1) * (3 * m + 2) / 2))
          = X ^ ((m + 1) * (3 * m + 2) / 2) from by rw [map_pow, PowerSeries.map_X],
      show PowerSeries.map evm1 (X ^ ((m + 1) * (3 * m + 4) / 2))
          = X ^ ((m + 1) * (3 * m + 4) / 2) from by rw [map_pow, PowerSeries.map_X],
      PowerSeries.map_C, PowerSeries.map_C,
      show evm1 (T ((m : ℤ) + 1)) = (-1 : ℤ) ^ (m + 1) from by
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) from by push_cast; ring, evm1_T_nat],
      show evm1 (T (-((m : ℤ) + 1))) = (-1 : ℤ) ^ (m + 1) from by
        rw [show (-((m : ℤ) + 1)) = (-((m + 1 : ℕ) : ℤ)) from by push_cast; ring, evm1_T_negnat]]
  ring

/-- **the per-term correspondence.** -/
lemma per_term_zero_eq_pent (m : ℕ) :
    zProj (0 : ℤ) (thetaA * thetaBTerm m) = E2 (PowerSeries.map evm1 (pentTermP m)) := by
  have h2 : 2 ∣ (m + 1) * (3 * m + 2) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨(2 * k + 1) * (3 * k + 1), by ring⟩
    · exact ⟨(k + 1) * (6 * k + 5), by ring⟩
  have h4 : 2 ∣ (m + 1) * (3 * m + 4) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩
    · exact ⟨(k + 1) * (6 * k + 7), by ring⟩
  rw [per_term_zero, map_evm1_pentTermP, map_mul, map_add, E2_C, E2_X_pow, E2_X_pow,
      Nat.mul_div_cancel' h2, Nat.mul_div_cancel' h4]

end MockTheta5.JTP
