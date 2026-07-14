/-
# Quintuple product, stone 3 (capstone): the N=0 per-term, in closed form

At `N = 0` the shift signs are `+1` and the `toNat`/`natAbs` exponents collapse to clean products:

  `zProj (−2(m+1)) thetaA = q^{(m+1)(2m+1)}`,   `zProj (2(m+1)) thetaA = q^{(m+1)(2m+3)}`,

so the per-term formula gives

  `zProj 0 (thetaA · thetaBTerm m) = (−1)^{m+1} (q^{(m+1)(3m+2)} + q^{(m+1)(3m+4)})`.

Summed over `m`, this is exactly `E2(pentSeries) = (q²;q²)_∞` — the N=0 pentagonal collapse. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintConv2
import RamanujanTau.MockTheta5QuintBracket1

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- `zProj (−2(m+1)) thetaA = q^{(m+1)(2m+1)}`. -/
lemma zProj_thetaA_neg2 (m : ℕ) :
    zProj (-(2 * ((m : ℤ) + 1))) thetaA = X ^ ((m + 1) * (2 * m + 1)) := by
  rw [zProj_thetaA]
  have h1 : (-(2 * ((m : ℤ) + 1))).natAbs = 2 * (m + 1) := by rw [Int.natAbs_neg]; omega
  have h2 : ((-(2 * ((m : ℤ) + 1))) * ((-(2 * ((m : ℤ) + 1))) + 1) / 2).toNat = (m + 1) * (2 * m + 1) := by
    have he : (-(2 * ((m : ℤ) + 1))) * ((-(2 * ((m : ℤ) + 1))) + 1) = 2 * (((m + 1) * (2 * m + 1) : ℕ) : ℤ) := by
      push_cast; ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0), Int.toNat_natCast]
  rw [h2, h1, Even.neg_one_pow (even_two_mul (m + 1)), map_one, one_mul]

/-- `zProj (2(m+1)) thetaA = q^{(m+1)(2m+3)}`. -/
lemma zProj_thetaA_pos2 (m : ℕ) :
    zProj (2 * ((m : ℤ) + 1)) thetaA = X ^ ((m + 1) * (2 * m + 3)) := by
  rw [zProj_thetaA]
  have h1 : (2 * ((m : ℤ) + 1)).natAbs = 2 * (m + 1) := by omega
  have h2 : ((2 * ((m : ℤ) + 1)) * ((2 * ((m : ℤ) + 1)) + 1) / 2).toNat = (m + 1) * (2 * m + 3) := by
    have he : (2 * ((m : ℤ) + 1)) * ((2 * ((m : ℤ) + 1)) + 1) = 2 * (((m + 1) * (2 * m + 3) : ℕ) : ℤ) := by
      push_cast; ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0), Int.toNat_natCast]
  rw [h2, h1, Even.neg_one_pow (even_two_mul (m + 1)), map_one, one_mul]

/-- **the N=0 per-term in closed form.** -/
lemma per_term_zero (m : ℕ) :
    zProj (0 : ℤ) (thetaA * thetaBTerm m)
      = PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * (X ^ ((m + 1) * (3 * m + 2)) + X ^ ((m + 1) * (3 * m + 4))) := by
  rw [zProj_thetaA_mul_thetaBTerm,
      show (0 : ℤ) - 2 * ((m : ℤ) + 1) = -(2 * ((m : ℤ) + 1)) from by ring,
      show (0 : ℤ) + 2 * ((m : ℤ) + 1) = 2 * ((m : ℤ) + 1) from by ring,
      zProj_thetaA_neg2, zProj_thetaA_pos2,
      show X ^ ((m + 1) ^ 2) * (PowerSeries.C ((-1 : ℤ) ^ (m + 1))
            * (X ^ ((m + 1) * (2 * m + 1)) + X ^ ((m + 1) * (2 * m + 3))))
          = PowerSeries.C ((-1 : ℤ) ^ (m + 1))
            * (X ^ ((m + 1) ^ 2) * X ^ ((m + 1) * (2 * m + 1))
              + X ^ ((m + 1) ^ 2) * X ^ ((m + 1) * (2 * m + 3))) from by ring,
      ← pow_add, ← pow_add,
      show (m + 1) ^ 2 + (m + 1) * (2 * m + 1) = (m + 1) * (3 * m + 2) from by ring,
      show (m + 1) ^ 2 + (m + 1) * (2 * m + 3) = (m + 1) * (3 * m + 4) from by ring]

end MockTheta5.JTP
