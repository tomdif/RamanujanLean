/-
# Quintuple product, stone 3 (capstone): the stabilized per-term sum

`thetaB`'s terms are each localized at a single q-degree, so at `coeff k` the product `thetaA·thetaB` only
sees the truncation `thetaBFinite (k+1)`:

  `coeff k (thetaA·thetaB) = coeff k (thetaA·thetaBFinite (k+1))`,

turning the infinite z-convolution into a **finite** sum of the per-term shifts:

  `coeff k (zProj N (thetaA·thetaB)) = coeff k (zProj N thetaA + Σ_{m<k+1} zProj N (thetaA·thetaBTerm m))`.

With `zProj_thetaA_mul_thetaBTerm` this is a finite theta-A sum; its collapse to `(q²;q²)_∞·[quintTheta coeff]`
by Euler's pentagonal theorem is the remaining step. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintConv2

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- at `coeff k` the product only sees `thetaB`'s truncation `thetaBFinite (k+1)`. -/
lemma coeff_thetaA_thetaB (k : ℕ) :
    coeff k (thetaA * thetaB) = coeff k (thetaA * thetaBFinite (k + 1)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  congr 1
  exact coeff_thetaB (by omega)

/-- **the stabilized per-term sum** (at each `coeff k`). -/
lemma coeff_zProj_thetaA_thetaB (N : ℤ) (k : ℕ) :
    coeff k (zProj N (thetaA * thetaB))
      = coeff k (zProj N thetaA + ∑ m ∈ Finset.range (k + 1), zProj N (thetaA * thetaBTerm m)) := by
  rw [coeff_zProj, coeff_thetaA_thetaB, ← coeff_zProj, thetaBFinite, mul_add, mul_one, Finset.mul_sum,
      zProj_add, zProj_sum]

end MockTheta5.JTP
