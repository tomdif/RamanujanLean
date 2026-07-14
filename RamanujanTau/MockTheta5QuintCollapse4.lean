/-
# Quintuple product, stone 3 (capstone): the N=0 collapse

  **`zProj 0 (thetaA · thetaB) = (q²;q²)_∞`** — the base case of `thetaA·thetaB = qfac2InfL·quintTheta`
  (at `N=0`, `zProj 0 quintTheta = 1`).

Proof: `coeff_zProj_thetaA_thetaB` turns the LHS into `coeff k 1 + Σ_{m<k+1} coeff k (zProj 0 (thetaA·
thetaBTerm m))`; by `per_term_zero_eq_pent` each term is `coeff k (E2(map evm1 (pentTermP m)))`. The RHS is
`coeff k (E2 pentSeries)` (`qfac2Inf = E2 qfacInf = E2 pentSeries` by `euler_pentagonal`). Splitting on `2∣k`
(`coeff_E2`), the two sides match term by term, with the extra `m` beyond `k/2` contributing zero
(`coeff_pentTermP_zero`). No `sorry`. -/
import RamanujanTau.MockTheta5QuintCollapse3
import RamanujanTau.MockTheta5QuintConv3
import RamanujanTau.MockTheta5EulerPentagonal

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- `zProj 0 thetaA = 1` (the `n=0` term of `thetaA`). -/
lemma zProj_zero_thetaA : zProj (0 : ℤ) thetaA = 1 := by
  rw [zProj_thetaA]; norm_num

/-- **the N=0 pentagonal collapse.** -/
theorem zProj_zero_thetaA_thetaB : zProj (0 : ℤ) (thetaA * thetaB) = qfac2Inf := by
  have hq2 : qfac2Inf = E2 pentSeries := congrArg E2 euler_pentagonal
  rw [hq2]
  ext k
  rw [coeff_zProj_thetaA_thetaB, map_add, zProj_zero_thetaA, map_sum, coeff_E2]
  simp only [per_term_zero_eq_pent, coeff_E2]
  by_cases hk : 2 ∣ k
  · simp only [if_pos hk]
    have hrhs : coeff (k / 2) pentSeries
        = evm1 (coeff (k / 2) (1 : PowerSeries (LaurentPolynomial ℤ)))
          + ∑ m ∈ Finset.range (k / 2 + 1), coeff (k / 2) (PowerSeries.map evm1 (pentTermP m)) := by
      rw [pentSeries, PowerSeries.coeff_map, coeff_pentTheta (Nat.le_refl (k / 2 + 1)), pentFiniteP,
          map_add, map_sum, map_add, map_sum]
      simp only [PowerSeries.coeff_map]
    rw [hrhs]
    congr 1
    · rw [PowerSeries.coeff_one, PowerSeries.coeff_one]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · rw [if_neg hk0, if_neg (by omega : k / 2 ≠ 0), map_zero]
    · symm
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [PowerSeries.coeff_map,
            coeff_pentTermP_zero (by have := pentExp_ge m; omega), map_zero]
  · simp only [if_neg hk, Finset.sum_const_zero, add_zero]
    rw [PowerSeries.coeff_one, if_neg (by rintro rfl; exact hk (dvd_zero 2))]

end MockTheta5.JTP
