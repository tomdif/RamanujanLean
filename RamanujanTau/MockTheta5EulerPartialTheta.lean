/-
# Partial-theta representation of the Euler product `(q²;q²)_∞`

`(q²;q²)_∞ = Σ_{k≥0} (−1)ᵏ q^{k(k+1)}/(q²;q²)_k` — the `z = −q` Cauchy/Euler identity, obtained from
`finite_jtp` evaluated at `z = −q` (`Polynomial.eval (−X)`): the one-sided product `∏(1−q^{2i+2})` is
`E2((q;q)_n)`, and the `n → ∞` limit lands on the Euler product `(q²;q²)_∞` while the sum side becomes the
partial theta `Σ (−1)ᵏ q^{k(k+1)}/(q²;q²)_k`. No `sorry`.
-/
import RamanujanTau.MockTheta5GaussProduct
import RamanujanTau.MockTheta5EvenOdd
import RamanujanTau.MockTheta5AltProduct

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

noncomputable def pthetaTerm (k : ℕ) : PowerSeries ℤ :=
  (-1) ^ k * (X ^ (k * (k + 1)) * Ring.inverse (E2 (qfac k)))

lemma coeff_pthetaTerm_zero {m k : ℕ} (h : m < k * (k + 1)) : coeff m (pthetaTerm k) = 0 := by
  rw [pthetaTerm, coeff_neg_pow_mul, MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h, mul_zero]

noncomputable def pthetaSum : PowerSeries ℤ :=
  mk fun m => coeff m (∑ k ∈ Finset.range (m + 1), pthetaTerm k)

lemma E2_qfac_eq_sum (n : ℕ) :
    E2 (qfac n) = ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (X ^ (k * (k + 1)) * E2 (gaussBinom n k)) := by
  have h := congrArg (Polynomial.eval (-X : PowerSeries ℤ)) (finite_jtp n)
  simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  rw [qfac, map_prod,
      show (∏ k ∈ Finset.range n, E2 (1 - X ^ (k + 1) : PowerSeries ℤ))
        = ∏ x ∈ Finset.range n, (1 + qq ^ (2 * x + 1) * -X) from
      Finset.prod_congr rfl (fun i _ => by rw [map_sub, map_one, map_pow, E2_X, qq]; ring), h]
  exact Finset.sum_congr rfl (fun k _ => by rw [qq]; ring)

lemma coeff_pterm_stable (m k : ℕ) :
    coeff m ((-1) ^ k * (X ^ (k * (k + 1)) * E2 (gaussBinom (2 * m + 2) k))) = coeff m (pthetaTerm k) := by
  rw [pthetaTerm, coeff_neg_pow_mul, coeff_neg_pow_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
  by_cases hkm : k * (k + 1) ≤ m
  · rw [if_pos hkm, if_pos hkm]
    have hkle : k ≤ m := le_trans (Nat.le_mul_of_pos_right k (by omega)) hkm
    rw [E2_gaussBinom_stable (2 * m + 2) k (by omega) (by omega)]
  · rw [if_neg hkm, if_neg hkm]

/-- **`(q²;q²)_∞ = Σ_{k≥0} (−1)ᵏ q^{k(k+1)}/(q²;q²)_k`** — a partial-theta representation of the Euler
product (the `z = −q` Cauchy identity). -/
theorem qfac2Inf_eq_pthetaSum : qfac2Inf = pthetaSum := by
  ext m
  rw [pthetaSum, coeff_mk, coeff_qfac2Inf_eq (show m + 1 ≤ 2 * m + 2 by omega), E2_qfac_eq_sum,
      map_sum, map_sum, Finset.sum_congr rfl (fun k _ => coeff_pterm_stable m k)]
  refine (Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun k _ hk => ?_)).symm
  simp only [Finset.mem_range, not_lt] at hk
  exact coeff_pthetaTerm_zero (by nlinarith [hk])
end MockTheta5.JTP
