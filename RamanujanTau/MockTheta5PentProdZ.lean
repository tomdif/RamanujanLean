/-
# Euler pentagonal — stone: the one-sided product `∏_{i≥0}(1+z q^{3i+1})` in the z-outer ring

Base-`q³` analogue of `MockTheta5TriangularProd`. Transports `finite_pent_jtp` into `ℤ[z;z⁻¹]⟦q⟧` via the
variable-swap `Psi`, reads off the `n→∞` limit by the `z`-degree projection `zProj`. Payoff:

  `zProj_pentProdAInf k :  zProj k (∏_{i≥0}(1+z q^{3i+1})) = q^{3·C(k,2)+k} / (q³;q³)_k`,

the shifted base-`q³` Cauchy coefficient (`3·C(k,2)+k = e(k)`, the pentagonal exponent). Needs the base-`q³`
Gaussian-binomial limit `E3_gaussBinom_stable`, proved via `PowerSeries.coeff_expand`. No `sorry`.
-/
import RamanujanTau.MockTheta5PentProd
import RamanujanTau.MockTheta5ClassicalJTP
import RamanujanTau.MockTheta5EulerCauchy

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### base-`q³` Gaussian-binomial stability -/

lemma coeff_E3 (m : ℕ) (f : PowerSeries ℤ) :
    coeff m (E3 f) = if 3 ∣ m then coeff (m / 3) f else 0 := by
  have h : E3 f = PowerSeries.expand 3 (by norm_num) f := rfl
  rw [h, PowerSeries.coeff_expand]

lemma E3_inverse_qfac (k : ℕ) : E3 (Ring.inverse (qfac k)) = Ring.inverse (E3 (qfac k)) := by
  have hu2 : IsUnit (E3 (qfac k)) := (isUnit_qfac k).map E3
  have h1 : E3 (qfac k) * E3 (Ring.inverse (qfac k)) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel (qfac k) (isUnit_qfac k), map_one]
  calc E3 (Ring.inverse (qfac k))
      = Ring.inverse (E3 (qfac k)) * (E3 (qfac k) * E3 (Ring.inverse (qfac k))) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu2, one_mul]
    _ = Ring.inverse (E3 (qfac k)) := by rw [h1, mul_one]

/-- **base-`q³` Gaussian-binomial limit** `[N,k]_{q³} → 1/(q³;q³)_k`, valid up to q-degree `3(N-k+1)`. -/
lemma E3_gaussBinom_stable (N k : ℕ) (hk : k ≤ N) {m : ℕ} (hm : m < 3 * (N - k + 1)) :
    coeff m (E3 (gaussBinom N k)) = coeff m (Ring.inverse (E3 (qfac k))) := by
  rw [← E3_inverse_qfac, coeff_E3, coeff_E3]
  by_cases h3 : 3 ∣ m
  · rw [if_pos h3, if_pos h3]
    exact gaussBinom_stable N k hk (by omega)
  · rw [if_neg h3, if_neg h3]

/-! ### the one-sided product and its z-projection -/

/-- the finite product `∏_{i<n}(1 + z q^{3i+1})` in the `q`-outer ring. -/
noncomputable def pentProdA (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 + X ^ (3 * i + 1) * PowerSeries.C (LaurentPolynomial.T 1))

lemma pentProdA_eq_sum (n : ℕ) :
    pentProdA n = ∑ k ∈ Finset.range (n + 1),
      X ^ (3 * k.choose 2 + k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
        * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  have h := congrArg Psi (finite_pent_jtp n)
  rw [map_prod, map_sum] at h
  rw [pentProdA,
      show (∏ i ∈ Finset.range n,
              (1 + X ^ (3 * i + 1) * PowerSeries.C (LaurentPolynomial.T 1) :
                PowerSeries (LaurentPolynomial ℤ)))
        = ∏ i ∈ Finset.range n, Psi (1 + Polynomial.C (qq ^ (3 * i + 1)) * Polynomial.X) from
        Finset.prod_congr rfl (fun i _ => by
          rw [map_add, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X]), h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Psi_C, map_pow, Psi_X, map_mul, map_pow, qq, PowerSeries.map_X, ← map_pow,
      T_one_pow, mul_assoc]

lemma pentProdA_succ (n : ℕ) :
    pentProdA (n + 1) = pentProdA n * (1 + X ^ (3 * n + 1) * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [pentProdA, pentProdA, Finset.prod_range_succ]

lemma coeff_pentProdA_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (pentProdA N) = coeff k (pentProdA M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [pentProdA_succ, mul_add, mul_one, map_add]
        have hz : coeff k (pentProdA N * (X ^ (3 * N + 1) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥0}(1 + z q^{3i+1})`** as a formal power series. -/
noncomputable def pentProdAInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (pentProdA (k + 1))

lemma coeff_pentProdAInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k pentProdAInf = coeff k (pentProdA N) := by
  rw [pentProdAInf, coeff_mk, coeff_pentProdA_stable (Nat.lt_succ_self k) hN]

lemma zProj_pentProdA_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (3 * k.choose 2 + k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
      * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then X ^ (3 * k.choose 2 + k) * E3 (gaussBinom n k) else 0 := by
  rw [show X ^ (3 * k.choose 2 + k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (3 * k.choose 2 + k) * E3 (gaussBinom n k)) from by
      rw [map_mul, map_pow, PowerSeries.map_X], zProj_mapC_CT]

lemma zProj_pentProdA (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (pentProdA M) = X ^ (3 * k.choose 2 + k) * E3 (gaussBinom M k) := by
  rw [pentProdA_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_pentProdA_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_pentProdA_term, if_pos rfl]

lemma coeff_X_E3gauss_stable (m k : ℕ) :
    coeff m (X ^ (3 * k.choose 2 + k) * E3 (gaussBinom (m + k + 1) k))
      = coeff m (X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k))) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : 3 * k.choose 2 + k ≤ m
  · rw [if_pos hkm, if_pos hkm]; exact E3_gaussBinom_stable (m + k + 1) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

/-- **the shifted base-`q³` Cauchy identity, projected**: `zᵏ`-coeff of `∏(1+z q^{3i+1})` is
`q^{3·C(k,2)+k} / (q³;q³)_k`. -/
lemma zProj_pentProdAInf (k : ℕ) :
    zProj (k : ℤ) pentProdAInf = X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_pentProdAInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_pentProdA k (m + k + 1) (by omega), coeff_X_E3gauss_stable]

lemma zProj_pentProdA_neg {κ : ℤ} (hκ : κ < 0) : zProj κ pentProdAInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_pentProdAInf (le_refl (m + 1)), ← coeff_zProj, pentProdA_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_pentProdA_term, if_neg (by omega)])]

end MockTheta5.JTP
