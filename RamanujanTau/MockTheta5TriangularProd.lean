/-
# Triangular Jacobi triple product, stone 2: the one-sided product `∏_{i≥0}(1 + z qⁱ)`

The base-`q` analogue of the square `jtpProdQInf` (`∏(1+z q^{2i+1})`, from `finite_jtp`). Here we transport the
base-`q` q-binomial theorem `qbinom` (`∏_{i<n}(1+qⁱt) = Σ q^{C(k,2)}[n,k]_q tᵏ`) into the `z`-outer ring
`ℤ[z;z⁻¹]⟦q⟧` via the variable-swap ring hom `Psi`, then read off the `n→∞` limit by the `z`-degree
projection `zProj`. The key output is

  `zProj_triProdQInf` :  the `zᵏ`-coefficient of `∏_{i≥0}(1+z qⁱ)` is `q^{C(k,2)} / (q;q)_k`

— i.e. the one-sided Euler/Cauchy identity in projected form (the base-`q` `euler_cauchy`, via the base-`q`
Gaussian-binomial limit `gaussBinom_stable`). This is exactly what stone 3 (the bilateral assembly) needs.
Mirrors `MockTheta5ClassicalJTP` line-for-line but at base `q` (exponent `C(k,2)` not `k²`, factor `X^i` not
`X^{2i+1}`, no `E2` reweighting). No `sorry`.
-/
import RamanujanTau.MockTheta5ClassicalJTP
import RamanujanTau.MockTheta5EulerCauchy

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the finite one-sided product `∏_{i<n}(1 + z qⁱ)` in the `q`-outer ring. -/
noncomputable def triProdQ (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 + X ^ i * PowerSeries.C (LaurentPolynomial.T 1))

/-- transport `qbinom` to the `q`-outer ring: `∏(1+z qⁱ) = Σ_{k≤n} q^{C(k,2)} [n,k]_q zᵏ`. -/
lemma triProdQ_eq_sum (n : ℕ) :
    triProdQ n = ∑ k ∈ Finset.range (n + 1),
      X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  have h := congrArg Psi (qbinom n)
  rw [qprod, qbRHS, map_prod, map_sum] at h
  rw [triProdQ,
      show (∏ i ∈ Finset.range n,
              (1 + X ^ i * PowerSeries.C (LaurentPolynomial.T 1) :
                PowerSeries (LaurentPolynomial ℤ)))
        = ∏ i ∈ Finset.range n, Psi (1 + Polynomial.C (qq ^ i) * Polynomial.X) from
        Finset.prod_congr rfl (fun i _ => by
          rw [map_add, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X]), h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Psi_C, map_pow, Psi_X, qcoeff, map_mul, map_pow, qq, PowerSeries.map_X,
      ← map_pow, T_one_pow, mul_assoc]

lemma triProdQ_succ (n : ℕ) :
    triProdQ (n + 1) = triProdQ n * (1 + X ^ n * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [triProdQ, triProdQ, Finset.prod_range_succ]

lemma coeff_triProdQ_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (triProdQ N) = coeff k (triProdQ M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [triProdQ_succ, mul_add, mul_one, map_add]
        have hz : coeff k (triProdQ N * (X ^ N * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥0}(1 + z qⁱ)`** as a formal power series (the one-sided triangular Jacobi product). -/
noncomputable def triProdQInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (triProdQ (k + 1))

lemma coeff_triProdQInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k triProdQInf = coeff k (triProdQ N) := by
  rw [triProdQInf, coeff_mk, coeff_triProdQ_stable (Nat.lt_succ_self k) hN]

/-! ### z-degree projection of the product, and the limit to the Cauchy sum -/

lemma zProj_triProdQ_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
      * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then X ^ (k.choose 2) * gaussBinom n k else 0 := by
  rw [show X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (k.choose 2) * gaussBinom n k) from by
      rw [map_mul, map_pow, PowerSeries.map_X], zProj_mapC_CT]

lemma zProj_triProdQ (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (triProdQ M) = X ^ (k.choose 2) * gaussBinom M k := by
  rw [triProdQ_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_triProdQ_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_triProdQ_term, if_pos rfl]

lemma coeff_X_gauss_stable (m k : ℕ) :
    coeff m (X ^ (k.choose 2) * gaussBinom (m + k + 1) k)
      = coeff m (X ^ (k.choose 2) * Ring.inverse (qfac k)) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : k.choose 2 ≤ m
  · rw [if_pos hkm, if_pos hkm]; exact gaussBinom_stable (m + k + 1) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

/-- **The one-sided Euler/Cauchy identity, projected**: the `zᵏ`-coefficient of `∏_{i≥0}(1+z qⁱ)` is
`q^{C(k,2)} / (q;q)_k`. -/
lemma zProj_triProdQInf (k : ℕ) :
    zProj (k : ℤ) triProdQInf = X ^ (k.choose 2) * Ring.inverse (qfac k) := by
  ext m
  rw [coeff_zProj, coeff_triProdQInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_triProdQ k (m + k + 1) (by omega), coeff_X_gauss_stable]

lemma zProj_triProdQ_neg {κ : ℤ} (hκ : κ < 0) : zProj κ triProdQInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_triProdQInf (le_refl (m + 1)), ← coeff_zProj, triProdQ_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_triProdQ_term, if_neg (by omega)])]

end MockTheta5.JTP
