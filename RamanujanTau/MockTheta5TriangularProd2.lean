/-
# Triangular JTP, stone 2b: the shifted one-sided product `∏_{i≥1}(1 + z qⁱ)`

The triangular Jacobi triple product `Σ zⁿq^{n(n−1)/2} = ∏(1−qⁿ)·∏_{n≥1}(1+z qⁿ⁻¹)·∏_{n≥1}(1+z⁻¹ qⁿ)` is
**asymmetric**: the `z`-product runs `∏_{i≥0}(1+z qⁱ)` (stone 2), but the `z⁻¹`-product runs `∏_{i≥1}(1+z⁻¹ qⁱ)`
— from `i = 1`. This file builds the shifted product `∏_{i≥1}(1+z qⁱ)`; its `z⁻¹` mirror (`map invertHom`) is
the second factor of the bilateral assembly (stone 3).

The shift multiplies the `tᵏ` weight by `qᵏ` (`∏_{i≥1}(1+tqⁱ) = Σ_k q^{C(k,2)+k} tᵏ/(q;q)_k`, and
`C(k,2)+k = C(k+1,2)`), so its projected Cauchy coefficient is

  `zProj_triProdQ1Inf k :  zProj k (∏_{i≥1}(1+z qⁱ)) = q^{C(k+1,2)} / (q;q)_k`.

With stone 2's `q^{C(k,2)}/(q;q)_k`, the z-Cauchy convolution collapses to `X^{C(N,2)}·rectInf N`, whence
`durfee_rect_base` (already proven, base q) gives `X^{C(N,2)}/(q;q)_∞`. No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularProd

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the finite shifted product `∏_{i<n}(1 + z q^{i+1})` in the `q`-outer ring. -/
noncomputable def triProdQ1 (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 + X ^ (i + 1) * PowerSeries.C (LaurentPolynomial.T 1))

/-- transport the shifted q-binomial (`qbinom` under `t ↦ q·t`) to the `q`-outer ring. -/
lemma triProdQ1_eq_sum (n : ℕ) :
    triProdQ1 n = ∑ k ∈ Finset.range (n + 1),
      X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  have hpoly : (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ (i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k * qq ^ k) * Polynomial.X ^ k := by
    rw [← qprod_comp, qbinom, comp_qbRHS]
  have h := congrArg Psi hpoly
  rw [map_prod, map_sum] at h
  rw [triProdQ1,
      show (∏ i ∈ Finset.range n,
              (1 + X ^ (i + 1) * PowerSeries.C (LaurentPolynomial.T 1) :
                PowerSeries (LaurentPolynomial ℤ)))
        = ∏ i ∈ Finset.range n, Psi (1 + Polynomial.C (qq ^ (i + 1)) * Polynomial.X) from
        Finset.prod_congr rfl (fun i _ => by
          rw [map_add, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X]), h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Psi_C, map_pow, Psi_X, ← map_pow, T_one_pow, qcoeff,
      mul_right_comm (qq ^ (k.choose 2)) (gaussBinom n k) (qq ^ k), ← pow_add, ← choose_two_succ,
      map_mul, map_pow, qq, PowerSeries.map_X, mul_assoc]

lemma triProdQ1_succ (n : ℕ) :
    triProdQ1 (n + 1) = triProdQ1 n * (1 + X ^ (n + 1) * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [triProdQ1, triProdQ1, Finset.prod_range_succ]

lemma coeff_triProdQ1_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (triProdQ1 N) = coeff k (triProdQ1 M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [triProdQ1_succ, mul_add, mul_one, map_add]
        have hz : coeff k (triProdQ1 N * (X ^ (N + 1) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥1}(1 + z qⁱ)`** as a formal power series (shifted one-sided triangular Jacobi product). -/
noncomputable def triProdQ1Inf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (triProdQ1 (k + 1))

lemma coeff_triProdQ1Inf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k triProdQ1Inf = coeff k (triProdQ1 N) := by
  rw [triProdQ1Inf, coeff_mk, coeff_triProdQ1_stable (Nat.lt_succ_self k) hN]

lemma zProj_triProdQ1_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
      * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then X ^ ((k + 1).choose 2) * gaussBinom n k else 0 := by
  rw [show X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        = PowerSeries.map (LaurentPolynomial.C) (X ^ ((k + 1).choose 2) * gaussBinom n k) from by
      rw [map_mul, map_pow, PowerSeries.map_X], zProj_mapC_CT]

lemma zProj_triProdQ1 (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (triProdQ1 M) = X ^ ((k + 1).choose 2) * gaussBinom M k := by
  rw [triProdQ1_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_triProdQ1_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_triProdQ1_term, if_pos rfl]

lemma coeff_X_gauss1_stable (m k : ℕ) :
    coeff m (X ^ ((k + 1).choose 2) * gaussBinom (m + k + 1) k)
      = coeff m (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : (k + 1).choose 2 ≤ m
  · rw [if_pos hkm, if_pos hkm]; exact gaussBinom_stable (m + k + 1) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

/-- **The shifted one-sided Cauchy identity, projected**: the `zᵏ`-coefficient of `∏_{i≥1}(1+z qⁱ)` is
`q^{C(k+1,2)} / (q;q)_k`. -/
lemma zProj_triProdQ1Inf (k : ℕ) :
    zProj (k : ℤ) triProdQ1Inf = X ^ ((k + 1).choose 2) * Ring.inverse (qfac k) := by
  ext m
  rw [coeff_zProj, coeff_triProdQ1Inf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_triProdQ1 k (m + k + 1) (by omega), coeff_X_gauss1_stable]

lemma zProj_triProdQ1_neg {κ : ℤ} (hκ : κ < 0) : zProj κ triProdQ1Inf = 0 := by
  ext m
  rw [coeff_zProj, coeff_triProdQ1Inf (le_refl (m + 1)), ← coeff_zProj, triProdQ1_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_triProdQ1_term, if_neg (by omega)])]

end MockTheta5.JTP
