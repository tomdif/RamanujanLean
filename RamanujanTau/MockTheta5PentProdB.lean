/-
# Euler pentagonal — stone: the second one-sided product `∏_{i≥0}(1+z q^{3i+2})`

The `z⁻¹`-side of the shifted base-`q³` JTP is `∏_{i≥1}(1+z⁻¹ q^{3i−1}) = ∏_{i≥0}(1+z⁻¹ q^{3i+2})`
(`= map invertHom pentProdBInf`). This file builds `pentProdB = ∏(1+z q^{3i+2})` — the `z`-version — via
`Φ3B` (`q↦q³`, `t↦z·q²`), with projected Cauchy

  `zProj_pentProdBInf k :  zProj k (∏(1+z q^{3i+2})) = q^{3·C(k,2)+2k} / (q³;q³)_k`

carrying `3·C(k,2)+2k = (3k²+k)/2 = e(−k)`. Mirror of `MockTheta5PentProd`/`PentProdZ` with `3i+1→3i+2`.
No `sorry`.
-/
import RamanujanTau.MockTheta5PentProdZ

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### the finite product via `Φ3B` (`t ↦ z·q²`) -/

noncomputable def Φ3B : Polynomial (PowerSeries ℤ) →+* Polynomial (PowerSeries ℤ) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp E3) (Polynomial.X * Polynomial.C (qq ^ 2))

lemma Φ3B_factor (i : ℕ) :
    Φ3B (1 + Polynomial.C (qq ^ i) * Polynomial.X)
      = 1 + Polynomial.C (qq ^ (3 * i + 2)) * Polynomial.X := by
  simp only [Φ3B, map_add, map_one, map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply, E3_X]
  ring

lemma Φ3B_qcoeff_term (n k : ℕ) :
    Φ3B (Polynomial.C (qcoeff n k) * Polynomial.X ^ k)
      = Polynomial.C (qq ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom n k)) * Polynomial.X ^ k := by
  simp only [Φ3B, qcoeff, map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply, E3_X]
  ring

theorem finite_pent_jtp_B (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ (3 * i + 2)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1),
          Polynomial.C (qq ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom n k)) * Polynomial.X ^ k := by
  have h : Φ3B (qprod n) = Φ3B (qbRHS n) := by rw [qbinom]
  rw [qprod, map_prod, qbRHS, map_sum,
      Finset.prod_congr rfl (fun i _ => Φ3B_factor i),
      Finset.sum_congr rfl (fun k _ => Φ3B_qcoeff_term n k)] at h
  exact h

/-! ### the z-outer-ring product and its z-projection -/

noncomputable def pentProdB (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 + X ^ (3 * i + 2) * PowerSeries.C (LaurentPolynomial.T 1))

lemma pentProdB_eq_sum (n : ℕ) :
    pentProdB n = ∑ k ∈ Finset.range (n + 1),
      X ^ (3 * k.choose 2 + 2 * k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
        * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  have h := congrArg Psi (finite_pent_jtp_B n)
  rw [map_prod, map_sum] at h
  rw [pentProdB,
      show (∏ i ∈ Finset.range n,
              (1 + X ^ (3 * i + 2) * PowerSeries.C (LaurentPolynomial.T 1) :
                PowerSeries (LaurentPolynomial ℤ)))
        = ∏ i ∈ Finset.range n, Psi (1 + Polynomial.C (qq ^ (3 * i + 2)) * Polynomial.X) from
        Finset.prod_congr rfl (fun i _ => by
          rw [map_add, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X]), h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Psi_C, map_pow, Psi_X, map_mul, map_pow, qq, PowerSeries.map_X, ← map_pow,
      T_one_pow, mul_assoc]

lemma pentProdB_succ (n : ℕ) :
    pentProdB (n + 1) = pentProdB n * (1 + X ^ (3 * n + 2) * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [pentProdB, pentProdB, Finset.prod_range_succ]

lemma coeff_pentProdB_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (pentProdB N) = coeff k (pentProdB M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [pentProdB_succ, mul_add, mul_one, map_add]
        have hz : coeff k (pentProdB N * (X ^ (3 * N + 2) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

noncomputable def pentProdBInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (pentProdB (k + 1))

lemma coeff_pentProdBInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k pentProdBInf = coeff k (pentProdB N) := by
  rw [pentProdBInf, coeff_mk, coeff_pentProdB_stable (Nat.lt_succ_self k) hN]

lemma zProj_pentProdB_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (3 * k.choose 2 + 2 * k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
      * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then X ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom n k) else 0 := by
  rw [show X ^ (3 * k.choose 2 + 2 * k) * PowerSeries.map (LaurentPolynomial.C) (E3 (gaussBinom n k))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom n k)) from by
      rw [map_mul, map_pow, PowerSeries.map_X], zProj_mapC_CT]

lemma zProj_pentProdB (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (pentProdB M) = X ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom M k) := by
  rw [pentProdB_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_pentProdB_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_pentProdB_term, if_pos rfl]

lemma coeff_X_E3gauss2_stable (m k : ℕ) :
    coeff m (X ^ (3 * k.choose 2 + 2 * k) * E3 (gaussBinom (m + k + 1) k))
      = coeff m (X ^ (3 * k.choose 2 + 2 * k) * Ring.inverse (E3 (qfac k))) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : 3 * k.choose 2 + 2 * k ≤ m
  · rw [if_pos hkm, if_pos hkm]; exact E3_gaussBinom_stable (m + k + 1) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

lemma zProj_pentProdBInf (k : ℕ) :
    zProj (k : ℤ) pentProdBInf = X ^ (3 * k.choose 2 + 2 * k) * Ring.inverse (E3 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_pentProdBInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_pentProdB k (m + k + 1) (by omega), coeff_X_E3gauss2_stable]

lemma zProj_pentProdB_neg {κ : ℤ} (hκ : κ < 0) : zProj κ pentProdBInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_pentProdBInf (le_refl (m + 1)), ← coeff_zProj, pentProdB_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_pentProdB_term, if_neg (by omega)])]

end MockTheta5.JTP
