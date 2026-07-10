/-
# Quintuple product, stone 2: the base-`q` `z`-side product `∏_{i≥1}(1 − z qⁱ)`

The quintuple product side carries `∏_{n≥1}(1 − z qⁿ) = ∏_{i≥1}(1 − z qⁱ)`. It is the shifted one-sided
triangular product `triProdQ1Inf = ∏_{i≥1}(1 + z qⁱ)` under the sign `z ↦ −z`, so its `zᵏ` coefficient is the
same shifted-Cauchy value carrying `(−1)ᵏ`:

  `zProj_qzProdAInf k :  zProj k (∏_{i≥1}(1 − z qⁱ)) = (−1)ᵏ · q^{C(k+1,2)} / (q;q)_k`.

Transport mirrors `triProdQ1`'s, plus the sign hom `negX : X ↦ −X` on `Polynomial (PowerSeries ℤ)` applied to
the shifted q-binomial (which turns each `tᵏ` weight into `(−1)ᵏ tᵏ`). The sign is kept **outside** `map C` as
the monomial factor `(− C(T 1))ᵏ`, converted to the signed Laurent monomial `C((−1)ᵏ · T k)` only inside the
`zProj` computation (`negCT_pow`, `zProj_mapC_signedCT`). No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularProd2

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the sign substitution `t ↦ −t` on `Polynomial (PowerSeries ℤ)`. -/
noncomputable def negX : Polynomial (PowerSeries ℤ) →+* Polynomial (PowerSeries ℤ) :=
  Polynomial.eval₂RingHom Polynomial.C (-Polynomial.X)

@[simp] lemma negX_C (a : PowerSeries ℤ) : negX (Polynomial.C a) = Polynomial.C a := by simp [negX]

@[simp] lemma negX_X : negX Polynomial.X = -Polynomial.X := by simp [negX]

/-- `(− z)ᵏ` as a signed Laurent monomial: `(− C(T 1))ᵏ = C((−1)ᵏ · T k)`. -/
lemma negCT_pow (k : ℕ) :
    (- PowerSeries.C (LaurentPolynomial.T (1 : ℤ))) ^ k
      = PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_neg, ← map_mul, mul_assoc,
        show LaurentPolynomial.T (k : ℤ) * LaurentPolynomial.T 1 = LaurentPolynomial.T ((k : ℤ) + 1) from by
          rw [← LaurentPolynomial.T_add],
        ← map_neg, ← neg_mul, ← map_neg,
        show (-(-1 : ℤ) ^ k) = (-1 : ℤ) ^ (k + 1) from by rw [pow_succ]; ring,
        show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) from by push_cast; ring]

/-- the finite signed shifted product `∏_{i<n}(1 − z q^{i+1})` in the `q`-outer ring. -/
noncomputable def qzProdA (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 - X ^ (i + 1) * PowerSeries.C (LaurentPolynomial.T 1))

/-- transport the sign-flipped shifted q-binomial: `∏(1 − z q^{i+1}) = Σ q^{C(k+1,2)} [n,k]_q (−z)ᵏ`. -/
lemma qzProdA_eq_sum (n : ℕ) :
    qzProdA n = ∑ k ∈ Finset.range (n + 1),
      X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        * (- PowerSeries.C (LaurentPolynomial.T (1 : ℤ))) ^ k := by
  -- the unsigned shifted q-binomial identity in `Polynomial (PowerSeries ℤ)`
  have hpoly : (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ (i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k * qq ^ k) * Polynomial.X ^ k := by
    rw [← qprod_comp, qbinom, comp_qbRHS]
  -- sign-flip both sides via `negX`
  have hL : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (i + 1)) * Polynomial.X))
      = negX (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ (i + 1)) * Polynomial.X)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_add, map_one, map_mul negX, negX_C, negX_X]; ring)
  have hR : (∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k * qq ^ k) * (-Polynomial.X) ^ k)
      = negX (∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k * qq ^ k) * Polynomial.X ^ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [map_mul negX, negX_C, map_pow negX, negX_X])
  have psigned : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k * qq ^ k) * (-Polynomial.X) ^ k := by
    rw [hL, hR, hpoly]
  -- transport to the `q`-outer ring via `Psi`
  have hq : qzProdA n = Psi (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (i + 1)) * Polynomial.X)) := by
    rw [qzProdA, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [map_sub, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X])
  rw [hq, psigned, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul Psi, Psi_C, map_pow Psi, map_neg, Psi_X, qcoeff,
      show (qq ^ (k.choose 2) * gaussBinom n k) * qq ^ k = qq ^ ((k + 1).choose 2) * gaussBinom n k from by
        rw [mul_right_comm, ← pow_add, ← choose_two_succ],
      map_mul (PowerSeries.map (LaurentPolynomial.C)),
      map_pow (PowerSeries.map (LaurentPolynomial.C)), qq, PowerSeries.map_X]

lemma qzProdA_succ (n : ℕ) :
    qzProdA (n + 1) = qzProdA n * (1 - X ^ (n + 1) * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [qzProdA, qzProdA, Finset.prod_range_succ]

lemma coeff_qzProdA_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (qzProdA N) = coeff k (qzProdA M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [qzProdA_succ, mul_sub, mul_one, map_sub]
        have hz : coeff k (qzProdA N * (X ^ (N + 1) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥1}(1 − z qⁱ)`** as a formal power series. -/
noncomputable def qzProdAInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (qzProdA (k + 1))

lemma coeff_qzProdAInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k qzProdAInf = coeff k (qzProdA N) := by
  rw [qzProdAInf, coeff_mk, coeff_qzProdA_stable (Nat.lt_succ_self k) hN]

/-- signed variant of `zProj_mapC_CT`: `zProj κ (map C a · C((−1)ᵏ·T k)) = if k=κ then (−1)ᵏ·a else 0`. -/
lemma zProj_mapC_signedCT (a : PowerSeries ℤ) (k : ℕ) (κ : ℤ) :
    zProj κ (PowerSeries.map (LaurentPolynomial.C) a
        * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then (-1 : PowerSeries ℤ) ^ k * a else 0 := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
  split_ifs with h
  · rw [show ((-1 : PowerSeries ℤ)) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) from by
          rw [map_pow, map_neg, map_one],
        PowerSeries.coeff_C_mul, mul_comm]
  · simp

lemma zProj_qzProdA_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
      * (- PowerSeries.C (LaurentPolynomial.T (1 : ℤ))) ^ k)
      = if (k : ℤ) = κ then (-1 : PowerSeries ℤ) ^ k * (X ^ ((k + 1).choose 2) * gaussBinom n k) else 0 := by
  rw [negCT_pow,
      show X ^ ((k + 1).choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        = PowerSeries.map (LaurentPolynomial.C) (X ^ ((k + 1).choose 2) * gaussBinom n k) from by
        rw [map_mul, map_pow, PowerSeries.map_X],
      zProj_mapC_signedCT]

lemma zProj_qzProdA (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (qzProdA M)
      = (-1 : PowerSeries ℤ) ^ k * (X ^ ((k + 1).choose 2) * gaussBinom M k) := by
  rw [qzProdA_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_qzProdA_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_qzProdA_term, if_pos rfl]

lemma coeff_X_signed_gauss1_stable (m k : ℕ) :
    coeff m ((-1 : PowerSeries ℤ) ^ k * (X ^ ((k + 1).choose 2) * gaussBinom (m + k + 1) k))
      = coeff m ((-1 : PowerSeries ℤ) ^ k * (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k))) := by
  rw [show ((-1 : PowerSeries ℤ)) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) from by rw [map_pow, map_neg, map_one],
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_X_gauss1_stable]

/-- **The signed shifted one-sided Cauchy identity, projected**: the `zᵏ`-coefficient of `∏_{i≥1}(1 − z qⁱ)`
is `(−1)ᵏ q^{C(k+1,2)} / (q;q)_k`. -/
lemma zProj_qzProdAInf (k : ℕ) :
    zProj (k : ℤ) qzProdAInf
      = (-1 : PowerSeries ℤ) ^ k * (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_qzProdAInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_qzProdA k (m + k + 1) (by omega), coeff_X_signed_gauss1_stable]

lemma zProj_qzProdA_neg {κ : ℤ} (hκ : κ < 0) : zProj κ qzProdAInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_qzProdAInf (le_refl (m + 1)), ← coeff_zProj, qzProdA_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_qzProdA_term, if_neg (by omega)])]

/-! ### The unshifted twin `∏_{i≥0}(1 − z qⁱ)` — its `z⁻¹` mirror is the quintuple's `∏(1 − z⁻¹ qⁿ⁻¹)` factor. -/

/-- the finite unshifted signed product `∏_{i<n}(1 − z qⁱ)` in the `q`-outer ring. -/
noncomputable def qzProdB (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 - X ^ i * PowerSeries.C (LaurentPolynomial.T 1))

/-- transport the sign-flipped q-binomial: `∏(1 − z qⁱ) = Σ q^{C(k,2)} [n,k]_q (−z)ᵏ`. -/
lemma qzProdB_eq_sum (n : ℕ) :
    qzProdB n = ∑ k ∈ Finset.range (n + 1),
      X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        * (- PowerSeries.C (LaurentPolynomial.T (1 : ℤ))) ^ k := by
  have hpoly := qbinom n
  rw [qprod, qbRHS] at hpoly
  have hL : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ i) * Polynomial.X))
      = negX (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ i) * Polynomial.X)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_add, map_one, map_mul negX, negX_C, negX_X]; ring)
  have hR : (∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k) * (-Polynomial.X) ^ k)
      = negX (∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k) * Polynomial.X ^ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [map_mul negX, negX_C, map_pow negX, negX_X])
  have psigned : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ i) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1), Polynomial.C (qcoeff n k) * (-Polynomial.X) ^ k := by
    rw [hL, hR, hpoly]
  have hq : qzProdB n = Psi (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ i) * Polynomial.X)) := by
    rw [qzProdB, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [map_sub, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X])
  rw [hq, psigned, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul Psi, Psi_C, map_pow Psi, map_neg, Psi_X, qcoeff,
      map_mul (PowerSeries.map (LaurentPolynomial.C)),
      map_pow (PowerSeries.map (LaurentPolynomial.C)), qq, PowerSeries.map_X]

lemma qzProdB_succ (n : ℕ) :
    qzProdB (n + 1) = qzProdB n * (1 - X ^ n * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [qzProdB, qzProdB, Finset.prod_range_succ]

lemma coeff_qzProdB_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (qzProdB N) = coeff k (qzProdB M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [qzProdB_succ, mul_sub, mul_one, map_sub]
        have hz : coeff k (qzProdB N * (X ^ N * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥0}(1 − z qⁱ)`** as a formal power series. -/
noncomputable def qzProdBInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (qzProdB (k + 1))

lemma coeff_qzProdBInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k qzProdBInf = coeff k (qzProdB N) := by
  rw [qzProdBInf, coeff_mk, coeff_qzProdB_stable (Nat.lt_succ_self k) hN]

lemma zProj_qzProdB_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
      * (- PowerSeries.C (LaurentPolynomial.T (1 : ℤ))) ^ k)
      = if (k : ℤ) = κ then (-1 : PowerSeries ℤ) ^ k * (X ^ (k.choose 2) * gaussBinom n k) else 0 := by
  rw [negCT_pow,
      show X ^ (k.choose 2) * PowerSeries.map (LaurentPolynomial.C) (gaussBinom n k)
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (k.choose 2) * gaussBinom n k) from by
        rw [map_mul, map_pow, PowerSeries.map_X],
      zProj_mapC_signedCT]

lemma zProj_qzProdB (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (qzProdB M)
      = (-1 : PowerSeries ℤ) ^ k * (X ^ (k.choose 2) * gaussBinom M k) := by
  rw [qzProdB_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_qzProdB_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_qzProdB_term, if_pos rfl]

lemma coeff_X_signed_gauss_stable (m k : ℕ) :
    coeff m ((-1 : PowerSeries ℤ) ^ k * (X ^ (k.choose 2) * gaussBinom (m + k + 1) k))
      = coeff m ((-1 : PowerSeries ℤ) ^ k * (X ^ (k.choose 2) * Ring.inverse (qfac k))) := by
  rw [show ((-1 : PowerSeries ℤ)) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) from by rw [map_pow, map_neg, map_one],
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_X_gauss_stable]

/-- **The unshifted signed one-sided Cauchy identity, projected**: the `zᵏ`-coefficient of `∏_{i≥0}(1 − z qⁱ)`
is `(−1)ᵏ q^{C(k,2)} / (q;q)_k`. -/
lemma zProj_qzProdBInf (k : ℕ) :
    zProj (k : ℤ) qzProdBInf
      = (-1 : PowerSeries ℤ) ^ k * (X ^ (k.choose 2) * Ring.inverse (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_qzProdBInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_qzProdB k (m + k + 1) (by omega), coeff_X_signed_gauss_stable]

lemma zProj_qzProdB_neg {κ : ℤ} (hκ : κ < 0) : zProj κ qzProdBInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_qzProdBInf (le_refl (m + 1)), ← coeff_zProj, qzProdB_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_qzProdB_term, if_neg (by omega)])]

end MockTheta5.JTP
