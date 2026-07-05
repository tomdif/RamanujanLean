/-
# Triangular JTP, stone 3 (assembly) — part A: the `(1+z)` factorization

The `z`-side product `∏_{i≥0}(1+z qⁱ)` (stone 2) splits off its `i=0` factor `(1+z)`:

  `triProdQInf = (1 + z) · triProdQ1Inf`      (`triProdQ1Inf = ∏_{i≥1}(1+z qⁱ)`, stone 2b).

This is the factor that vanishes at `z = −1` — the mechanism by which `d/dz|_{z=−1}` of the bilateral triangular
JTP drops the cube `(q;q)³` (stone 4). Proved by splitting the finite product and matching coefficients
(`(1+z)` is `q`-degree 0). No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularProd2
import RamanujanTau.MockTheta5TriangularTheta
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- split the `i=0` factor off the finite `z`-product: `∏_{i<n+1}(1+z qⁱ) = (∏_{i<n}(1+z q^{i+1}))·(1+z)`. -/
lemma triProdQ_succ_split (n : ℕ) :
    triProdQ (n + 1) = triProdQ1 n * (1 + PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [triProdQ, Finset.prod_range_succ', ← triProdQ1, pow_zero, one_mul]

/-- the `∞`-product agrees with its own truncation at the matching degree (added factor has higher order). -/
lemma coeff_triProdQ1Inf_self (k : ℕ) : coeff k triProdQ1Inf = coeff k (triProdQ1 k) := by
  rw [coeff_triProdQ1Inf (le_refl (k + 1)), triProdQ1_succ, mul_add, mul_one, map_add]
  have h0 : coeff k (triProdQ1 k * (X ^ (k + 1) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
    rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [h0, add_zero]

/-- **The `(1+z)` factorization** `∏_{i≥0}(1+z qⁱ) = (1+z)·∏_{i≥1}(1+z qⁱ)`. -/
lemma triProdQInf_eq_split :
    triProdQInf = (1 + PowerSeries.C (LaurentPolynomial.T 1)) * triProdQ1Inf := by
  ext k
  rw [coeff_triProdQInf (le_refl (k + 1)), triProdQ_succ_split, mul_comm (triProdQ1 k)]
  simp only [add_mul, one_mul, map_add, PowerSeries.coeff_C_mul]
  rw [coeff_triProdQ1Inf_self]

/-! ### Stone 3B: the theta-side projection `zProj n triTheta = q^{n(n−1)/2}` -/

/-- the `T^κ` slice of the paired triangular term `(z^{m+1} + z^{−m})·q^{m(m+1)/2}`. -/
lemma zProj_triTerm (m : ℕ) (κ : ℤ) :
    zProj κ (triTerm m)
      = (if (m : ℤ) + 1 = κ then X ^ (m * (m + 1) / 2) else 0)
        + (if -(m : ℤ) = κ then X ^ (m * (m + 1) / 2) else 0) := by
  ext k
  rw [coeff_zProj, map_add, triTerm, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  simp only [apply_ite (fun p : PowerSeries ℤ => coeff k p), PowerSeries.coeff_X_pow, map_zero]
  by_cases hk : k = m * (m + 1) / 2
  · subst hk
    simp only [if_true, one_mul]
    rw [show ((T ((m : ℤ) + 1) + T (-(m : ℤ)) : LaurentPolynomial ℤ) κ)
          = (T ((m : ℤ) + 1) : LaurentPolynomial ℤ) κ + (T (-(m : ℤ)) : LaurentPolynomial ℤ) κ
        from Finsupp.add_apply _ _ _, LaurentPolynomial.T_apply, LaurentPolynomial.T_apply]
  · simp only [if_neg hk, zero_mul, ite_self, add_zero]
    exact Finsupp.zero_apply

/-- the `z^n` slice of the truncated triangular sum: a single term `q^{n(n−1)/2}` survives. -/
lemma zProj_triFinite (n : ℤ) (M : ℕ) (hM : n.natAbs < M) :
    zProj n (triFinite M) = X ^ ((n * (n - 1) / 2).toNat) := by
  rw [triFinite, zProj_sum]
  simp only [zProj_triTerm, Finset.sum_add_distrib]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- n < 0: first sum empty, second sum single at m = n.natAbs
    have hexp : n.natAbs * (n.natAbs + 1) / 2 = (n * (n - 1) / 2).toNat := by
      have h1 : (n.natAbs : ℤ) = -n := by omega
      have hprod : ((n.natAbs * (n.natAbs + 1) : ℕ) : ℤ) = n * (n - 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h1]; ring
      omega
    rw [Finset.sum_eq_zero (fun m _ => if_neg (by omega)), zero_add,
        Finset.sum_eq_single n.natAbs (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos (by omega), hexp]
  · -- n = 0
    subst hn
    rw [Finset.sum_eq_zero (fun m _ => if_neg (by omega)), zero_add,
        Finset.sum_eq_single 0 (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos (by norm_num)]
    norm_num
  · -- n > 0: first sum single at m = n.natAbs - 1, second sum empty
    have hexp : (n.natAbs - 1) * (n.natAbs - 1 + 1) / 2 = (n * (n - 1) / 2).toNat := by
      have h1 : ((n.natAbs - 1 : ℕ) : ℤ) = n - 1 := by omega
      have hprod : (((n.natAbs - 1) * (n.natAbs - 1 + 1) : ℕ) : ℤ) = n * (n - 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h1]; ring
      omega
    rw [Finset.sum_eq_single (n.natAbs - 1) (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, if_pos (by omega), hexp]

/-- **`zProj n triTheta = q^{n(n−1)/2}`** for every `n ∈ ℤ` — the RHS of the triangular JTP. -/
lemma zProj_triTheta (n : ℤ) : zProj n triTheta = X ^ ((n * (n - 1) / 2).toNat) := by
  ext k
  rw [coeff_zProj, coeff_triTheta (show k + 1 ≤ k + 1 + n.natAbs by omega), ← coeff_zProj,
      zProj_triFinite n (k + 1 + n.natAbs) (by omega)]

end MockTheta5.JTP
