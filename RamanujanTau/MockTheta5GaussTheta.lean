/-
# A Gauss/Jacobi theta evaluation — the `z = 1` corollary of the bilateral JTP

Specialising the bilateral Jacobi triple product `qfac2InfL · SZ · SZinv = bilateralTheta` at `z = 1`
(applying the augmentation `ε : ℤ[z;z⁻¹] → ℤ`, `zᵏ ↦ 1`, coefficientwise) collapses the two one-sided
factors to the same diagonal partial theta and yields

  `Σ_{n∈ℤ} q^{n²} = (q²;q²)_∞ · (Σ_{k≥0} q^{k²}/(q²;q²)_k)²`,

a classical theta-function identity. The proof is just `PowerSeries.map ε` applied to the JTP, using
that `ε` fixes the (z-degree-0) prefactor and identifies the `z` and `z⁻¹` Cauchy sums. No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- evaluation `z ↦ 1` (the augmentation `Σ aₖ zᵏ ↦ Σ aₖ`) of `ℤ[z;z⁻¹]`, as a `RingHom`. -/
noncomputable def ev1 : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

@[simp] lemma ev1_T (k : ℤ) : ev1 (T k) = 1 := by rw [ev1, LaurentPolynomial.eval₂_T]; simp

@[simp] lemma ev1_C (a : ℤ) : ev1 (LaurentPolynomial.C a) = a := by
  rw [ev1, ← Polynomial.toLaurent_C, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_C,
      RingHom.id_apply]

/-- `z ↦ 1` of the `k`-th `SZ` Cauchy term at q-degree `m` is the Cauchy coefficient `szc m k`. -/
lemma ev1_coeff_SZterm (m k : ℕ) : ev1 (coeff m (SZterm k)) = szc m k := by
  rw [SZterm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, ev1.map_mul, ev1_C,
      ev1_T, mul_one]; rfl

/-- `z ↦ 1` of the `k`-th `SZinv` Cauchy term — the same `szc m k` (the `z⁻ᵏ` becomes `1` too). -/
lemma ev1_coeff_SZinvTerm (m k : ℕ) : ev1 (coeff m (SZinvTerm k)) = szc m k := by
  rw [SZinvTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, ev1.map_mul, ev1_C,
      ev1_T, mul_one]; rfl

/-- `map ev1` sends the lifted prefactor back to `(q²;q²)_∞`. -/
lemma map_ev1_qfac2InfL : PowerSeries.map ev1 qfac2InfL = qfac2Inf := by
  refine PowerSeries.ext fun m => ?_
  simp only [qfac2InfL, PowerSeries.coeff_map, ev1_C]

/-- at `z = 1` the two one-sided factors `SZ`, `SZinv` evaluate to the same diagonal partial theta. -/
lemma map_ev1_SZinv_eq : PowerSeries.map ev1 SZinv = PowerSeries.map ev1 SZ := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)),
      coeff_SZinv (le_refl (m + 1)), SZfinite, SZinvFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [ev1_coeff_SZinvTerm, ev1_coeff_SZterm]

/-- **the `z = 1` partial-theta sum** `Σ_{k≥0} q^{k²}/(q²;q²)_k`: the `q^m` coefficient is the finite
diagonal sum `Σ_{k} szc m k` of Cauchy coefficients. -/
lemma coeff_map_ev1_SZ (m : ℕ) :
    coeff m (PowerSeries.map ev1 SZ) = ∑ k ∈ Finset.range (m + 1), szc m k := by
  rw [PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)), SZfinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => ev1_coeff_SZterm m k

/-- the `z = 1` value of the paired bilateral term: `2` at `q^{(m+1)²}` (the `±(m+1)` pair), else `0`. -/
lemma ev1_coeff_bilatTerm (m k : ℕ) :
    ev1 (coeff k (bilatTerm m)) = if k = (m + 1) ^ 2 then 2 else 0 := by
  rw [bilatTerm, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, ev1.map_mul, ev1.map_add,
      ev1_T, ev1_T]
  by_cases hk : k = (m + 1) ^ 2
  · rw [if_pos hk, map_one, if_pos hk]; norm_num
  · rw [if_neg hk, map_zero, if_neg hk, zero_mul]

/-- **the `z = 1` theta** `Σ_{n∈ℤ} q^{n²}`: the `q^k` coefficient counts integer square roots of `k`
(`1` for `k = 0`, else `2` for each `k = (m+1)²`). -/
lemma coeff_map_ev1_bilateralTheta (k : ℕ) :
    coeff k (PowerSeries.map ev1 bilateralTheta)
      = (if k = 0 then 1 else 0) + ∑ m ∈ Finset.range (k + 1), (if k = (m + 1) ^ 2 then 2 else 0) := by
  rw [PowerSeries.coeff_map, coeff_bilateralTheta (le_refl (k + 1)), bilatFinite, map_add,
      ev1.map_add, map_sum, map_sum]
  congr 1
  · rw [PowerSeries.coeff_one]; by_cases hk : k = 0 <;> simp [hk]
  · exact Finset.sum_congr rfl fun m _ => ev1_coeff_bilatTerm m k

/-- **Gauss/Jacobi theta evaluation.**
`Σ_{n∈ℤ} q^{n²} = (q²;q²)_∞ · (Σ_{k≥0} q^{k²}/(q²;q²)_k)²` — the bilateral Jacobi triple product at `z = 1`. -/
theorem gauss_theta :
    PowerSeries.map ev1 bilateralTheta = qfac2Inf * (PowerSeries.map ev1 SZ) ^ 2 := by
  have h := congrArg (PowerSeries.map ev1) bilateral_jacobi_triple_product
  rw [map_mul, map_mul, map_ev1_qfac2InfL, map_ev1_SZinv_eq] at h
  rw [← h]; ring

end MockTheta5.JTP
