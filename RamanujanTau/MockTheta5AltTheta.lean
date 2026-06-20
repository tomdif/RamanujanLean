/-
# The alternating Jacobi theta evaluation — the `z = −1` corollary of the bilateral JTP

Specialising the bilateral Jacobi triple product at `z = −1` (the ring hom `ε₋ : ℤ[z;z⁻¹] → ℤ`,
`zᵏ ↦ (−1)ᵏ`) gives

  `Σ_{n∈ℤ} (−1)ⁿ q^{n²} = (q²;q²)_∞ · (Σ_{k≥0} (−1)ᵏ q^{k²}/(q²;q²)_k)²`,

the twin of `gauss_theta`. The `(−1)ᵏ` signs from `zᵏ` and `z⁻ᵏ` agree (`(−1)ᵏ = (−1)⁻ᵏ`), so the two
one-sided factors still coincide and the core identity is `PowerSeries.map ε₋` of the JTP. No `sorry`.
-/
import RamanujanTau.MockTheta5GaussTheta

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- evaluation `z ↦ −1` (`Σ aₖ zᵏ ↦ Σ (−1)ᵏ aₖ`) of `ℤ[z;z⁻¹]`, as a `RingHom`. -/
noncomputable def evm1 : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) (-1 : ℤˣ)

@[simp] lemma evm1_C (a : ℤ) : evm1 (LaurentPolynomial.C a) = a := by
  rw [evm1, ← Polynomial.toLaurent_C, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_C,
      RingHom.id_apply]

lemma evm1_T_nat (k : ℕ) : evm1 (T (k : ℤ)) = (-1) ^ k := by
  rw [evm1, LaurentPolynomial.eval₂_T, zpow_natCast]; simp

lemma evm1_T_negnat (k : ℕ) : evm1 (T (-(k : ℤ))) = (-1) ^ k := by
  rw [evm1, LaurentPolynomial.eval₂_T, zpow_neg, zpow_natCast]; simp

/-- `z ↦ −1` of the `k`-th `SZ` Cauchy term: the signed Cauchy coefficient `(−1)ᵏ szc m k`. -/
lemma evm1_coeff_SZterm (m k : ℕ) : evm1 (coeff m (SZterm k)) = (-1) ^ k * szc m k := by
  rw [SZterm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, evm1.map_mul, evm1_C,
      evm1_T_nat, mul_comm]; rfl

/-- `z ↦ −1` of the `k`-th `SZinv` term — the same `(−1)ᵏ szc m k` (since `(−1)⁻ᵏ = (−1)ᵏ`). -/
lemma evm1_coeff_SZinvTerm (m k : ℕ) : evm1 (coeff m (SZinvTerm k)) = (-1) ^ k * szc m k := by
  rw [SZinvTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, evm1.map_mul, evm1_C,
      evm1_T_negnat, mul_comm]; rfl

/-- `map evm1` sends the lifted prefactor back to `(q²;q²)_∞`. -/
lemma map_evm1_qfac2InfL : PowerSeries.map evm1 qfac2InfL = qfac2Inf := by
  refine PowerSeries.ext fun m => ?_
  simp only [qfac2InfL, PowerSeries.coeff_map, evm1_C]

/-- at `z = −1` the two one-sided factors evaluate to the same signed diagonal partial theta. -/
lemma map_evm1_SZinv_eq : PowerSeries.map evm1 SZinv = PowerSeries.map evm1 SZ := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)),
      coeff_SZinv (le_refl (m + 1)), SZfinite, SZinvFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [evm1_coeff_SZinvTerm, evm1_coeff_SZterm]

/-- **the `z = −1` partial theta** `Σ_{k≥0} (−1)ᵏ q^{k²}/(q²;q²)_k`. -/
lemma coeff_map_evm1_SZ (m : ℕ) :
    coeff m (PowerSeries.map evm1 SZ) = ∑ k ∈ Finset.range (m + 1), (-1) ^ k * szc m k := by
  rw [PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)), SZfinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => evm1_coeff_SZterm m k

/-- the `z = −1` value of the paired bilateral term: `2·(−1)^{m+1}` at `q^{(m+1)²}`, else `0`. -/
lemma evm1_coeff_bilatTerm (m k : ℕ) :
    evm1 (coeff k (bilatTerm m)) = if k = (m + 1) ^ 2 then 2 * (-1) ^ (m + 1) else 0 := by
  rw [bilatTerm, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, evm1.map_mul, evm1.map_add,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, evm1_T_nat, evm1_T_negnat]
  by_cases hk : k = (m + 1) ^ 2
  · rw [if_pos hk, map_one, if_pos hk]; ring
  · rw [if_neg hk, map_zero, if_neg hk, zero_mul]

/-- **the `z = −1` theta** `Σ_{n∈ℤ} (−1)ⁿ q^{n²}`: the `q^k` coefficient is the signed representation count. -/
lemma coeff_map_evm1_bilateralTheta (k : ℕ) :
    coeff k (PowerSeries.map evm1 bilateralTheta)
      = (if k = 0 then 1 else 0)
        + ∑ m ∈ Finset.range (k + 1), (if k = (m + 1) ^ 2 then 2 * (-1) ^ (m + 1) else 0) := by
  rw [PowerSeries.coeff_map, coeff_bilateralTheta (le_refl (k + 1)), bilatFinite, map_add,
      evm1.map_add, map_sum, map_sum]
  congr 1
  · rw [PowerSeries.coeff_one]; by_cases hk : k = 0 <;> simp [hk]
  · exact Finset.sum_congr rfl fun m _ => evm1_coeff_bilatTerm m k

/-- **Alternating Jacobi theta evaluation.**
`Σ_{n∈ℤ} (−1)ⁿ q^{n²} = (q²;q²)_∞ · (Σ_{k≥0} (−1)ᵏ q^{k²}/(q²;q²)_k)²` — the bilateral JTP at `z = −1`. -/
theorem alternating_theta :
    PowerSeries.map evm1 bilateralTheta = qfac2Inf * (PowerSeries.map evm1 SZ) ^ 2 := by
  have h := congrArg (PowerSeries.map evm1) bilateral_jacobi_triple_product
  rw [map_mul, map_mul, map_evm1_qfac2InfL, map_evm1_SZinv_eq] at h
  rw [← h]; ring

end MockTheta5.JTP
