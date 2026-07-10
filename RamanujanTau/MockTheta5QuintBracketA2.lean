/-
# Quintuple product, stone 3 (Bracket 1, part 2): the signed triangular convolution

The signed triangular z-Cauchy product `SZA · SZAinv` reduces to the *unsigned* triangular one already
proven (`zProj_TZ_TZ1inv` / `_neg`). Because `SZA` carries the shift on the `z`-side (opposite the standard
`TZ`), the diagonal at z-degree `N` matches `TZ1inv · TZ` (`= TZ · TZ1inv`) at z-degree `−N`, and the sign
`(−1)ᵏ(−1)ʲ = (−1)ᴺ` factors out:

  `zProj N (SZA·SZAinv) = (−1)ᴺ · zProj (−N) (TZ·TZ1inv) = (−1)ᴺ q^{C(N+1,2)} · rectInf N`   (`N ≥ 0`),
  `zProj (−M) (SZA·SZAinv) = (−1)ᴹ · zProj M (TZ·TZ1inv) = (−1)ᴹ q^{C(M,2)} · rectInf M`      (`M ≥ 0`).

`zProj_TZ_TZ1inv_neg` supplies the `C(N+1,2)` exponent for free (the triangular theta is asymmetric). No `sorry`.
-/
import RamanujanTau.MockTheta5QuintBracketA1

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### Singles of `SZA`, `SZAinv` -/

lemma coeff_SZAterm_single (p k : ℕ) :
    coeff p (SZAterm k) = Finsupp.single (k : ℤ) ((-1 : ℤ) ^ k * tzc1 p k) := by
  ext n
  rw [SZAterm, PowerSeries.coeff_mul_C, tcCoef1, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply, Finsupp.single_apply, tzc1]
  split_ifs with h <;> [rw [mul_comm]; rfl]

lemma coeff_SZAinvterm_single (r j : ℕ) :
    coeff r (SZAinvterm j) = Finsupp.single (-(j : ℤ)) ((-1 : ℤ) ^ j * tzc r j) := by
  ext n
  rw [SZAinvterm, PowerSeries.coeff_mul_C, tcCoef, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply, Finsupp.single_apply, tzc]
  split_ifs with h <;> [rw [mul_comm]; rfl]

/-! ### The two z-Cauchy products, as diagonal double-sums -/

lemma prodSZA_apply (p r : ℕ) (N : ℤ) :
    (coeff p SZA * coeff r SZAinv) N = ∑ k ∈ Finset.range (p + 2), ∑ j ∈ Finset.range (r + 2),
        (if (k : ℤ) - j = N then ((-1 : ℤ) ^ k * tzc1 p k) * ((-1 : ℤ) ^ j * tzc r j) else 0) := by
  rw [coeff_SZA (le_refl (p + 2)), coeff_SZAinv (le_refl (r + 2)), SZAfinite, SZAinvFinite,
      map_sum, map_sum]
  simp_rw [coeff_SZAterm_single, coeff_SZAinvterm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

lemma prodTZ1inv_TZ_apply (p r : ℕ) (M : ℤ) :
    (coeff p TZ1inv * coeff r TZ) M = ∑ k ∈ Finset.range (p + 2), ∑ j ∈ Finset.range (r + 2),
        (if (-(k : ℤ)) + j = M then tzc1 p k * tzc r j else 0) := by
  rw [coeff_TZ1inv (le_refl (p + 2)), coeff_TZ (le_refl (r + 2)), TZ1invFinite, TZfinite,
      map_sum, map_sum]
  simp_rw [coeff_TZ1invTerm_single, coeff_TZterm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply]

/-! ### The sign factors out (both signs of the degree) -/

private lemma sign_split {k j N : ℕ} (h : k = N + j) : (-1 : ℤ) ^ k * (-1 : ℤ) ^ j = (-1 : ℤ) ^ N := by
  rw [h, pow_add, mul_assoc, ← pow_add, show j + j = 2 * j from by ring, pow_mul, neg_one_sq,
      one_pow, mul_one]

lemma prodSZA_diag (p r N : ℕ) :
    (coeff p SZA * coeff r SZAinv) (N : ℤ) = (-1 : ℤ) ^ N * (coeff p TZ1inv * coeff r TZ) (-(N : ℤ)) := by
  rw [prodSZA_apply, prodTZ1inv_TZ_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (k : ℤ) - j = N
  · rw [if_pos h, if_pos (by omega)]
    calc ((-1 : ℤ) ^ k * tzc1 p k) * ((-1 : ℤ) ^ j * tzc r j)
        = ((-1 : ℤ) ^ k * (-1 : ℤ) ^ j) * (tzc1 p k * tzc r j) := by ring
      _ = (-1 : ℤ) ^ N * (tzc1 p k * tzc r j) := by rw [sign_split (show k = N + j by omega)]
  · rw [if_neg h, if_neg (by omega), mul_zero]

lemma prodSZA_diag_neg (p r M : ℕ) :
    (coeff p SZA * coeff r SZAinv) (-(M : ℤ)) = (-1 : ℤ) ^ M * (coeff p TZ1inv * coeff r TZ) (M : ℤ) := by
  rw [prodSZA_apply, prodTZ1inv_TZ_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (k : ℤ) - j = -(M : ℤ)
  · rw [if_pos h, if_pos (by omega)]
    calc ((-1 : ℤ) ^ k * tzc1 p k) * ((-1 : ℤ) ^ j * tzc r j)
        = ((-1 : ℤ) ^ k * (-1 : ℤ) ^ j) * (tzc1 p k * tzc r j) := by ring
      _ = (-1 : ℤ) ^ M * (tzc1 p k * tzc r j) := by
            rw [mul_comm ((-1 : ℤ) ^ k) ((-1 : ℤ) ^ j), sign_split (show j = M + k by omega)]
  · rw [if_neg h, if_neg (by omega), mul_zero]

/-! ### The signed triangular z-Cauchy product -/

/-- `zProj N (SZA·SZAinv) = (−1)ᴺ q^{C(N+1,2)} · rectInf N` (`N ≥ 0`). -/
lemma zProj_SZA_SZAinv (N : ℕ) :
    zProj (N : ℤ) (SZA * SZAinv) = PowerSeries.C ((-1 : ℤ) ^ N) * (X ^ ((N + 1).choose 2) * rectInf N) := by
  have h : zProj (-(N : ℤ)) (TZ1inv * TZ) = X ^ ((N + 1).choose 2) * rectInf N := by
    rw [mul_comm, zProj_TZ_TZ1inv_neg]
  ext q
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_C_mul, ← h, coeff_zProj,
      PowerSeries.coeff_mul, laurentSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pr _ => prodSZA_diag pr.1 pr.2 N

/-- `zProj (−M) (SZA·SZAinv) = (−1)ᴹ q^{C(M,2)} · rectInf M` (`M ≥ 0`). -/
lemma zProj_SZA_SZAinv_neg (M : ℕ) :
    zProj (-(M : ℤ)) (SZA * SZAinv) = PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M.choose 2) * rectInf M) := by
  have h : zProj (M : ℤ) (TZ1inv * TZ) = X ^ (M.choose 2) * rectInf M := by
    rw [mul_comm, zProj_TZ_TZ1inv]
  ext q
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_C_mul, ← h, coeff_zProj,
      PowerSeries.coeff_mul, laurentSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pr _ => prodSZA_diag_neg pr.1 pr.2 M

end MockTheta5.JTP
