/-
# Quintuple product, stone 3 (Bracket 2, part 2): the signed square convolution and assembly

Completes Bracket 2: **`qfac2InfL · P_{z²} · P_{z⁻²} = thetaB`**, i.e. `qfac2InfL · SZ2 · SZ2inv = thetaB`.

The signed square z-Cauchy convolution reduces to the *unsigned* one already proven: at z-degree `2M` the
diagonal `2k − 2j = 2M` is `k − j = M`, and the sign `(−1)ᵏ(−1)ʲ = (−1)ᴹ` factors out (`k = M+j`), so

  `zProj (2M) (SZ2·SZ2inv) = (−1)ᴹ · zProj M (SZ·SZinv) = (−1)ᴹ q^{M²} E2(rectInf M)`,

whence the prefactor `(q²;q²)_∞` and `durfee_rect_base_Q` give `(−1)ᴹ q^{M²}`, matching `zProj (2M) thetaB`.
Odd z-degrees vanish; the `z ↦ z⁻¹` symmetry gives the negative degrees. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintBracketB1
import RamanujanTau.MockTheta5QuintBrackets

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### The signed z-Cauchy product, reduced to the unsigned one -/

lemma prodSZ2_apply (p r : ℕ) (N : ℤ) :
    (coeff p SZ2 * coeff r SZ2inv) N = ∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (r + 1),
        (if (2 * (k : ℤ)) - 2 * j = N then ((-1 : ℤ) ^ k * szc p k) * ((-1 : ℤ) ^ j * szc r j) else 0) := by
  rw [coeff_SZ2 (le_refl (p + 1)), coeff_SZ2inv (le_refl (r + 1)), SZ2finite, SZ2invFinite,
      map_sum, map_sum]
  simp_rw [coeff_SZ2term_single, coeff_SZ2invTerm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

/-- **the sign factors out**: the signed z-Cauchy product at `2M` is `(−1)ᴹ` times the unsigned one at `M`. -/
lemma prodSZ2_diag (p r M : ℕ) :
    (coeff p SZ2 * coeff r SZ2inv) (2 * (M : ℤ)) = (-1 : ℤ) ^ M * (coeff p SZ * coeff r SZinv) (M : ℤ) := by
  rw [prodSZ2_apply, prodSZ_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (k : ℤ) - j = M
  · rw [if_pos (by omega), if_pos h]
    have hsign : (-1 : ℤ) ^ k * (-1 : ℤ) ^ j = (-1 : ℤ) ^ M := by
      have hkj : k = M + j := by omega
      rw [hkj, pow_add, mul_assoc, ← pow_add, show j + j = 2 * j from by ring, pow_mul,
          neg_one_sq, one_pow, mul_one]
    calc ((-1 : ℤ) ^ k * szc p k) * ((-1 : ℤ) ^ j * szc r j)
        = ((-1 : ℤ) ^ k * (-1 : ℤ) ^ j) * (szc p k * szc r j) := by ring
      _ = (-1 : ℤ) ^ M * (szc p k * szc r j) := by rw [hsign]
  · rw [if_neg (by omega), if_neg h, mul_zero]

/-- **signed square z-Cauchy product** at z-degree `2M`: `(−1)ᴹ q^{M²} E2(rectInf M)`. -/
lemma zProj_SZ2_SZ2inv (M : ℕ) :
    zProj (2 * (M : ℤ)) (SZ2 * SZ2inv) = PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M ^ 2) * E2 (rectInf M)) := by
  have h := zProj_SZ_SZinv M
  ext q
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_C_mul, ← h, coeff_zProj,
      PowerSeries.coeff_mul, laurentSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pr _ => prodSZ2_diag pr.1 pr.2 M

/-- odd z-degrees of the signed square product vanish. -/
lemma zProj_SZ2_SZ2inv_odd {n : ℤ} (hn : ¬ ∃ M : ℤ, 2 * M = n) : zProj n (SZ2 * SZ2inv) = 0 := by
  ext q
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, map_zero]
  refine Finset.sum_eq_zero fun pr _ => ?_
  rw [prodSZ2_apply]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg (fun heq => hn ⟨(k : ℤ) - j, by omega⟩)]

/-! ### The `z ↦ z⁻¹` symmetry for the negative z-degrees -/

lemma map_invert_SZ2inv : PowerSeries.map invertHom SZ2inv = SZ2 := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, coeff_SZ2 (le_refl (m + 1)), coeff_SZ2inv (le_refl (m + 1)),
      SZ2finite, SZ2invFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coeff_SZ2term_single, coeff_SZ2invTerm_single, invert_single, neg_neg]

lemma map_invert_SZ2mul : PowerSeries.map invertHom (SZ2 * SZ2inv) = SZ2 * SZ2inv := by
  rw [map_mul, map_invert_SZ2, map_invert_SZ2inv, mul_comm]

lemma zProj_SZ2_SZ2inv_neg (M : ℕ) :
    zProj (-(2 * (M : ℤ))) (SZ2 * SZ2inv) = PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M ^ 2) * E2 (rectInf M)) := by
  rw [← map_invert_SZ2mul, zProj_map_invert, neg_neg, zProj_SZ2_SZ2inv]

/-! ### The prefactor law fused with `durfee_rect_base_Q` -/

/-- `(q²;q²)_∞ · zProj (±2M) (SZ2·SZ2inv) = (−1)ᴹ q^{M²}` (the Durfee inverse cancels). -/
lemma prefactor_times2 (M : ℕ) (b : Bool) :
    qfac2Inf * zProj (if b then 2 * (M : ℤ) else -(2 * (M : ℤ))) (SZ2 * SZ2inv)
      = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
  have hq : qfac2Inf * Ring.inverse qfac2Inf = 1 := Ring.mul_inverse_cancel _ isUnit_qfac2Inf
  cases b with
  | true =>
    rw [if_pos rfl, zProj_SZ2_SZ2inv, durfee_rect_base_Q]
    rw [show qfac2Inf * (PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M ^ 2) * Ring.inverse qfac2Inf))
          = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) * (qfac2Inf * Ring.inverse qfac2Inf) from by ring,
        hq, mul_one]
  | false =>
    rw [if_neg (by simp), zProj_SZ2_SZ2inv_neg, durfee_rect_base_Q]
    rw [show qfac2Inf * (PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M ^ 2) * Ring.inverse qfac2Inf))
          = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) * (qfac2Inf * Ring.inverse qfac2Inf) from by ring,
        hq, mul_one]

/-! ### Status

The **signed square z-Cauchy convolution is complete**: `zProj_SZ2_SZ2inv` (+ `_neg`, `_odd`) with
`prefactor_times2` deliver `(q²;q²)_∞ · zProj (±2M) (SZ2·SZ2inv) = (−1)ᴹ q^{M²}`, and 0 at odd degrees —
exactly the coefficients of `thetaB`. The remaining step (matching `zProj n thetaB` and the `zProj_ext`
assembly `qfac2InfL·SZ2·SZ2inv = thetaB`, plus rewriting via `SZ2_eq`/`SZ2inv_eq` to the actual product
`P_{z²}·P_{z⁻²}`) is the follow-up. -/

end MockTheta5.JTP
