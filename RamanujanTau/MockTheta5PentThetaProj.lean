/-
# Euler pentagonal — stone: the theta-side projection `zProj n pentTheta = q^{(3n²−n)/2}`

Mirror of `zProj_bilateralTheta` (same `±(m+1)` z-degree pairing), with the pentagonal exponents. For each
`n ∈ ℤ` exactly one term survives, giving `q^{(3n²−n)/2}` (`= q^{e(n)}`, the generalized pentagonal number).
No `sorry`.
-/
import RamanujanTau.MockTheta5PentTheta
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- z-projection of a single monomial `X^e · z^j`. -/
lemma zProj_map_C_T (a : PowerSeries ℤ) (j κ : ℤ) :
    zProj κ (PowerSeries.map (LaurentPolynomial.C) a * PowerSeries.C (T j)) = if j = κ then a else 0 := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
  split_ifs with h <;> simp

lemma zProj_pentTermP (m : ℕ) (κ : ℤ) :
    zProj κ (pentTermP m)
      = (if (m : ℤ) + 1 = κ then X ^ ((m + 1) * (3 * m + 2) / 2) else 0)
        + (if -((m : ℤ) + 1) = κ then X ^ ((m + 1) * (3 * m + 4) / 2) else 0) := by
  rw [pentTermP, zProj_add,
      show X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (T ((m : ℤ) + 1))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ ((m + 1) * (3 * m + 2) / 2))
            * PowerSeries.C (T ((m : ℤ) + 1)) from by rw [map_pow, PowerSeries.map_X],
      zProj_map_C_T,
      show X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (T (-((m : ℤ) + 1)))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ ((m + 1) * (3 * m + 4) / 2))
            * PowerSeries.C (T (-((m : ℤ) + 1))) from by rw [map_pow, PowerSeries.map_X],
      zProj_map_C_T]

/-- exponent cast (`n = N+1 > 0`). -/
lemma pentExp_cast_pos (N : ℕ) :
    (N + 1) * (3 * N + 2) / 2 = ((3 * ((N : ℤ) + 1) ^ 2 - ((N : ℤ) + 1)) / 2).toNat := by
  have key : (((N + 1) * (3 * N + 2) : ℕ) : ℤ) = 3 * ((N : ℤ) + 1) ^ 2 - ((N : ℤ) + 1) := by
    push_cast; ring
  rw [← key]; omega

/-- exponent cast (`n = −(N+1) < 0`). -/
lemma pentExp_cast_neg (N : ℕ) :
    (N + 1) * (3 * N + 4) / 2 = ((3 * (-((N : ℤ) + 1)) ^ 2 - -((N : ℤ) + 1)) / 2).toNat := by
  have key : (((N + 1) * (3 * N + 4) : ℕ) : ℤ) = 3 * (-((N : ℤ) + 1)) ^ 2 - -((N : ℤ) + 1) := by
    push_cast; ring
  rw [← key]; omega

lemma zProj_pentFinite (n : ℤ) (M : ℕ) (hM : n.natAbs < M) :
    zProj n (pentFiniteP M) = X ^ ((3 * n ^ 2 - n) / 2).toNat := by
  rw [pentFiniteP, zProj_add, zProj_one, zProj_sum]
  simp only [zProj_pentTermP, Finset.sum_add_distrib]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- n < 0: write n = −(N+1); second sum single at m = N
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = -((N : ℤ) + 1) := ⟨n.natAbs - 1, by omega⟩
    rw [if_neg (show -((N : ℤ) + 1) ≠ 0 from by omega), zero_add,
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), zero_add,
        Finset.sum_eq_single N (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl, pentExp_cast_neg]
  · subst hn
    rw [Finset.sum_eq_zero (fun m _ => if_neg (by omega)),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero]
    norm_num
  · -- n > 0: write n = N+1; first sum single at m = N
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) + 1 := ⟨n.natAbs - 1, by omega⟩
    rw [if_neg (show ((N : ℤ) + 1) ≠ 0 from by omega), zero_add,
        Finset.sum_eq_single N (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, if_pos rfl, pentExp_cast_pos]

lemma zProj_pentTheta (n : ℤ) : zProj n pentTheta = X ^ ((3 * n ^ 2 - n) / 2).toNat := by
  ext k
  rw [coeff_zProj, coeff_pentTheta (show k + 1 ≤ k + 1 + n.natAbs by omega), ← coeff_zProj,
      zProj_pentFinite n (k + 1 + n.natAbs) (by omega)]

end MockTheta5.JTP
