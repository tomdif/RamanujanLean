/-
# JTP step L8 (the capstone): the bilateral Jacobi triple product

The Jacobi triple product, fully bilateralized:

  `(q²;q²)_∞ · (Σ_{k≥0} q^{k²} zᵏ/(q²;q²)_k) · (Σ_{j≥0} q^{j²} z⁻ʲ/(q²;q²)_j) = Σ_{n∈ℤ} zⁿ q^{n²}`,

i.e. `qfac2InfL · SZ · SZinv = bilateralTheta` in `PowerSeries (ℤ[z;z⁻¹])`.

The proof matches the two sides **z-degree by z-degree** through the projection `zProj`:

  * `zProj n (qfac2InfL · SZ · SZinv) = (q²;q²)_∞ · zProj n (SZ · SZinv)`   (prefactor is z-degree 0),
  * `(q²;q²)_∞ · zProj n (SZ · SZinv) = q^{n²}`   — the z-Cauchy product collapses to the Durfee-rectangle
    diagonal `zProj_SZ_SZinv` (and its `z↦z⁻¹` mirror for `n < 0`), then `durfee_rect_base_Q` discharges
    the `(q²;q²)_∞` factor since `E2(rectInf |n|) = 1/(q²;q²)_∞`,
  * `zProj n bilateralTheta = q^{n²}`,
  * `zProj`-by-`zProj` agreement determines the elements (`zProj_ext`).

Everything is computed by algebraic coefficient stabilization — no topology, no `tsum`. Axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only), no `sorry`.
-/
import RamanujanTau.MockTheta5ZConv
import RamanujanTau.MockTheta5JacobiBilateral

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### Combining both signs: `(q²;q²)_∞ · zProj n (SZ·SZinv) = q^{n²}` -/

/-- the prefactor `(q²;q²)_∞` cancels the Durfee-rectangle inverse for either sign of `n`, leaving
`q^{n²}` (with `n² = (|n|)²`). This fuses `zProj_SZ_SZinv`/`zProj_SZ_SZinv_neg` with `durfee_rect_base_Q`. -/
lemma prefactor_times (n : ℤ) : qfac2Inf * zProj n (SZ * SZinv) = X ^ (n.natAbs ^ 2) := by
  have hq : qfac2Inf * Ring.inverse qfac2Inf = 1 := Ring.mul_inverse_cancel _ isUnit_qfac2Inf
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with N
    rw [zProj_SZ_SZinv, durfee_rect_base_Q, Int.natAbs_natCast, ← mul_assoc,
        mul_comm qfac2Inf (X ^ (N ^ 2)), mul_assoc, hq, mul_one]
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, n = -(M : ℤ) := ⟨n.natAbs, by omega⟩
    rw [hM, zProj_SZ_SZinv_neg, durfee_rect_base_Q, Int.natAbs_neg, Int.natAbs_natCast,
        ← mul_assoc, mul_comm qfac2Inf (X ^ (M ^ 2)), mul_assoc, hq, mul_one]

/-! ### The bilateral theta side: `zProj n bilateralTheta = q^{n²}` -/

/-- the `T^n` slice of the paired bilateral term `(zᵐ⁺¹ + z⁻⁽ᵐ⁺¹⁾)·q^{(m+1)²}`. -/
lemma zProj_bilatTerm (m : ℕ) (n : ℤ) :
    zProj n (bilatTerm m)
      = (if (m : ℤ) + 1 = n then X ^ ((m + 1) ^ 2) else 0)
        + (if -((m : ℤ) + 1) = n then X ^ ((m + 1) ^ 2) else 0) := by
  ext k
  rw [coeff_zProj, map_add, bilatTerm, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  simp only [apply_ite (fun p : PowerSeries ℤ => coeff k p), PowerSeries.coeff_X_pow, map_zero]
  by_cases hk : k = (m + 1) ^ 2
  · subst hk
    simp only [if_true, one_mul]
    rw [show ((T ((m : ℤ) + 1) + T (-((m : ℤ) + 1)) : LaurentPolynomial ℤ) n)
          = (T ((m : ℤ) + 1) : LaurentPolynomial ℤ) n + (T (-((m : ℤ) + 1)) : LaurentPolynomial ℤ) n
        from Finsupp.add_apply _ _ _, LaurentPolynomial.T_apply, LaurentPolynomial.T_apply]
  · simp only [if_neg hk, zero_mul, ite_self, add_zero]
    exact Finsupp.zero_apply

/-- the constant `1` of the series (the `n = 0` term) projects to `1` at z-degree `0`, else `0`. -/
lemma zProj_one (n : ℤ) :
    zProj n (1 : PowerSeries (LaurentPolynomial ℤ)) = if n = 0 then 1 else 0 := by
  ext k
  rw [coeff_zProj, PowerSeries.coeff_one, apply_ite (coeff k), PowerSeries.coeff_one, map_zero]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, ← LaurentPolynomial.single_zero_one_eq_one, Finsupp.single_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [if_neg hk, ite_self]; exact Finsupp.zero_apply

/-- the `z^n` slice of the truncated bilateral sum: a single term `q^{n²}` survives (the `n = ±natAbs`
term), for any truncation `M` past `|n|`. -/
lemma zProj_bilatFinite (n : ℤ) (M : ℕ) (hM : n.natAbs < M) :
    zProj n (bilatFinite M) = X ^ (n.natAbs ^ 2) := by
  rw [bilatFinite, zProj_add, zProj_one, zProj_sum]
  simp only [zProj_bilatTerm, Finset.sum_add_distrib]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hnat : n.natAbs - 1 + 1 = n.natAbs := by omega
    rw [if_neg (by omega), Finset.sum_eq_zero (fun m _ => if_neg (by omega)), zero_add,
        Finset.sum_eq_single (n.natAbs - 1)]
    · rw [if_pos (by omega), hnat, zero_add]
    · exact fun m _ hm => if_neg (by omega)
    · exact fun h => absurd (Finset.mem_range.mpr (by omega)) h
  · subst hn
    rw [if_pos rfl, Finset.sum_eq_zero (fun m _ => if_neg (by omega)),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, add_zero]
    simp
  · have hnat : n.natAbs - 1 + 1 = n.natAbs := by omega
    have hA : ∑ m ∈ Finset.range M,
          (if (m : ℤ) + 1 = n then (X : PowerSeries ℤ) ^ ((m + 1) ^ 2) else 0)
        = (X : PowerSeries ℤ) ^ (n.natAbs ^ 2) := by
      rw [Finset.sum_eq_single (n.natAbs - 1)]
      · rw [if_pos (by omega), hnat]
      · exact fun m _ hm => if_neg (by omega)
      · exact fun h => absurd (Finset.mem_range.mpr (by omega)) h
    have hB : ∑ m ∈ Finset.range M,
        (if -((m : ℤ) + 1) = n then (X : PowerSeries ℤ) ^ ((m + 1) ^ 2) else 0) = 0 :=
      Finset.sum_eq_zero (fun m _ => if_neg (by omega))
    rw [if_neg (by omega), hA, hB, zero_add, add_zero]

/-- **`zProj n bilateralTheta = q^{n²}`** for every `n ∈ ℤ` — the RHS of the Jacobi triple product. -/
lemma zProj_bilateralTheta (n : ℤ) : zProj n bilateralTheta = X ^ (n.natAbs ^ 2) := by
  ext k
  rw [coeff_zProj, coeff_bilateralTheta (show k + 1 ≤ k + 1 + n.natAbs by omega), ← coeff_zProj,
      zProj_bilatFinite n (k + 1 + n.natAbs) (by omega)]

/-! ### z-projections determine the element, and the capstone -/

/-- a power series over `ℤ[z;z⁻¹]` is determined by all of its z-degree projections. -/
lemma zProj_ext {A B : PowerSeries (LaurentPolynomial ℤ)} (h : ∀ n, zProj n A = zProj n B) :
    A = B := by
  ext m n
  rw [← coeff_zProj, ← coeff_zProj, h n]

/-- **The Jacobi triple product (bilateral form).**
`(q²;q²)_∞ · (Σ_{k≥0} q^{k²}zᵏ/(q²;q²)_k) · (Σ_{j≥0} q^{j²}z⁻ʲ/(q²;q²)_j) = Σ_{n∈ℤ} zⁿ q^{n²}`. -/
theorem bilateral_jacobi_triple_product : qfac2InfL * SZ * SZinv = bilateralTheta := by
  refine zProj_ext fun n => ?_
  rw [mul_assoc, zProj_qfac2InfL_mul, prefactor_times, zProj_bilateralTheta]

end MockTheta5.JTP
