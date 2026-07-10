/-
# Quintuple product, stone 3 (Bracket 1, assembly): `qfacInfL · P_z · P_{z⁻¹} = thetaA`

The final step of Bracket 1. Combining the signed triangular convolution (`zProj_SZA_SZAinv` / `_neg` +
`durfee_rect_base`) with the `thetaA`-side projection, the `zProj_ext` assembly gives

  `qfacInfL · SZA · SZAinv = thetaA`,

and via `SZA_eq` / `SZAinv_eq` this is `qfacInfL · qzProdAInf · (map invertHom qzProdBInf) = thetaA`, i.e.
`(q;q)_∞ · ∏(1−z qⁿ) · ∏(1−z⁻¹ qⁿ⁻¹) = Σ_{n∈ℤ}(−1)ⁿ z⁻ⁿ q^{n(n−1)/2}`. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintBracketA2
import RamanujanTau.MockTheta5QuintBrackets
import RamanujanTau.MockTheta5TriangularBilateral

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

private lemma coeff_ite_CX_self (e : ℕ) (s : ℤ) (P : Prop) [Decidable P] :
    (coeff e) (if P then PowerSeries.C s * X ^ e else 0) = if P then s else 0 := by
  rw [apply_ite (coeff e), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one, map_zero]

private lemma coeff_ite_CX_ne (k e : ℕ) (s : ℤ) (P : Prop) [Decidable P] (h : k ≠ e) :
    (coeff k) (if P then PowerSeries.C s * X ^ e else 0) = 0 := by
  rw [apply_ite (coeff k), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg h, mul_zero,
      map_zero, ite_self]

/-- the `T^κ` slice of the paired `thetaA` term `(−1)ᵐ z^m − (−1)ᵐ z^{−(m+1)}) q^{m(m+1)/2}`. -/
lemma zProj_thetaATerm (m : ℕ) (κ : ℤ) :
    zProj κ (thetaATerm m)
      = (if (m : ℤ) = κ then PowerSeries.C ((-1 : ℤ) ^ m) * X ^ (m * (m + 1) / 2) else 0)
        + (if -((m : ℤ) + 1) = κ then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ (m * (m + 1) / 2) else 0) := by
  ext k
  rw [coeff_zProj, thetaATerm, PowerSeries.coeff_mul_C, map_add]
  by_cases hk : k = m * (m + 1) / 2
  · subst hk
    rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul, C_mul_apply,
        show ((T (m : ℤ) - T (-((m : ℤ) + 1)) : LaurentPolynomial ℤ) κ)
          = (T (m : ℤ) : LaurentPolynomial ℤ) κ - (T (-((m : ℤ) + 1)) : LaurentPolynomial ℤ) κ
        from Finsupp.sub_apply _ _ _,
        LaurentPolynomial.T_apply, LaurentPolynomial.T_apply, coeff_ite_CX_self, coeff_ite_CX_self,
        show (-1 : ℤ) ^ (m + 1) = (-1) ^ m * (-1) from pow_succ _ _]
    split_ifs <;> ring
  · rw [PowerSeries.coeff_X_pow, if_neg hk, zero_mul, coeff_ite_CX_ne _ _ _ _ hk,
        coeff_ite_CX_ne _ _ _ _ hk, add_zero]
    exact Finsupp.zero_apply

lemma zProj_thetaAFinite (n : ℤ) (M : ℕ) (hM : n.natAbs < M) :
    zProj n (thetaAFinite M) = PowerSeries.C ((-1 : ℤ) ^ n.natAbs) * X ^ ((n * (n + 1) / 2).toNat) := by
  rw [thetaAFinite, zProj_sum]
  simp only [zProj_thetaATerm, Finset.sum_add_distrib]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- n < 0: `z^{−(m+1)} = n` term at m = n.natAbs − 1
    have hexp : (n.natAbs - 1) * (n.natAbs - 1 + 1) / 2 = (n * (n + 1) / 2).toNat := by
      have h1 : ((n.natAbs - 1 : ℕ) : ℤ) = -n - 1 := by omega
      have hprod : (((n.natAbs - 1) * (n.natAbs - 1 + 1) : ℕ) : ℤ) = n * (n + 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h1]; ring
      omega
    have hsign : (-1 : ℤ) ^ (n.natAbs - 1 + 1) = (-1 : ℤ) ^ n.natAbs := by
      congr 1; omega
    rw [Finset.sum_eq_zero (fun m _ => if_neg (by omega)), zero_add,
        Finset.sum_eq_single (n.natAbs - 1) (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h), if_pos (by omega), hexp, hsign]
  · subst hn
    rw [Finset.sum_eq_single 0 (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, if_pos (by norm_num)]
    norm_num
  · -- n > 0: `z^m = n` term at m = n.natAbs
    have hexp : n.natAbs * (n.natAbs + 1) / 2 = (n * (n + 1) / 2).toNat := by
      have h1 : (n.natAbs : ℤ) = n := by omega
      have hprod : ((n.natAbs * (n.natAbs + 1) : ℕ) : ℤ) = n * (n + 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, h1]
      omega
    rw [Finset.sum_eq_single n.natAbs (fun m _ hm => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, if_pos (by omega), hexp]

/-- **`zProj n thetaA = (−1)^{|n|} q^{n(n+1)/2}`** for every `n ∈ ℤ`. -/
lemma zProj_thetaA (n : ℤ) :
    zProj n thetaA = PowerSeries.C ((-1 : ℤ) ^ n.natAbs) * X ^ ((n * (n + 1) / 2).toNat) := by
  ext k
  rw [coeff_zProj, coeff_thetaA (show k + 1 ≤ k + 1 + n.natAbs by omega), ← coeff_zProj,
      zProj_thetaAFinite n (k + 1 + n.natAbs) (by omega)]

/-- exponent identity `⌊N(N+1)/2⌋ = C(N+1,2)`. -/
private lemma choose_two_toNat_pos (N : ℕ) : ((N : ℤ) * ((N : ℤ) + 1) / 2).toNat = (N + 1).choose 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have h : (N : ℤ) * ((N : ℤ) + 1) = (((N + 1) * N : ℕ) : ℤ) := by push_cast; ring
  rw [h]; omega

/-- exponent identity `⌊(−M)(−M+1)/2⌋ = C(M,2)`. -/
private lemma choose_two_toNat_negA (M : ℕ) :
    ((-(M : ℤ)) * ((-(M : ℤ)) + 1) / 2).toNat = M.choose 2 := by
  rw [Nat.choose_two_right]
  have h : (-(M : ℤ)) * ((-(M : ℤ)) + 1) = ((M * (M - 1) : ℕ) : ℤ) := by
    rcases M with _ | M
    · simp
    · push_cast; ring
  rw [h]; omega

/-! ### The assembly -/

/-- **Bracket 1 (Cauchy form):** `qfacInfL · SZA · SZAinv = thetaA`. -/
theorem bracket1_SZA : qfacInfL * SZA * SZAinv = thetaA := by
  refine zProj_ext (fun n => ?_)
  rw [mul_assoc, zProj_qfacInfL_mul, zProj_thetaA]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with N
    rw [zProj_SZA_SZAinv, durfee_rect_base,
        show qfacInf * (PowerSeries.C ((-1 : ℤ) ^ N) * (X ^ ((N + 1).choose 2) * Ring.inverse qfacInf))
          = PowerSeries.C ((-1 : ℤ) ^ N) * X ^ ((N + 1).choose 2) * (qfacInf * Ring.inverse qfacInf) from by
          ring,
        Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, mul_one, Int.natAbs_natCast,
        choose_two_toNat_pos]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, n = -(M : ℤ) := ⟨n.natAbs, by omega⟩
    rw [zProj_SZA_SZAinv_neg, durfee_rect_base,
        show qfacInf * (PowerSeries.C ((-1 : ℤ) ^ M) * (X ^ (M.choose 2) * Ring.inverse qfacInf))
          = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M.choose 2) * (qfacInf * Ring.inverse qfacInf) from by
          ring,
        Ring.mul_inverse_cancel qfacInf isUnit_qfacInf, mul_one, Int.natAbs_neg, Int.natAbs_natCast,
        choose_two_toNat_negA]

/-- **Bracket 1:** `(q;q)_∞ · ∏(1−z qⁿ) · ∏(1−z⁻¹ qⁿ⁻¹) = Σ_{n∈ℤ}(−1)ⁿ z⁻ⁿ q^{n(n−1)/2}`. -/
theorem bracket1 : qfacInfL * qzProdAInf * (PowerSeries.map invertHom qzProdBInf) = thetaA := by
  rw [← SZA_eq, ← SZAinv_eq, bracket1_SZA]

end MockTheta5.JTP
