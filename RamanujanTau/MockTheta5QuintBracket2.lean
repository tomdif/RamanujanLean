/-
# Quintuple product, stone 3 (Bracket 2, assembly): `qfac2InfL · P_{z²} · P_{z⁻²} = thetaB`

The final step of Bracket 2. Combining the signed square convolution (`prefactor_times2`) with the
`thetaB`-side projection (`zProj_thetaB_*`), the `zProj_ext` assembly gives

  `qfac2InfL · SZ2 · SZ2inv = thetaB`,

and via `SZ2_eq` / `SZ2inv_eq` this is `qfac2InfL · jtp2ProdInf · (map invertHom jtp2ProdInf) = thetaB`,
i.e. `(q²;q²)_∞ · ∏(1−z²q^{2n−1}) · ∏(1−z⁻²q^{2n−1}) = Σ_{n∈ℤ}(−1)ⁿ z^{2n} q^{n²}`. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintBracketB2

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- coeff at the matching power: `coeff e (if P then C(s)·X^e else 0) = if P then s else 0`. -/
private lemma coeff_ite_CX_self (e : ℕ) (s : ℤ) (P : Prop) [Decidable P] :
    (coeff e) (if P then PowerSeries.C s * X ^ e else 0) = if P then s else 0 := by
  rw [apply_ite (coeff e), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one,
      map_zero]

/-- coeff off the power: `coeff k (if P then C(s)·X^e else 0) = 0` when `k ≠ e`. -/
private lemma coeff_ite_CX_ne (k e : ℕ) (s : ℤ) (P : Prop) [Decidable P] (h : k ≠ e) :
    (coeff k) (if P then PowerSeries.C s * X ^ e else 0) = 0 := by
  rw [apply_ite (coeff k), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg h, mul_zero,
      map_zero, ite_self]

/-- the `T^n` slice of the paired `thetaB` term `(−1)^{m+1}(z^{2(m+1)}+z^{−2(m+1)})q^{(m+1)²}`. -/
lemma zProj_thetaBTerm (m : ℕ) (n : ℤ) :
    zProj n (thetaBTerm m)
      = (if 2 * ((m : ℤ) + 1) = n then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2) else 0)
        + (if -(2 * ((m : ℤ) + 1)) = n then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2) else 0) := by
  ext k
  rw [coeff_zProj, thetaBTerm, PowerSeries.coeff_mul_C, map_add]
  by_cases hk : k = (m + 1) ^ 2
  · subst hk
    rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul, C_mul_apply,
        show ((T (2 * ((m : ℤ) + 1)) + T (-(2 * ((m : ℤ) + 1))) : LaurentPolynomial ℤ) n)
          = (T (2 * ((m : ℤ) + 1)) : LaurentPolynomial ℤ) n + (T (-(2 * ((m : ℤ) + 1))) : LaurentPolynomial ℤ) n
        from Finsupp.add_apply _ _ _,
        LaurentPolynomial.T_apply, LaurentPolynomial.T_apply, coeff_ite_CX_self, coeff_ite_CX_self]
    split_ifs <;> ring
  · rw [PowerSeries.coeff_X_pow, if_neg hk, zero_mul, coeff_ite_CX_ne _ _ _ _ hk,
        coeff_ite_CX_ne _ _ _ _ hk, add_zero]
    exact Finsupp.zero_apply

/-! ### `zProj n thetaB` -/

lemma zProj_thetaB_pos_finite (M N : ℕ) (h : M < N) :
    zProj (2 * (M : ℤ)) (thetaBFinite N) = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
  rw [thetaBFinite, zProj_add, zProj_one, zProj_sum]
  simp only [zProj_thetaBTerm, Finset.sum_add_distrib]
  have hS2 : (∑ m ∈ Finset.range N,
      if -(2 * ((m : ℤ) + 1)) = 2 * (M : ℤ) then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2)
        else 0) = 0 := Finset.sum_eq_zero (fun m _ => if_neg (by omega))
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    rw [if_pos (by norm_num), Finset.sum_eq_zero (fun m _ => if_neg (by omega)), hS2, add_zero, add_zero]
    simp
  · have hS1 : (∑ m ∈ Finset.range N,
        if 2 * ((m : ℤ) + 1) = 2 * (M : ℤ) then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2)
          else 0) = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
      rw [Finset.sum_eq_single (M - 1)]
      · rw [if_pos (by omega), show M - 1 + 1 = M from by omega]
      · exact fun m _ hm => if_neg (by omega)
      · exact fun hc => absurd (Finset.mem_range.mpr (by omega)) hc
    rw [if_neg (by omega), zero_add, hS1, hS2, add_zero]

lemma zProj_thetaB_pos (M : ℕ) : zProj (2 * (M : ℤ)) thetaB = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
  ext k
  rw [coeff_zProj, coeff_thetaB (show k + 1 ≤ k + 1 + M by omega), ← coeff_zProj,
      zProj_thetaB_pos_finite M (k + 1 + M) (by omega)]

lemma zProj_thetaB_neg_finite (M N : ℕ) (h : M < N) :
    zProj (-(2 * (M : ℤ))) (thetaBFinite N) = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
  rw [thetaBFinite, zProj_add, zProj_one, zProj_sum]
  simp only [zProj_thetaBTerm, Finset.sum_add_distrib]
  have hS1 : (∑ m ∈ Finset.range N,
      if 2 * ((m : ℤ) + 1) = -(2 * (M : ℤ)) then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2)
        else 0) = 0 := Finset.sum_eq_zero (fun m _ => if_neg (by omega))
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    rw [if_pos (by norm_num), hS1, Finset.sum_eq_zero (fun m _ => if_neg (by omega)), add_zero, add_zero]
    simp
  · have hS2 : (∑ m ∈ Finset.range N,
        if -(2 * ((m : ℤ) + 1)) = -(2 * (M : ℤ)) then PowerSeries.C ((-1 : ℤ) ^ (m + 1)) * X ^ ((m + 1) ^ 2)
          else 0) = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
      rw [Finset.sum_eq_single (M - 1)]
      · rw [if_pos (by omega), show M - 1 + 1 = M from by omega]
      · exact fun m _ hm => if_neg (by omega)
      · exact fun hc => absurd (Finset.mem_range.mpr (by omega)) hc
    rw [if_neg (by omega), zero_add, hS1, hS2, zero_add]

lemma zProj_thetaB_neg (M : ℕ) :
    zProj (-(2 * (M : ℤ))) thetaB = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := by
  ext k
  rw [coeff_zProj, coeff_thetaB (show k + 1 ≤ k + 1 + M by omega), ← coeff_zProj,
      zProj_thetaB_neg_finite M (k + 1 + M) (by omega)]

lemma zProj_thetaB_odd {n : ℤ} (hn : ¬ ∃ M : ℤ, 2 * M = n) : zProj n thetaB = 0 := by
  ext k
  rw [coeff_zProj, coeff_thetaB (le_refl (k + 1)), ← coeff_zProj, map_zero, thetaBFinite, zProj_add,
      zProj_one, if_neg (fun h => hn ⟨0, by omega⟩), zero_add, zProj_sum,
      Finset.sum_eq_zero (fun m _ => by
        rw [zProj_thetaBTerm, if_neg (fun h => hn ⟨(m : ℤ) + 1, h⟩),
            if_neg (fun h => hn ⟨-((m : ℤ) + 1), by omega⟩), add_zero]), map_zero]

/-! ### The assembly -/

/-- **Bracket 2 (Cauchy form):** `qfac2InfL · SZ2 · SZ2inv = thetaB`. -/
theorem bracket2_SZ2 : qfac2InfL * SZ2 * SZ2inv = thetaB := by
  have hpos : ∀ M : ℕ, qfac2Inf * zProj (2 * (M : ℤ)) (SZ2 * SZ2inv)
      = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := fun M => by
    have h := prefactor_times2 M true; simpa using h
  have hneg : ∀ M : ℕ, qfac2Inf * zProj (-(2 * (M : ℤ))) (SZ2 * SZ2inv)
      = PowerSeries.C ((-1 : ℤ) ^ M) * X ^ (M ^ 2) := fun M => by
    have h := prefactor_times2 M false; simpa using h
  refine zProj_ext fun n => ?_
  rw [mul_assoc, zProj_qfac2InfL_mul]
  by_cases hn : ∃ M : ℤ, 2 * M = n
  · obtain ⟨M, rfl⟩ := hn
    rcases lt_or_ge M 0 with hM | hM
    · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = -(M' : ℤ) := ⟨M.natAbs, by omega⟩
      rw [show 2 * (-(M' : ℤ)) = -(2 * (M' : ℤ)) from by ring, hneg M', zProj_thetaB_neg]
    · lift M to ℕ using hM with M
      rw [hpos M, zProj_thetaB_pos]
  · rw [zProj_SZ2_SZ2inv_odd hn, mul_zero, zProj_thetaB_odd hn]

/-- **Bracket 2:** `(q²;q²)_∞ · ∏(1−z²q^{2n−1}) · ∏(1−z⁻²q^{2n−1}) = Σ_{n∈ℤ}(−1)ⁿ z^{2n} q^{n²}`. -/
theorem bracket2 : qfac2InfL * jtp2ProdInf * (PowerSeries.map invertHom jtp2ProdInf) = thetaB := by
  rw [← SZ2inv_eq, ← SZ2_eq, bracket2_SZ2]

end MockTheta5.JTP
