/-
# Quintuple product, stone 3 (Bracket 2, part 1): the signed Cauchy sums `SZ2`, `SZ2inv`

For Bracket 2 (`qfac2InfL · P_{z²} · P_{z⁻²} = thetaB`) we represent the base-`q²` z²-side product
`P_{z²} = jtp2ProdInf` in the Cauchy sum-of-singles form used by the square JTP convolution:

  `SZ2   = Σ_{k≥0} (−1)ᵏ (q^{k²}/(q²;q²)_k) z^{2k}`,   `SZ2inv = Σ_{k≥0} (−1)ᵏ (q^{k²}/(q²;q²)_k) z^{−2k}`.

These reuse `cauchyCoef` (same Cauchy coefficient `q^{k²}/(q²;q²)_k` as the unsigned `SZ`), placed at z-degree
`±2k` with sign `(−1)ᵏ`. This file builds them, their z-projections (via `zProj_mapC_scaledCT`), and proves the
**connection** `SZ2 = jtp2ProdInf`, `SZ2inv = map invertHom jtp2ProdInf` — so the convolution (part 2) can run
on `SZ2·SZ2inv` and land back on the actual quintuple factors. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintProdZ2
import RamanujanTau.MockTheta5CauchySum
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the `z^{2k}`-term of the signed square Cauchy sum: `(−1)ᵏ (q^{k²}/(q²;q²)_k) z^{2k}`. -/
noncomputable def SZ2term (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  cauchyCoef k * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (2 * (k : ℤ)))

/-- the `z^{−2k}`-term of the mirror signed square Cauchy sum. -/
noncomputable def SZ2invTerm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  cauchyCoef k * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (-(2 * (k : ℤ))))

lemma SZ2term_coeff_zero {k m : ℕ} (h : m < k ^ 2) : coeff m (SZ2term k) = 0 := by
  rw [SZ2term, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k ^ 2) m h, map_zero, zero_mul]

lemma SZ2invTerm_coeff_zero {k m : ℕ} (h : m < k ^ 2) : coeff m (SZ2invTerm k) = 0 := by
  rw [SZ2invTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k ^ 2) m h, map_zero, zero_mul]

noncomputable def SZ2finite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZ2term k
noncomputable def SZ2invFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZ2invTerm k
noncomputable def SZ2 : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZ2finite (m + 1))
noncomputable def SZ2inv : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZ2invFinite (m + 1))

lemma coeff_SZ2_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N → coeff m (SZ2finite N) = coeff m (SZ2finite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZ2finite (N + 1) = SZ2finite N + SZ2term N := by
          rw [SZ2finite, SZ2finite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZ2term_coeff_zero (show m < N ^ 2 by have hN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N; omega),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZ2 {m M : ℕ} (hM : m + 1 ≤ M) : coeff m SZ2 = coeff m (SZ2finite M) := by
  rw [SZ2, coeff_mk, coeff_SZ2_stable (Nat.lt_succ_self m) hM]

lemma coeff_SZ2inv_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N →
    coeff m (SZ2invFinite N) = coeff m (SZ2invFinite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZ2invFinite (N + 1) = SZ2invFinite N + SZ2invTerm N := by
          rw [SZ2invFinite, SZ2invFinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZ2invTerm_coeff_zero (show m < N ^ 2 by have hN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N; omega),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZ2inv {m M : ℕ} (hM : m + 1 ≤ M) : coeff m SZ2inv = coeff m (SZ2invFinite M) := by
  rw [SZ2inv, coeff_mk, coeff_SZ2inv_stable (Nat.lt_succ_self m) hM]

/-! ### z-projections of `SZ2` (via `zProj_mapC_scaledCT`) -/

lemma zProj_SZ2term (k : ℕ) (n : ℤ) :
    zProj n (SZ2term k)
      = if (2 * (k : ℤ)) = n then PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))
        else 0 := by
  rw [SZ2term, cauchyCoef, zProj_mapC_scaledCT]

lemma zProj_SZ2invTerm (k : ℕ) (n : ℤ) :
    zProj n (SZ2invTerm k)
      = if (-(2 * (k : ℤ))) = n then PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))
        else 0 := by
  rw [SZ2invTerm, cauchyCoef, zProj_mapC_scaledCT]

lemma zProj_SZ2finite (k M : ℕ) (h : k < M) :
    zProj (2 * (k : ℤ)) (SZ2finite M)
      = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) := by
  rw [SZ2finite, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_SZ2term, if_neg (by omega)])
        (fun hk => absurd (Finset.mem_range.mpr h) hk),
      zProj_SZ2term, if_pos rfl]

/-- z-degree-`2k` projection of `SZ2` = `(−1)ᵏ q^{k²}/(q²;q²)_k` (matches `zProj_jtp2ProdInf`). -/
lemma zProj_SZ2 (k : ℕ) :
    zProj (2 * (k : ℤ)) SZ2 = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) := by
  ext m
  rw [coeff_zProj, coeff_SZ2 (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_SZ2finite k (m + k + 1) (by omega)]

/-- `SZ2` vanishes at any z-degree that is not `2k` (`k ≥ 0`). -/
lemma zProj_SZ2_zero {n : ℤ} (hn : ¬ ∃ k : ℕ, (2 * (k : ℤ)) = n) : zProj n SZ2 = 0 := by
  ext m
  rw [coeff_zProj, coeff_SZ2 (le_refl (m + 1)), ← coeff_zProj, SZ2finite, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_SZ2term, if_neg (fun heq => hn ⟨k, heq⟩)])]

/-- **`SZ2 = jtp2ProdInf = P_{z²}`** — the Cauchy form equals the actual product. -/
lemma SZ2_eq : SZ2 = jtp2ProdInf := by
  refine zProj_ext fun n => ?_
  by_cases hn : ∃ k : ℕ, (2 * (k : ℤ)) = n
  · obtain ⟨k, rfl⟩ := hn
    rw [zProj_SZ2 k, zProj_jtp2ProdInf k]
  · rw [zProj_SZ2_zero hn, zProj_jtp2Prod_odd hn]

/-! ### `SZ2inv = map invertHom SZ2` (the `z ↦ z⁻¹` mirror), and `= map invertHom jtp2ProdInf = P_{z⁻²}`. -/

lemma coeff_SZ2term_single (p k : ℕ) :
    coeff p (SZ2term k) = Finsupp.single (2 * (k : ℤ)) ((-1 : ℤ) ^ k * szc p k) := by
  ext n
  rw [SZ2term, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply, Finsupp.single_apply, szc]
  split_ifs with h <;> [rw [mul_comm]; rfl]

lemma coeff_SZ2invTerm_single (p k : ℕ) :
    coeff p (SZ2invTerm k) = Finsupp.single (-(2 * (k : ℤ))) ((-1 : ℤ) ^ k * szc p k) := by
  ext n
  rw [SZ2invTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply, Finsupp.single_apply, szc]
  split_ifs with h <;> [rw [mul_comm]; rfl]

lemma map_invert_SZ2 : PowerSeries.map invertHom SZ2 = SZ2inv := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, coeff_SZ2 (le_refl (m + 1)), coeff_SZ2inv (le_refl (m + 1)),
      SZ2finite, SZ2invFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coeff_SZ2term_single, coeff_SZ2invTerm_single, invert_single]

/-- **`SZ2inv = map invertHom jtp2ProdInf = P_{z⁻²}`**. -/
lemma SZ2inv_eq : SZ2inv = PowerSeries.map invertHom jtp2ProdInf := by
  rw [← map_invert_SZ2, SZ2_eq]

end MockTheta5.JTP
