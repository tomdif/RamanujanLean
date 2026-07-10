/-
# Quintuple product, stone 3 (Bracket 1, part 1): the signed triangular Cauchy sums `SZA`, `SZAinv`

For Bracket 1 (`qfacInfL · P_z · P_{z⁻¹} = thetaA`) we represent the base-`q` products
`P_z = qzProdAInf = ∏_{i≥1}(1−zqⁱ)` and `P_{z⁻¹} = map invertHom qzProdBInf = ∏_{i≥0}(1−z⁻¹qⁱ)` in the Cauchy
sum-of-singles form (asymmetric: the `z`-side is *shifted*, the `z⁻¹`-side *unshifted*):

  `SZA    = Σ_{k≥0} (−1)ᵏ (q^{C(k+1,2)}/(q;q)_k) zᵏ`,   `SZAinv = Σ_{k≥0} (−1)ᵏ (q^{C(k,2)}/(q;q)_k) z^{−k}`.

These reuse `tcCoef1` (`q^{C(k+1,2)}/(q;q)_k`) and `tcCoef` (`q^{C(k,2)}/(q;q)_k`) from the triangular JTP,
placed at z-degree `±k` with sign `(−1)ᵏ`. This file builds them (with the `m+2` stabilization the slow
`C(k,2)` growth forces), their z-projections, and the **connection** `SZA = qzProdAInf`,
`SZAinv = map invertHom qzProdBInf` via `zProj_ext`. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintProdZ
import RamanujanTau.MockTheta5QuintProdZ2
import RamanujanTau.MockTheta5TriangularConv
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the `zᵏ`-term of the signed triangular Cauchy sum (shifted): `(−1)ᵏ (q^{C(k+1,2)}/(q;q)_k) zᵏ`. -/
noncomputable def SZAterm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  tcCoef1 k * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (k : ℤ))

/-- the `z^{−k}`-term of the mirror signed triangular Cauchy sum (unshifted): `(−1)ᵏ (q^{C(k,2)}/(q;q)_k) z^{−k}`. -/
noncomputable def SZAinvterm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  tcCoef k * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (-(k : ℤ)))

lemma SZAterm_coeff_zero {k m : ℕ} (h : m < (k + 1).choose 2) : coeff m (SZAterm k) = 0 := by
  rw [SZAterm, PowerSeries.coeff_mul_C, tcCoef1, PowerSeries.coeff_map,
      show coeff m (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ ((k + 1).choose 2) m h, map_zero, zero_mul]

lemma SZAinvterm_coeff_zero {k m : ℕ} (h : m < k.choose 2) : coeff m (SZAinvterm k) = 0 := by
  rw [SZAinvterm, PowerSeries.coeff_mul_C, tcCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k.choose 2) * Ring.inverse (qfac k)) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k.choose 2) m h, map_zero, zero_mul]

noncomputable def SZAfinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZAterm k
noncomputable def SZAinvFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZAinvterm k
noncomputable def SZA : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZAfinite (m + 2))
noncomputable def SZAinv : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZAinvFinite (m + 2))

lemma coeff_SZA_stable {m : ℕ} : ∀ {M N : ℕ}, m < M.choose 2 → M ≤ N →
    coeff m (SZAfinite N) = coeff m (SZAfinite M) := by
  intro M N hm hMN
  induction N with
  | zero => rw [Nat.le_zero.mp hMN]
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZAfinite (N + 1) = SZAfinite N + SZAterm N := by
          rw [SZAfinite, SZAfinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZAterm_coeff_zero (lt_of_lt_of_le hm (le_trans (Nat.choose_le_choose 2 (by omega))
              (Nat.choose_le_choose 2 (by omega)))), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZA {m M : ℕ} (hM : m + 2 ≤ M) : coeff m SZA = coeff m (SZAfinite M) := by
  rw [SZA, coeff_mk, coeff_SZA_stable (lt_choose_two_add_two m) hM]

lemma coeff_SZAinv_stable {m : ℕ} : ∀ {M N : ℕ}, m < M.choose 2 → M ≤ N →
    coeff m (SZAinvFinite N) = coeff m (SZAinvFinite M) := by
  intro M N hm hMN
  induction N with
  | zero => rw [Nat.le_zero.mp hMN]
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZAinvFinite (N + 1) = SZAinvFinite N + SZAinvterm N := by
          rw [SZAinvFinite, SZAinvFinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZAinvterm_coeff_zero (lt_of_lt_of_le hm (Nat.choose_le_choose 2 (by omega))),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZAinv {m M : ℕ} (hM : m + 2 ≤ M) : coeff m SZAinv = coeff m (SZAinvFinite M) := by
  rw [SZAinv, coeff_mk, coeff_SZAinv_stable (lt_choose_two_add_two m) hM]

/-! ### z-projections via `zProj_mapC_scaledCT` -/

lemma zProj_SZAterm (k : ℕ) (n : ℤ) :
    zProj n (SZAterm k)
      = if (k : ℤ) = n then PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k))
        else 0 := by
  rw [SZAterm, tcCoef1, zProj_mapC_scaledCT]

lemma zProj_SZAinvterm (k : ℕ) (n : ℤ) :
    zProj n (SZAinvterm k)
      = if (-(k : ℤ)) = n then PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k.choose 2) * Ring.inverse (qfac k))
        else 0 := by
  rw [SZAinvterm, tcCoef, zProj_mapC_scaledCT]

lemma zProj_SZAfinite (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (SZAfinite M)
      = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) := by
  rw [SZAfinite, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_SZAterm, if_neg (by exact_mod_cast hik)])
        (fun hc => absurd (Finset.mem_range.mpr h) hc),
      zProj_SZAterm, if_pos rfl]

lemma zProj_SZA (k : ℕ) :
    zProj (k : ℤ) SZA = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_SZA (show m + 2 ≤ m + k + 2 by omega), ← coeff_zProj,
      zProj_SZAfinite k (m + k + 2) (by omega)]

lemma zProj_SZA_neg {n : ℤ} (hn : n < 0) : zProj n SZA = 0 := by
  ext m
  rw [coeff_zProj, coeff_SZA (le_refl (m + 2)), ← coeff_zProj, SZAfinite, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_SZAterm, if_neg (by omega)])]

lemma zProj_SZAinv (k : ℕ) :
    zProj (-(k : ℤ)) SZAinv = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k.choose 2) * Ring.inverse (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_SZAinv (show m + 2 ≤ m + k + 2 by omega), ← coeff_zProj]
  rw [SZAinvFinite, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_SZAinvterm, if_neg (by omega)])
        (fun hc => absurd (Finset.mem_range.mpr (show k < m + k + 2 by omega)) hc),
      zProj_SZAinvterm, if_pos rfl]

lemma zProj_SZAinv_pos {n : ℤ} (hn : 0 < n) : zProj n SZAinv = 0 := by
  ext m
  rw [coeff_zProj, coeff_SZAinv (le_refl (m + 2)), ← coeff_zProj, SZAinvFinite, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_SZAinvterm, if_neg (by omega)])]

/-! ### The connection to the actual products -/

private lemma C_negpow (k : ℕ) : PowerSeries.C ((-1 : ℤ) ^ k) = (-1 : PowerSeries ℤ) ^ k := by
  rw [map_pow, map_neg, map_one]

/-- **`SZA = qzProdAInf = P_z`.** -/
lemma SZA_eq : SZA = qzProdAInf := by
  refine zProj_ext fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [zProj_SZA_neg hn, zProj_qzProdA_neg hn]
  · lift n to ℕ using hn with k
    rw [zProj_SZA, zProj_qzProdAInf, C_negpow]

/-- **`SZAinv = map invertHom qzProdBInf = P_{z⁻¹}`.** -/
lemma SZAinv_eq : SZAinv = PowerSeries.map invertHom qzProdBInf := by
  refine zProj_ext fun n => ?_
  rw [zProj_map_invert]
  rcases lt_or_ge 0 n with hn | hn
  · rw [zProj_SZAinv_pos hn, zProj_qzProdB_neg (by omega : -n < 0)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
    rw [zProj_SZAinv, neg_neg, zProj_qzProdBInf, C_negpow]

end MockTheta5.JTP
