/-
# Triangular JTP, stone 3C stage 1: the one-sided Cauchy *sum* objects (for the z-convolution)

The bilateral assembly convolves the two one-sided factors on their **sum** representations (whose
coefficients are single `z`-monomials), as in `MockTheta5CauchySum`. This file builds

  `TZ    = Σ_{k≥0} (q^{C(k,2)}  /(q;q)_k)·zᵏ`      (`= triProdQInf`,   stone 2),
  `TZ1inv = Σ_{k≥0} (q^{C(k+1,2)}/(q;q)_k)·z⁻ᵏ`     (`= map invertHom triProdQ1Inf`, stone 2b),

by coefficient stabilization. **Subtlety vs. the square case:** the triangular exponent `C(k,2)=k(k−1)/2`
grows *slowly* (`C(1,2)=0`, `C(2,2)=1`), so `TZterm k` touches low coefficients; the stabilization index must
be governed by `C(k,2)` (bound `m < M.choose 2`), not by `k` directly. No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularProd2
import RamanujanTau.MockTheta5DurfeeBase

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- `m < (m+2).choose 2` — the stabilization index `m+2` clears every term reaching `coeff m`. -/
lemma lt_choose_two_add_two (m : ℕ) : m < (m + 2).choose 2 := by
  rw [Nat.choose_two_right]
  have hle : 2 * (m + 1) ≤ (m + 2) * (m + 2 - 1) := by
    have : m + 2 - 1 = m + 1 := by omega
    rw [this]; nlinarith
  set P := (m + 2) * (m + 2 - 1) with hP
  omega

/-- lifted `z`-side Cauchy coefficient `q^{C(k,2)}/(q;q)_k`. -/
noncomputable def tcCoef (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (X ^ (k.choose 2) * Ring.inverse (qfac k))

/-- lifted shifted (`z⁻¹`-side) Cauchy coefficient `q^{C(k+1,2)}/(q;q)_k`. -/
noncomputable def tcCoef1 (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k))

noncomputable def TZterm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  tcCoef k * PowerSeries.C (LaurentPolynomial.T (k : ℤ))
noncomputable def TZ1invTerm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  tcCoef1 k * PowerSeries.C (LaurentPolynomial.T (-(k : ℤ)))

lemma TZterm_coeff_zero {k m : ℕ} (h : m < k.choose 2) : coeff m (TZterm k) = 0 := by
  rw [TZterm, PowerSeries.coeff_mul_C, tcCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k.choose 2) * Ring.inverse (qfac k)) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k.choose 2) m h, map_zero, zero_mul]

lemma TZ1invTerm_coeff_zero {k m : ℕ} (h : m < (k + 1).choose 2) : coeff m (TZ1invTerm k) = 0 := by
  rw [TZ1invTerm, PowerSeries.coeff_mul_C, tcCoef1, PowerSeries.coeff_map,
      show coeff m (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k)) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ ((k + 1).choose 2) m h, map_zero, zero_mul]

noncomputable def TZfinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, TZterm k
noncomputable def TZ : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (TZfinite (m + 2))

lemma coeff_TZ_stable {m : ℕ} : ∀ {M N : ℕ}, m < M.choose 2 → M ≤ N →
    coeff m (TZfinite N) = coeff m (TZfinite M) := by
  intro M N hm hMN
  induction N with
  | zero => rw [Nat.le_zero.mp hMN]
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : TZfinite (N + 1) = TZfinite N + TZterm N := by
          rw [TZfinite, TZfinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            TZterm_coeff_zero (lt_of_lt_of_le hm (Nat.choose_le_choose 2 (by omega))),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_TZ {m M : ℕ} (hM : m + 2 ≤ M) : coeff m TZ = coeff m (TZfinite M) := by
  rw [TZ, coeff_mk, coeff_TZ_stable (lt_choose_two_add_two m) hM]

noncomputable def TZ1invFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∑ k ∈ Finset.range M, TZ1invTerm k
noncomputable def TZ1inv : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (TZ1invFinite (m + 2))

lemma coeff_TZ1inv_stable {m : ℕ} : ∀ {M N : ℕ}, m < M.choose 2 → M ≤ N →
    coeff m (TZ1invFinite N) = coeff m (TZ1invFinite M) := by
  intro M N hm hMN
  induction N with
  | zero => rw [Nat.le_zero.mp hMN]
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : TZ1invFinite (N + 1) = TZ1invFinite N + TZ1invTerm N := by
          rw [TZ1invFinite, TZ1invFinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            TZ1invTerm_coeff_zero
              (lt_of_lt_of_le hm (le_trans (Nat.choose_le_choose 2 (by omega))
                (Nat.choose_le_choose 2 (Nat.le_succ N)))),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_TZ1inv {m M : ℕ} (hM : m + 2 ≤ M) : coeff m TZ1inv = coeff m (TZ1invFinite M) := by
  rw [TZ1inv, coeff_mk, coeff_TZ1inv_stable (lt_choose_two_add_two m) hM]

/-! ### Cauchy coefficients as single `z`-monomials, and the Durfee-summand recognition -/

/-- the `k`-th `z`-side Cauchy coefficient at q-degree `p`: `[q^p] q^{C(k,2)}/(q;q)_k`. -/
noncomputable def tzc (p k : ℕ) : ℤ := coeff p (X ^ (k.choose 2) * Ring.inverse (qfac k))
/-- the `k`-th `z⁻¹`-side (shifted) Cauchy coefficient at q-degree `p`: `[q^p] q^{C(k+1,2)}/(q;q)_k`. -/
noncomputable def tzc1 (p k : ℕ) : ℤ := coeff p (X ^ ((k + 1).choose 2) * Ring.inverse (qfac k))

lemma coeff_TZterm_single (p k : ℕ) : coeff p (TZterm k) = Finsupp.single (k : ℤ) (tzc p k) := by
  rw [TZterm, PowerSeries.coeff_mul_C, tcCoef, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T]
  rfl

lemma coeff_TZ1invTerm_single (r j : ℕ) :
    coeff r (TZ1invTerm j) = Finsupp.single (-(j : ℤ)) (tzc1 r j) := by
  rw [TZ1invTerm, PowerSeries.coeff_mul_C, tcCoef1, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T]
  rfl

/-- exponent bookkeeping `C(N,2) + (j²+Nj) = C(N+j,2) + C(j+1,2)` (the match with `rectTerm N j`). -/
lemma tri_exp (N j : ℕ) : N.choose 2 + (j ^ 2 + N * j) = (N + j).choose 2 + (j + 1).choose 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : N + (j + 1) = (N + j) + 1 := by ring
      have h2 : N * (j + 1) = N * j + N := by ring
      have h3 : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
      rw [h1, choose_two_succ, choose_two_succ]
      omega

/-- **the Durfee summand recognition**: `q^{C(N,2)}·rectTerm N j` is the assembled Cauchy-product summand
`(q^{C(N+j,2)}/(q;q)_{N+j})·(q^{C(j+1,2)}/(q;q)_j)`, via `tri_exp`. -/
lemma tri_rectTerm (N j : ℕ) :
    X ^ (N.choose 2) * rectTerm N j
      = X ^ ((N + j).choose 2) * Ring.inverse (qfac (N + j)) *
          (X ^ ((j + 1).choose 2) * Ring.inverse (qfac j)) := by
  rw [rectTerm,
      show X ^ (N.choose 2) * (X ^ (j ^ 2 + N * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (N + j)))
        = X ^ (N.choose 2 + (j ^ 2 + N * j)) * (Ring.inverse (qfac j) * Ring.inverse (qfac (N + j))) from by
        rw [pow_add]; ring,
      tri_exp, pow_add]
  ring

/-! ### The z-Cauchy product `TZ · TZ1inv` collapses to the Durfee rectangle -/

lemma tzc_zero (p k : ℕ) (h : p < k.choose 2) : tzc p k = 0 := by
  rw [tzc]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h
lemma tzc1_zero (p k : ℕ) (h : p < (k + 1).choose 2) : tzc1 p k = 0 := by
  rw [tzc1]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h

/-- the `z^N` coefficient of `coeff p TZ · coeff r TZ1inv` is the diagonal double-sum `k − j = N`. -/
lemma prodTZ_apply (p r : ℕ) (N : ℤ) :
    (coeff p TZ * coeff r TZ1inv) N
      = ∑ k ∈ Finset.range (p + 2), ∑ j ∈ Finset.range (r + 2),
          (if (k : ℤ) - j = N then tzc p k * tzc1 r j else 0) := by
  rw [coeff_TZ (le_refl (p + 2)), coeff_TZ1inv (le_refl (r + 2)), TZfinite, TZ1invFinite,
      map_sum, map_sum]
  simp_rw [coeff_TZterm_single, coeff_TZ1invTerm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

/-- collapse the `k`-sum against the diagonal `k − j = N` (so `k = N + j`). -/
lemma kcollapse_tri (p N j : ℕ) (c : ℤ) :
    ∑ k ∈ Finset.range (p + 2), (if (k : ℤ) - (j : ℤ) = (N : ℤ) then tzc p k * c else 0)
      = tzc p (N + j) * c := by
  rw [Finset.sum_eq_single (N + j)]
  · rw [if_pos (by push_cast; ring)]
  · intro k _ hk; rw [if_neg (by omega)]
  · intro hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [if_pos (by push_cast; ring),
        tzc_zero p (N + j) (by have := lt_choose_two_add_two p
                               have := Nat.choose_le_choose 2 (show p + 2 ≤ N + j by omega); omega),
        zero_mul]

lemma prodTZ_collapsed (p r N : ℕ) :
    (coeff p TZ * coeff r TZ1inv) (N : ℤ) = ∑ j ∈ Finset.range (r + 2), tzc p (N + j) * tzc1 r j := by
  rw [prodTZ_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => kcollapse_tri p N j (tzc1 r j)

/-- `coeff m (q^{C(N,2)}·rectInf N)` as a finite sum over Durfee-rectangle terms. -/
lemma coeff_rhs_tri (N m : ℕ) :
    coeff m (X ^ (N.choose 2) * rectInf N)
      = ∑ j ∈ Finset.range (m + 2), coeff m (X ^ (N.choose 2) * rectTerm N j) := by
  have hstab : coeff m (X ^ (N.choose 2) * rectInf N)
      = coeff m (X ^ (N.choose 2) * rectPartial N (m + 2)) := by
    have hdvd : (X : PowerSeries ℤ) ^ (m + 2) ∣ (rectInf N - rectPartial N (m + 2)) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro i hi
      rw [map_sub, coeff_rectInf N (show i + 1 ≤ m + 2 by omega), sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hkey : X ^ (N.choose 2) * rectInf N - X ^ (N.choose 2) * rectPartial N (m + 2)
        = X ^ (N.choose 2 + (m + 2)) * g := by
      rw [← mul_sub, hg, ← mul_assoc, ← pow_add]
    have hz : coeff m (X ^ (N.choose 2) * rectInf N)
        - coeff m (X ^ (N.choose 2) * rectPartial N (m + 2)) = 0 := by
      rw [← map_sub, hkey]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ m (by omega)
    exact sub_eq_zero.mp hz
  rw [hstab, rectPartial, Finset.mul_sum, map_sum]

/-- the `rectTerm` coefficient as a `tzc`-antidiagonal sum (one `coeff_mul`, defeq fold). -/
lemma coeff_rhs_tzc (N m j : ℕ) :
    coeff m (X ^ (N.choose 2) * rectTerm N j)
      = ∑ pr ∈ Finset.antidiagonal m, tzc pr.1 (N + j) * tzc1 pr.2 j := by
  rw [tri_rectTerm, PowerSeries.coeff_mul]
  rfl

/-- **the z-Cauchy product `TZ · TZ1inv` at z-degree `N ≥ 0`** equals `q^{C(N,2)}·rectInf N`. With
`durfee_rect_base` this is `q^{C(N,2)}/(q;q)_∞`. -/
lemma zProj_TZ_TZ1inv (N : ℕ) : zProj (N : ℤ) (TZ * TZ1inv) = X ^ (N.choose 2) * rectInf N := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, coeff_rhs_tri]
  simp_rw [prodTZ_collapsed, coeff_rhs_tzc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [Finset.mem_antidiagonal] at hpr
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun j _ hj => ?_)
  simp only [Finset.mem_range, not_lt] at hj
  rw [tzc1_zero pr.2 j (by rw [choose_two_succ]; omega), mul_zero]

/-! ### The sum forms equal the products (`TZ = triProdQInf`, `TZ1inv = map invert triProdQ1Inf`) -/

lemma zProj_TZ (k : ℕ) : zProj (k : ℤ) TZ = X ^ (k.choose 2) * Ring.inverse (qfac k) := by
  ext m
  rw [coeff_zProj, coeff_TZ (show m + 2 ≤ m + k + 2 by omega), TZfinite, map_sum, laurentSum_apply]
  simp_rw [coeff_TZterm_single, Finsupp.single_apply, Nat.cast_inj]
  rw [Finset.sum_ite_eq' (Finset.range (m + k + 2)) k (fun i => tzc m i),
      if_pos (Finset.mem_range.mpr (by omega))]
  rfl

lemma zProj_TZ_neg {κ : ℤ} (hκ : κ < 0) : zProj κ TZ = 0 := by
  ext m
  rw [coeff_zProj, coeff_TZ (le_refl (m + 2)), TZfinite, map_sum, laurentSum_apply,
      Finset.sum_eq_zero
        (fun i _ => by rw [coeff_TZterm_single, Finsupp.single_apply, if_neg (by omega)]), map_zero]

theorem TZ_eq : TZ = triProdQInf := by
  refine zProj_ext (fun κ => ?_)
  by_cases hκ : 0 ≤ κ
  · lift κ to ℕ using hκ with k; rw [zProj_TZ, zProj_triProdQInf]
  · rw [not_le] at hκ; rw [zProj_TZ_neg hκ, zProj_triProdQ_neg hκ]

lemma zProj_TZ1inv (j : ℕ) :
    zProj (-(j : ℤ)) TZ1inv = X ^ ((j + 1).choose 2) * Ring.inverse (qfac j) := by
  ext m
  rw [coeff_zProj, coeff_TZ1inv (show m + 2 ≤ m + j + 2 by omega), TZ1invFinite, map_sum,
      laurentSum_apply]
  simp_rw [coeff_TZ1invTerm_single, Finsupp.single_apply, neg_inj, Nat.cast_inj]
  rw [Finset.sum_ite_eq' (Finset.range (m + j + 2)) j (fun i => tzc1 m i),
      if_pos (Finset.mem_range.mpr (by omega))]
  rfl

lemma zProj_TZ1inv_pos {κ : ℤ} (hκ : 0 < κ) : zProj κ TZ1inv = 0 := by
  ext m
  rw [coeff_zProj, coeff_TZ1inv (le_refl (m + 2)), TZ1invFinite, map_sum, laurentSum_apply,
      Finset.sum_eq_zero
        (fun i _ => by rw [coeff_TZ1invTerm_single, Finsupp.single_apply, if_neg (by omega)]), map_zero]

theorem TZ1inv_eq : TZ1inv = PowerSeries.map invertHom triProdQ1Inf := by
  refine zProj_ext (fun κ => ?_)
  rw [zProj_map_invert]
  by_cases hκ : κ ≤ 0
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, κ = -(j : ℤ) := ⟨κ.natAbs, by omega⟩
    rw [zProj_TZ1inv, neg_neg, zProj_triProdQ1Inf]
  · push Not at hκ
    rw [zProj_TZ1inv_pos hκ, zProj_triProdQ1_neg (show -κ < 0 by omega)]

/-! ### The z-Cauchy product at NEGATIVE z-degree (the products are asymmetric — no free symmetry) -/

/-- swapped exponent bookkeeping `C(M+1,2) + (k²+Mk) = C(k,2) + C(k+M+1,2)`. -/
lemma tri_exp_neg (M k : ℕ) : (M + 1).choose 2 + (k ^ 2 + M * k) = k.choose 2 + (k + M + 1).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show (k + 1).choose 2 = k.choose 2 + k from choose_two_succ k,
          show k + 1 + M + 1 = (k + M + 1) + 1 from by ring,
          show ((k + M + 1) + 1).choose 2 = (k + M + 1).choose 2 + (k + M + 1) from choose_two_succ (k + M + 1)]
      have h2 : M * (k + 1) = M * k + M := by ring
      have h3 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega

lemma tri_rectTerm_neg (M k : ℕ) :
    X ^ ((M + 1).choose 2) * rectTerm M k
      = X ^ (k.choose 2) * Ring.inverse (qfac k) *
          (X ^ ((k + M + 1).choose 2) * Ring.inverse (qfac (k + M))) := by
  rw [rectTerm, Nat.add_comm M k,
      show X ^ ((M + 1).choose 2)
            * (X ^ (k ^ 2 + M * k) * Ring.inverse (qfac k) * Ring.inverse (qfac (k + M)))
        = X ^ ((M + 1).choose 2 + (k ^ 2 + M * k))
            * (Ring.inverse (qfac k) * Ring.inverse (qfac (k + M))) from by rw [pow_add]; ring,
      tri_exp_neg, pow_add]
  ring

/-- generalized `coeff_rhs_tri` with an arbitrary prefactor exponent. -/
lemma coeff_rhs_gen (e N m : ℕ) :
    coeff m (X ^ e * rectInf N) = ∑ j ∈ Finset.range (m + 2), coeff m (X ^ e * rectTerm N j) := by
  have hstab : coeff m (X ^ e * rectInf N) = coeff m (X ^ e * rectPartial N (m + 2)) := by
    have hdvd : (X : PowerSeries ℤ) ^ (m + 2) ∣ (rectInf N - rectPartial N (m + 2)) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro i hi
      rw [map_sub, coeff_rectInf N (show i + 1 ≤ m + 2 by omega), sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hkey : X ^ e * rectInf N - X ^ e * rectPartial N (m + 2) = X ^ (e + (m + 2)) * g := by
      rw [← mul_sub, hg, ← mul_assoc, ← pow_add]
    have hz : coeff m (X ^ e * rectInf N) - coeff m (X ^ e * rectPartial N (m + 2)) = 0 := by
      rw [← map_sub, hkey]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ m (by omega)
    exact sub_eq_zero.mp hz
  rw [hstab, rectPartial, Finset.mul_sum, map_sum]

/-- collapse the `j`-sum against the negative diagonal `k − j = −M` (so `j = k + M`). -/
lemma jcollapse_neg (r M k : ℕ) (c : ℤ) :
    ∑ j ∈ Finset.range (r + 2), (if (k : ℤ) - j = -(M : ℤ) then c * tzc1 r j else 0)
      = c * tzc1 r (k + M) := by
  rw [Finset.sum_eq_single (k + M)]
  · rw [if_pos (by push_cast; ring)]
  · intro j _ hj; rw [if_neg (by omega)]
  · intro hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [if_pos (by push_cast; ring), tzc1_zero r (k + M) (by rw [choose_two_succ]; omega), mul_zero]

lemma prodTZ_collapsed_neg (p r M : ℕ) :
    (coeff p TZ * coeff r TZ1inv) (-(M : ℤ))
      = ∑ k ∈ Finset.range (p + 2), tzc p k * tzc1 r (k + M) := by
  rw [prodTZ_apply]
  exact Finset.sum_congr rfl fun k _ => jcollapse_neg r M k (tzc p k)

lemma coeff_rhs_tzc_neg (M m k : ℕ) :
    coeff m (X ^ ((M + 1).choose 2) * rectTerm M k)
      = ∑ pr ∈ Finset.antidiagonal m, tzc pr.1 k * tzc1 pr.2 (k + M) := by
  rw [tri_rectTerm_neg, PowerSeries.coeff_mul]
  rfl

/-- **the z-Cauchy product at z-degree `−M ≤ 0`** equals `q^{C(M+1,2)}·rectInf M` (`= q^{C(−M,2)}/(q;q)_∞`). -/
lemma zProj_TZ_TZ1inv_neg (M : ℕ) :
    zProj (-(M : ℤ)) (TZ * TZ1inv) = X ^ ((M + 1).choose 2) * rectInf M := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, coeff_rhs_gen ((M + 1).choose 2) M]
  simp_rw [prodTZ_collapsed_neg, coeff_rhs_tzc_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [Finset.mem_antidiagonal] at hpr
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun k _ hk => ?_)
  simp only [Finset.mem_range, not_lt] at hk
  rw [tzc_zero pr.1 k (by have := lt_choose_two_add_two pr.1
                          have := Nat.choose_le_choose 2 (show pr.1 + 2 ≤ k by omega); omega), zero_mul]

end MockTheta5.JTP
