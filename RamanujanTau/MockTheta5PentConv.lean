/-
# Euler pentagonal — stone: the z-convolution (base-`q³`), foundation

Base-`q³` analogue of `MockTheta5TriangularConv`. The bilateral assembly convolves the two one-sided
Cauchy factors on their sum representations:

  `PZ    = Σ_{k≥0} (q^{e(k)}  /(q³;q³)_k)·zᵏ`      (`= pentProdAInf`),
  `PZ1inv = Σ_{k≥0} (q^{e(−k)}/(q³;q³)_k)·z⁻ᵏ`      (`= map invertHom pentProdBInf`),

with `e(k)=3·C(k,2)+k`, `e(−k)=3·C(k,2)+2k`. Their z-Cauchy product collapses to `X^{e(N)}·E3(rectInf N)`
= `X^{e(N)}/(q³;q³)_∞` (`durfee_rect_base_q3`), via the exponent identity `e(N)+3(j²+Nj)=e(N+j)+e(−j)`.
Here: the sum objects, the `single`-coefficients, and the Durfee-summand recognition. No `sorry`.
-/
import RamanujanTau.MockTheta5PentProdB

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-! ### sum-form Cauchy objects -/

noncomputable def pcCoef (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k)))
noncomputable def pcCoef1 (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (X ^ (3 * k.choose 2 + 2 * k) * Ring.inverse (E3 (qfac k)))

noncomputable def PZterm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  pcCoef k * PowerSeries.C (LaurentPolynomial.T (k : ℤ))
noncomputable def PZ1invTerm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  pcCoef1 k * PowerSeries.C (LaurentPolynomial.T (-(k : ℤ)))

lemma PZterm_coeff_zero {k m : ℕ} (h : m < 3 * k.choose 2 + k) : coeff m (PZterm k) = 0 := by
  rw [PZterm, PowerSeries.coeff_mul_C, pcCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (3 * k.choose 2 + k) m h, map_zero, zero_mul]

lemma PZ1invTerm_coeff_zero {k m : ℕ} (h : m < 3 * k.choose 2 + 2 * k) : coeff m (PZ1invTerm k) = 0 := by
  rw [PZ1invTerm, PowerSeries.coeff_mul_C, pcCoef1, PowerSeries.coeff_map,
      show coeff m (X ^ (3 * k.choose 2 + 2 * k) * Ring.inverse (E3 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (3 * k.choose 2 + 2 * k) m h, map_zero, zero_mul]

/-- `e(k) = 3·C(k,2)+k ≥ k` (fast growth ⇒ `m+1` stabilization, no slow-growth issue). -/
lemma e_ge (k : ℕ) : k ≤ 3 * k.choose 2 + k := Nat.le_add_left k _

noncomputable def PZfinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, PZterm k
noncomputable def PZ : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (PZfinite (m + 1))

lemma coeff_PZ_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N →
    coeff m (PZfinite N) = coeff m (PZfinite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : PZfinite (N + 1) = PZfinite N + PZterm N := by
          rw [PZfinite, PZfinite, Finset.sum_range_succ]
        rw [hsucc, map_add, PZterm_coeff_zero (by have := e_ge N; omega), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_PZ {m M : ℕ} (hM : m + 1 ≤ M) : coeff m PZ = coeff m (PZfinite M) := by
  rw [PZ, coeff_mk, coeff_PZ_stable (Nat.lt_succ_self m) hM]

noncomputable def PZ1invFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∑ k ∈ Finset.range M, PZ1invTerm k
noncomputable def PZ1inv : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (PZ1invFinite (m + 1))

lemma coeff_PZ1inv_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N →
    coeff m (PZ1invFinite N) = coeff m (PZ1invFinite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : PZ1invFinite (N + 1) = PZ1invFinite N + PZ1invTerm N := by
          rw [PZ1invFinite, PZ1invFinite, Finset.sum_range_succ]
        rw [hsucc, map_add, PZ1invTerm_coeff_zero (by have := e_ge N; omega), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_PZ1inv {m M : ℕ} (hM : m + 1 ≤ M) : coeff m PZ1inv = coeff m (PZ1invFinite M) := by
  rw [PZ1inv, coeff_mk, coeff_PZ1inv_stable (Nat.lt_succ_self m) hM]

/-! ### single-coefficients and the Durfee-summand recognition -/

noncomputable def pzc (p k : ℕ) : ℤ := coeff p (X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k)))
noncomputable def pzc1 (p k : ℕ) : ℤ := coeff p (X ^ (3 * k.choose 2 + 2 * k) * Ring.inverse (E3 (qfac k)))

lemma coeff_PZterm_single (p k : ℕ) : coeff p (PZterm k) = Finsupp.single (k : ℤ) (pzc p k) := by
  rw [PZterm, PowerSeries.coeff_mul_C, pcCoef, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T]
  rfl

lemma coeff_PZ1invTerm_single (r j : ℕ) :
    coeff r (PZ1invTerm j) = Finsupp.single (-(j : ℤ)) (pzc1 r j) := by
  rw [PZ1invTerm, PowerSeries.coeff_mul_C, pcCoef1, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T]
  rfl

lemma pzc_zero (p k : ℕ) (h : p < 3 * k.choose 2 + k) : pzc p k = 0 := by
  rw [pzc]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h
lemma pzc1_zero (p k : ℕ) (h : p < 3 * k.choose 2 + 2 * k) : pzc1 p k = 0 := by
  rw [pzc1]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h

/-- exponent bookkeeping `e(N) + 3(j²+Nj) = e(N+j) + e(−j)`. -/
lemma pent_exp (N j : ℕ) :
    (3 * N.choose 2 + N) + 3 * (j ^ 2 + N * j)
      = (3 * (N + j).choose 2 + (N + j)) + (3 * j.choose 2 + 2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : N + (j + 1) = (N + j) + 1 := by ring
      have h2 : N * (j + 1) = N * j + N := by ring
      have h3 : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
      rw [h1, choose_two_succ, choose_two_succ]
      omega

/-- `E3 (rectTerm N j) = q^{3(j²+Nj)}/((q³;q³)_j·(q³;q³)_{N+j})`. -/
lemma E3_rectTerm (N j : ℕ) :
    E3 (rectTerm N j)
      = X ^ (3 * (j ^ 2 + N * j)) * Ring.inverse (E3 (qfac j)) * Ring.inverse (E3 (qfac (N + j))) := by
  rw [rectTerm, map_mul, map_mul, map_pow, E3_X, E3_inverse_qfac, E3_inverse_qfac, ← pow_mul]

/-- **the Durfee summand recognition**: `q^{e(N)}·E3(rectTerm N j)` is the assembled Cauchy-product summand. -/
lemma pent_rectTerm (N j : ℕ) :
    X ^ (3 * N.choose 2 + N) * E3 (rectTerm N j)
      = X ^ (3 * (N + j).choose 2 + (N + j)) * Ring.inverse (E3 (qfac (N + j))) *
          (X ^ (3 * j.choose 2 + 2 * j) * Ring.inverse (E3 (qfac j))) := by
  rw [E3_rectTerm,
      show X ^ (3 * N.choose 2 + N)
            * (X ^ (3 * (j ^ 2 + N * j)) * Ring.inverse (E3 (qfac j)) * Ring.inverse (E3 (qfac (N + j))))
        = X ^ ((3 * N.choose 2 + N) + 3 * (j ^ 2 + N * j))
            * (Ring.inverse (E3 (qfac j)) * Ring.inverse (E3 (qfac (N + j)))) from by
        rw [pow_add]; ring,
      pent_exp, pow_add]
  ring

/-! ### the z-Cauchy product collapses to the base-`q³` Durfee rectangle (`N ≥ 0`) -/

lemma prodPZ_apply (p r : ℕ) (N : ℤ) :
    (coeff p PZ * coeff r PZ1inv) N
      = ∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (r + 1),
          (if (k : ℤ) - j = N then pzc p k * pzc1 r j else 0) := by
  rw [coeff_PZ (le_refl (p + 1)), coeff_PZ1inv (le_refl (r + 1)), PZfinite, PZ1invFinite,
      map_sum, map_sum]
  simp_rw [coeff_PZterm_single, coeff_PZ1invTerm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

lemma kcollapse_pent (p N j : ℕ) (c : ℤ) :
    ∑ k ∈ Finset.range (p + 1), (if (k : ℤ) - (j : ℤ) = (N : ℤ) then pzc p k * c else 0)
      = pzc p (N + j) * c := by
  rw [Finset.sum_eq_single (N + j)]
  · rw [if_pos (by push_cast; ring)]
  · intro k _ hk; rw [if_neg (by omega)]
  · intro hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [if_pos (by push_cast; ring), pzc_zero p (N + j) (by have := e_ge (N + j); omega), zero_mul]

lemma prodPZ_collapsed (p r N : ℕ) :
    (coeff p PZ * coeff r PZ1inv) (N : ℤ) = ∑ j ∈ Finset.range (r + 1), pzc p (N + j) * pzc1 r j := by
  rw [prodPZ_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => kcollapse_pent p N j (pzc1 r j)

lemma coeff_rhs_pent (N m : ℕ) :
    coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectInf N))
      = ∑ j ∈ Finset.range (m + 1), coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectTerm N j)) := by
  have hstab : coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectInf N))
      = coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectPartial N (m + 1))) := by
    have hdvd : (X : PowerSeries ℤ) ^ (m + 1) ∣ (E3 (rectInf N) - E3 (rectPartial N (m + 1))) := by
      obtain ⟨g, hg⟩ : (X : PowerSeries ℤ) ^ (m + 1) ∣ (rectInf N - rectPartial N (m + 1)) := by
        rw [PowerSeries.X_pow_dvd_iff]; intro i hi
        rw [map_sub, coeff_rectInf N (show i + 1 ≤ m + 1 by omega), sub_self]
      rw [← map_sub, hg, map_mul, map_pow, E3_X, ← pow_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _
    obtain ⟨g2, hg2⟩ := hdvd
    have hkey : X ^ (3 * N.choose 2 + N) * E3 (rectInf N)
        - X ^ (3 * N.choose 2 + N) * E3 (rectPartial N (m + 1))
          = X ^ ((3 * N.choose 2 + N) + (m + 1)) * g2 := by
      rw [← mul_sub, hg2, ← mul_assoc, ← pow_add]
    have hz : coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectInf N))
        - coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectPartial N (m + 1))) = 0 := by
      rw [← map_sub, hkey]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ m (by omega)
    exact sub_eq_zero.mp hz
  rw [hstab, rectPartial, map_sum, Finset.mul_sum, map_sum]

lemma coeff_rhs_pzc (N m j : ℕ) :
    coeff m (X ^ (3 * N.choose 2 + N) * E3 (rectTerm N j))
      = ∑ pr ∈ Finset.antidiagonal m, pzc pr.1 (N + j) * pzc1 pr.2 j := by
  rw [pent_rectTerm, PowerSeries.coeff_mul]
  rfl

lemma zProj_PZ_PZ1inv (N : ℕ) :
    zProj (N : ℤ) (PZ * PZ1inv) = X ^ (3 * N.choose 2 + N) * E3 (rectInf N) := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, coeff_rhs_pent]
  simp_rw [prodPZ_collapsed, coeff_rhs_pzc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [Finset.mem_antidiagonal] at hpr
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun j _ hj => ?_)
  simp only [Finset.mem_range, not_lt] at hj
  rw [pzc1_zero pr.2 j (by have := Nat.le_add_left (2 * j) (3 * j.choose 2); omega), mul_zero]

/-! ### the z-Cauchy product at NEGATIVE z-degree -/

lemma pent_exp_neg (M k : ℕ) :
    (3 * M.choose 2 + 2 * M) + 3 * (k ^ 2 + M * k)
      = (3 * k.choose 2 + k) + (3 * (k + M).choose 2 + 2 * (k + M)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show (k + 1).choose 2 = k.choose 2 + k from choose_two_succ k,
          show k + 1 + M = (k + M) + 1 from by ring,
          show ((k + M) + 1).choose 2 = (k + M).choose 2 + (k + M) from choose_two_succ (k + M)]
      have h2 : M * (k + 1) = M * k + M := by ring
      have h3 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega

lemma pent_rectTerm_neg (M k : ℕ) :
    X ^ (3 * M.choose 2 + 2 * M) * E3 (rectTerm M k)
      = X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k)) *
          (X ^ (3 * (k + M).choose 2 + 2 * (k + M)) * Ring.inverse (E3 (qfac (k + M)))) := by
  rw [E3_rectTerm, Nat.add_comm M k,
      show X ^ (3 * M.choose 2 + 2 * M)
            * (X ^ (3 * (k ^ 2 + M * k)) * Ring.inverse (E3 (qfac k)) * Ring.inverse (E3 (qfac (k + M))))
        = X ^ ((3 * M.choose 2 + 2 * M) + 3 * (k ^ 2 + M * k))
            * (Ring.inverse (E3 (qfac k)) * Ring.inverse (E3 (qfac (k + M)))) from by
        rw [pow_add]; ring,
      pent_exp_neg, pow_add]
  ring

lemma coeff_rhs_gen_pent (e N m : ℕ) :
    coeff m (X ^ e * E3 (rectInf N))
      = ∑ j ∈ Finset.range (m + 1), coeff m (X ^ e * E3 (rectTerm N j)) := by
  have hstab : coeff m (X ^ e * E3 (rectInf N)) = coeff m (X ^ e * E3 (rectPartial N (m + 1))) := by
    have hdvd : (X : PowerSeries ℤ) ^ (m + 1) ∣ (E3 (rectInf N) - E3 (rectPartial N (m + 1))) := by
      obtain ⟨g, hg⟩ : (X : PowerSeries ℤ) ^ (m + 1) ∣ (rectInf N - rectPartial N (m + 1)) := by
        rw [PowerSeries.X_pow_dvd_iff]; intro i hi
        rw [map_sub, coeff_rectInf N (show i + 1 ≤ m + 1 by omega), sub_self]
      rw [← map_sub, hg, map_mul, map_pow, E3_X, ← pow_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _
    obtain ⟨g2, hg2⟩ := hdvd
    have hkey : X ^ e * E3 (rectInf N) - X ^ e * E3 (rectPartial N (m + 1)) = X ^ (e + (m + 1)) * g2 := by
      rw [← mul_sub, hg2, ← mul_assoc, ← pow_add]
    have hz : coeff m (X ^ e * E3 (rectInf N)) - coeff m (X ^ e * E3 (rectPartial N (m + 1))) = 0 := by
      rw [← map_sub, hkey]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ m (by omega)
    exact sub_eq_zero.mp hz
  rw [hstab, rectPartial, map_sum, Finset.mul_sum, map_sum]

lemma jcollapse_pent_neg (r M k : ℕ) (c : ℤ) :
    ∑ j ∈ Finset.range (r + 1), (if (k : ℤ) - j = -(M : ℤ) then c * pzc1 r j else 0)
      = c * pzc1 r (k + M) := by
  rw [Finset.sum_eq_single (k + M)]
  · rw [if_pos (by push_cast; ring)]
  · intro j _ hj; rw [if_neg (by omega)]
  · intro hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [if_pos (by push_cast; ring),
        pzc1_zero r (k + M) (by have := Nat.le_add_left (2 * (k + M)) (3 * (k + M).choose 2); omega),
        mul_zero]

lemma prodPZ_collapsed_neg (p r M : ℕ) :
    (coeff p PZ * coeff r PZ1inv) (-(M : ℤ))
      = ∑ k ∈ Finset.range (p + 1), pzc p k * pzc1 r (k + M) := by
  rw [prodPZ_apply]
  exact Finset.sum_congr rfl fun k _ => jcollapse_pent_neg r M k (pzc p k)

lemma coeff_rhs_pzc_neg (M m k : ℕ) :
    coeff m (X ^ (3 * M.choose 2 + 2 * M) * E3 (rectTerm M k))
      = ∑ pr ∈ Finset.antidiagonal m, pzc pr.1 k * pzc1 pr.2 (k + M) := by
  rw [pent_rectTerm_neg, PowerSeries.coeff_mul]
  rfl

lemma zProj_PZ_PZ1inv_neg (M : ℕ) :
    zProj (-(M : ℤ)) (PZ * PZ1inv) = X ^ (3 * M.choose 2 + 2 * M) * E3 (rectInf M) := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, coeff_rhs_gen_pent (3 * M.choose 2 + 2 * M) M]
  simp_rw [prodPZ_collapsed_neg, coeff_rhs_pzc_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [Finset.mem_antidiagonal] at hpr
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun k _ hk => ?_)
  simp only [Finset.mem_range, not_lt] at hk
  rw [pzc_zero pr.1 k (by have := e_ge k; omega), zero_mul]

/-! ### the sum forms equal the products -/

lemma zProj_PZ (k : ℕ) : zProj (k : ℤ) PZ = X ^ (3 * k.choose 2 + k) * Ring.inverse (E3 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_PZ (show m + 1 ≤ m + k + 1 by omega), PZfinite, map_sum, laurentSum_apply]
  simp_rw [coeff_PZterm_single, Finsupp.single_apply, Nat.cast_inj]
  rw [Finset.sum_ite_eq' (Finset.range (m + k + 1)) k (fun i => pzc m i),
      if_pos (Finset.mem_range.mpr (by omega))]
  rfl

lemma zProj_PZ_neg {κ : ℤ} (hκ : κ < 0) : zProj κ PZ = 0 := by
  ext m
  rw [coeff_zProj, coeff_PZ (le_refl (m + 1)), PZfinite, map_sum, laurentSum_apply,
      Finset.sum_eq_zero
        (fun i _ => by rw [coeff_PZterm_single, Finsupp.single_apply, if_neg (by omega)]), map_zero]

theorem PZ_eq : PZ = pentProdAInf := by
  refine zProj_ext (fun κ => ?_)
  by_cases hκ : 0 ≤ κ
  · lift κ to ℕ using hκ with k; rw [zProj_PZ, zProj_pentProdAInf]
  · rw [not_le] at hκ; rw [zProj_PZ_neg hκ, zProj_pentProdA_neg hκ]

lemma zProj_PZ1inv (j : ℕ) :
    zProj (-(j : ℤ)) PZ1inv = X ^ (3 * j.choose 2 + 2 * j) * Ring.inverse (E3 (qfac j)) := by
  ext m
  rw [coeff_zProj, coeff_PZ1inv (show m + 1 ≤ m + j + 1 by omega), PZ1invFinite, map_sum,
      laurentSum_apply]
  simp_rw [coeff_PZ1invTerm_single, Finsupp.single_apply, neg_inj, Nat.cast_inj]
  rw [Finset.sum_ite_eq' (Finset.range (m + j + 1)) j (fun i => pzc1 m i),
      if_pos (Finset.mem_range.mpr (by omega))]
  rfl

lemma zProj_PZ1inv_pos {κ : ℤ} (hκ : 0 < κ) : zProj κ PZ1inv = 0 := by
  ext m
  rw [coeff_zProj, coeff_PZ1inv (le_refl (m + 1)), PZ1invFinite, map_sum, laurentSum_apply,
      Finset.sum_eq_zero
        (fun i _ => by rw [coeff_PZ1invTerm_single, Finsupp.single_apply, if_neg (by omega)]), map_zero]

theorem PZ1inv_eq : PZ1inv = PowerSeries.map invertHom pentProdBInf := by
  refine zProj_ext (fun κ => ?_)
  rw [zProj_map_invert]
  by_cases hκ : κ ≤ 0
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, κ = -(j : ℤ) := ⟨κ.natAbs, by omega⟩
    rw [zProj_PZ1inv, neg_neg, zProj_pentProdBInf]
  · push Not at hκ
    rw [zProj_PZ1inv_pos hκ, zProj_pentProdB_neg (show -κ < 0 by omega)]

end MockTheta5.JTP
