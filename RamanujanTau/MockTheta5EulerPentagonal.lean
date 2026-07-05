/-
# Euler's pentagonal number theorem — reassembly and capstone

The `z=−1` evaluation of `bilateral_pent_JTP` gives `(q³;q³)_∞ · ∏(1−q^{3i+1}) · ∏(1−q^{3i+2}) = pentSeries`.
Reassembling the three residue-class products mod 3 into `∏_{k≥1}(1−qᵏ) = (q;q)_∞` yields

  **`euler_pentagonal`:**  `(q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}`.

This file: the finite residue-class split `qfac_split` (`(q;q)_{3n} = ∏(1−q^{3i+1})∏(1−q^{3i+2})∏(1−q^{3i+3})`)
and `E3 (qfac n) = ∏(1−q^{3i+3})`. No `sorry`.
-/
import RamanujanTau.MockTheta5PentEval

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- `E3 (q;q)_n = ∏_{i<n}(1 − q^{3i+3})`. -/
lemma E3_qfac (n : ℕ) : E3 (qfac n) = ∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 3)) := by
  rw [qfac, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_sub, map_one, map_pow, E3_X, ← pow_mul, show 3 * (i + 1) = 3 * i + 3 from by ring]

/-- **residue-class split mod 3**: `(q;q)_{3n} = ∏(1−q^{3i+1})·∏(1−q^{3i+2})·∏(1−q^{3i+3})`. -/
lemma qfac_split (n : ℕ) :
    qfac (3 * n)
      = (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1))) * (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 2)))
          * ∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 3)) := by
  induction n with
  | zero => simp [qfac]
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
          show 3 * (n + 1) = 3 * n + 1 + 1 + 1 from by ring, qfac, Finset.prod_range_succ,
          Finset.prod_range_succ, Finset.prod_range_succ, ← qfac, ih]
      ring_nf

/-! ### the infinite reassembly and the capstone -/

lemma coeff_FAInf {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k FAInf = coeff k (∏ i ∈ Finset.range N, (1 - X ^ (3 * i + 1))) := by
  rw [← map_evm1_pentProdAInf, PowerSeries.coeff_map, coeff_pentProdAInf hN,
      ← PowerSeries.coeff_map, map_evm1_pentProdA]

lemma coeff_FBInf {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k FBInf = coeff k (∏ i ∈ Finset.range N, (1 - X ^ (3 * i + 2))) := by
  rw [← map_evm1_pentProdBInf, PowerSeries.coeff_map, coeff_pentProdBInf hN,
      ← PowerSeries.coeff_map, map_evm1_pentProdB]

lemma coeff_E3qfacInf {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k (E3 qfacInf) = coeff k (∏ i ∈ Finset.range N, (1 - X ^ (3 * i + 3))) := by
  rw [← E3_qfac]
  have hdvd : (X : PowerSeries ℤ) ^ (k + 1) ∣ (E3 qfacInf - E3 (qfac N)) := by
    obtain ⟨g, hg⟩ : (X : PowerSeries ℤ) ^ N ∣ (qfacInf - qfac N) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro i hi
      rw [map_sub, coeff_qfacInf (show i + 1 ≤ N by omega), sub_self]
    rw [← map_sub, hg, map_mul, map_pow, E3_X, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _
  obtain ⟨g, hg⟩ := hdvd
  have hz : coeff k (E3 qfacInf) - coeff k (E3 (qfac N)) = 0 := by
    rw [← map_sub, hg]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ k (by omega)
  exact sub_eq_zero.mp hz

/-- **residue-class reassembly**: `(q³;q³)_∞ · ∏(1−q^{3i+1}) · ∏(1−q^{3i+2}) = (q;q)_∞`. -/
lemma reassembly : E3 qfacInf * FAInf * FBInf = qfacInf := by
  ext m
  have hF3 : (X : PowerSeries ℤ) ^ (m + 1) ∣ (E3 qfacInf - ∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 3))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, coeff_E3qfacInf (show i + 1 ≤ m + 1 by omega), sub_self]
  have hFA : (X : PowerSeries ℤ) ^ (m + 1) ∣ (FAInf - ∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 1))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, coeff_FAInf (show i + 1 ≤ m + 1 by omega), sub_self]
  have hFB : (X : PowerSeries ℤ) ^ (m + 1) ∣ (FBInf - ∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 2))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, coeff_FBInf (show i + 1 ≤ m + 1 by omega), sub_self]
  rw [coeff_mul_congr_right hFB,
      show E3 qfacInf * FAInf * (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 2)))
          = E3 qfacInf * (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 2))) * FAInf from by ring,
      coeff_mul_congr_right hFA,
      show E3 qfacInf * (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 2)))
            * (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 1)))
          = (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 1)))
              * (∏ i ∈ Finset.range (m + 1), (1 - X ^ (3 * i + 2))) * E3 qfacInf from by ring,
      coeff_mul_congr_right hF3, ← qfac_split, ← coeff_qfacInf (show m + 1 ≤ 3 * (m + 1) by omega)]

/-- **Euler's pentagonal number theorem** `(q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}`. -/
theorem euler_pentagonal : qfacInf = pentSeries := by
  have key := congrArg (PowerSeries.map evm1) bilateral_pent_JTP
  rw [map_mul, map_mul, map_evm1_qfacInfL_q3, map_evm1_pentProdAInf, map_evm1_map_invert,
      map_evm1_pentProdBInf, map_evm1_pentTheta] at key
  rw [← reassembly]; exact key

end MockTheta5.JTP
