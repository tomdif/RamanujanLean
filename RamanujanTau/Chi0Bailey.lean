/-
# The Bailey transform for `χ₀`: a Hecke-type double sum for `(q;q)_∞ χ₀`

`χ₀ = Σ_n qⁿ (q;q)_n/(q;q)_{2n}`, and by `pair_identity` the `n`-th term is `Σ_j c_j F(r(j), n)` with
`r(j) = 3j` (`j ≥ 0`), `−3j − 1` (`j < 0`). Exchanging the sums and multiplying by `(q;q)_∞` (`γc_eq`):

  `(q;q)_∞ χ₀ = Σ_{j∈ℤ} (q^{j(6j−1)} − q^{(2j+1)(3j+1)}) · Σ_{u≥0} (−1)^u q^{r+3ru+u(3u+5)/2}(1 + q^{r+1+u})`, `r = r(j)`.
-/
import RamanujanTau.Chi0Conj
import RamanujanTau.MockTheta5Defs
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace Chi0
open PowerSeries Finset MockTheta5.Bailey FourSquares MockTheta5.JTP MockTheta5.Formal

/-- `r(j)`. -/
def rj (j : ℤ) : ℕ := if 0 ≤ j then (3 * j).toNat else (-3 * j - 1).toNat

lemma qfac_add (a b : ℕ) : qfac (a + b) = qfac a * ∏ k ∈ range b, (1 - X ^ (a + 1 + k)) := by
  induction b with
  | zero => simp
  | succ b ih => rw [← add_assoc, qfac_succ', ih, prod_range_succ]; ring_nf

lemma chi0term_eq (n : ℕ) : chi0term n = X ^ n * qfac n * Ring.inverse (qfac (2 * n)) := by
  have h : qfac (2 * n) = qfac n * qpochG (X ^ (n + 1)) X n := by
    rw [two_mul, qfac_add, qpochG]
    congr 1
    refine prod_congr rfl fun k _ => ?_
    rw [← pow_add]
  have hu : IsUnit (qpochG (X ^ (n + 1)) X n) := isUnit_qpochG _ _ (by simp) n
  rw [chi0term, h, Ring.mul_inverse_rev' (Commute.all _ _)]
  have hq := Ring.mul_inverse_cancel _ (isUnit_qfac n)
  linear_combination (-(X ^ n * Ring.inverse (qpochG (X ^ (n + 1)) X n))) * hq

lemma inv_qfac_two_mul (n : ℕ) : Ring.inverse (qfac (2 * n)) = (1 - X ^ (2 * n + 1)) * Ring.inverse (qfac (2 * n + 1)) := by
  rw [qfac_succ', Ring.mul_inverse_rev' (Commute.all _ _)]
  have hu := isUnit_one_sub (m := 2 * n + 1) (by omega)
  have h := Ring.inverse_mul_cancel _ hu
  linear_combination (-(Ring.inverse (qfac (2 * n)))) * h

lemma Fc_rj (j : ℤ) (n : ℕ) :
    Fc (rj j) n = X ^ n * qfac n * invf ((n : ℤ) - 3 * j) * invf ((n : ℤ) + 3 * j + 1) := by
  unfold Fc rj
  split_ifs with h
  · rw [Int.toNat_of_nonneg (by omega)]
  · rw [Int.toNat_of_nonneg (by omega), show (n : ℤ) - (-3 * j - 1) = (n : ℤ) + 3 * j + 1 by ring,
      show (n : ℤ) + (-3 * j - 1) + 1 = (n : ℤ) - 3 * j by ring]
    ring

/-- the `n`-th term of `χ₀` through the Bailey pair. -/
lemma chi0term_pair (n : ℕ) : chi0term n =
    ∑ i ∈ range (2 * (n + 3) + 1), cj ((i : ℤ) - (n + 3 : ℕ)) * Fc (rj ((i : ℤ) - (n + 3 : ℕ))) n := by
  rw [chi0term_eq, inv_qfac_two_mul, pair_identity, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Fc_rj]; ring

/-! ## `ℤ`-indexed sums with terms of order `≥ |j|` -/

/-- `Σ_{j∈ℤ} T j`, stabilized coefficientwise. -/
noncomputable def zsum (T : ℤ → PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun k => coeff k (∑ j ∈ Icc (-(k : ℤ)) k, T j)

lemma coeff_zsum {T : ℤ → PowerSeries ℤ} (hT : ∀ j, (X : PowerSeries ℤ) ^ j.natAbs ∣ T j) {k M : ℕ} (hM : k ≤ M) :
    coeff k (zsum T) = coeff k (∑ j ∈ Icc (-(M : ℤ)) M, T j) := by
  rw [zsum, coeff_mk, map_sum, map_sum]
  refine sum_subset (Icc_subset_Icc (by omega) (by omega)) fun j hj hj' => ?_
  simp only [mem_Icc, not_and_or, not_le] at hj hj'
  obtain ⟨c, hc⟩ := hT j
  rw [hc, coeff_X_pow_mul', if_neg (by omega)]

lemma X_pow_dvd_sub_of_coeff {f g : PowerSeries ℤ} {k : ℕ} (h : ∀ m ≤ k, coeff m f = coeff m g) :
    (X : PowerSeries ℤ) ^ (k + 1) ∣ f - g := by
  rw [PowerSeries.X_pow_dvd_iff]; intro m hm; rw [map_sub, h m (by omega), sub_self]

lemma coeff_mul_of_dvd {f g P : PowerSeries ℤ} {k : ℕ} (h : (X : PowerSeries ℤ) ^ (k + 1) ∣ f - g) :
    coeff k (P * f) = coeff k (P * g) := by
  obtain ⟨c, hc⟩ := h
  rw [show P * f = P * g + X ^ (k + 1) * (P * c) by rw [← mul_assoc, mul_comm _ P, mul_assoc, ← hc]; ring,
    map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

lemma zsum_mul {T : ℤ → PowerSeries ℤ} (hT : ∀ j, (X : PowerSeries ℤ) ^ j.natAbs ∣ T j) (P : PowerSeries ℤ) :
    zsum (fun j => P * T j) = P * zsum T := by
  have hT' : ∀ j, (X : PowerSeries ℤ) ^ j.natAbs ∣ P * T j := fun j => dvd_mul_of_dvd_right (hT j) _
  ext k
  rw [coeff_zsum hT' le_rfl, ← mul_sum]
  refine (coeff_mul_of_dvd (X_pow_dvd_sub_of_coeff fun m hm => ?_)).symm
  rw [coeff_zsum hT hm]

lemma zsum_congr {T T' : ℤ → PowerSeries ℤ} (h : ∀ j, T j = T' j) : zsum T = zsum T' := by
  unfold zsum; simp only [h]

lemma cj_dvd (j : ℤ) : (X : PowerSeries ℤ) ^ j.natAbs ∣ cj j := by
  unfold cj
  have h1 : j.natAbs ≤ (j * (6 * j - 1)).toNat := by
    rcases (by omega : j ≤ -1 ∨ j = 0 ∨ 1 ≤ j) with h | h | h
    · have : (j.natAbs : ℤ) ≤ j * (6 * j - 1) := by rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]; nlinarith
      omega
    · subst h; simp
    · have : (j.natAbs : ℤ) ≤ j * (6 * j - 1) := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]; nlinarith
      omega
  have h2 : j.natAbs ≤ ((2 * j + 1) * (3 * j + 1)).toNat := by
    rcases (by omega : j ≤ -1 ∨ 0 ≤ j) with h | h
    · have : (j.natAbs : ℤ) ≤ (2 * j + 1) * (3 * j + 1) := by rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]; nlinarith
      omega
    · have : (j.natAbs : ℤ) ≤ (2 * j + 1) * (3 * j + 1) := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]; nlinarith
      omega
  exact dvd_sub (pow_dvd_pow X h1) (pow_dvd_pow X h2)

/-! ## Exchanging the sums -/

lemma Fc_rj_zero {j : ℤ} {n : ℕ} (h : (n : ℤ) < j.natAbs) : cj j * Fc (rj j) n = 0 := by
  rw [Fc_rj]
  unfold invf
  rcases le_or_gt 0 j with hj | hj
  · rw [if_neg (by omega)]; ring
  · rw [if_neg (show ¬ (0 : ℤ) ≤ (n : ℤ) + 3 * j + 1 by omega)]; ring

lemma sum_range_eq_Icc (M : ℕ) (f : ℤ → PowerSeries ℤ) :
    ∑ i ∈ range (2 * M + 1), f ((i : ℤ) - M) = ∑ j ∈ Icc (-(M : ℤ)) M, f j := by
  refine sum_nbij' (fun i => (i : ℤ) - M) (fun j => (j + M).toNat) (fun i hi => ?_) (fun j hj => ?_)
    (fun i _ => ?_) (fun j hj => ?_) (fun i _ => rfl)
  · simp only [mem_range] at hi; simp only [mem_Icc]; omega
  · simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · simp
  · simp only [mem_Icc] at hj; simp only; omega

lemma chi0term_zsum (n : ℕ) {M : ℕ} (hM : n ≤ M) :
    chi0term n = ∑ j ∈ Icc (-(M : ℤ)) M, cj j * Fc (rj j) n := by
  rw [chi0term_pair, sum_range_eq_Icc (n + 3) (fun j => cj j * Fc (rj j) n)]
  rcases le_or_gt (n + 3) M with h | h
  · refine sum_subset (Icc_subset_Icc (by omega) (by omega)) fun j _ hj => ?_
    simp only [mem_Icc, not_and_or, not_le] at hj
    exact Fc_rj_zero (by omega)
  · symm
    refine sum_subset (Icc_subset_Icc (by omega) (by omega)) fun j _ hj => ?_
    simp only [mem_Icc, not_and_or, not_le] at hj
    exact Fc_rj_zero (by omega)

lemma Sr_dvd_trunc (r k N : ℕ) (hN : k + 1 ≤ N) : (X : PowerSeries ℤ) ^ (k + 1) ∣ Sr r - ∑ n ∈ range N, Fc r n :=
  X_pow_dvd_sub_of_coeff fun m hm => coeff_Sr (by omega)

/-- **`χ₀ = Σ_j c_j S_{r(j)}`**. -/
theorem chi0_eq_zsum : chi0 = zsum (fun j => cj j * Sr (rj j)) := by
  ext k
  have hT : ∀ j, (X : PowerSeries ℤ) ^ j.natAbs ∣ cj j * Sr (rj j) := fun j => dvd_mul_of_dvd_left (cj_dvd j) _
  rw [coeff_chi0 (M := k + 1) le_rfl, coeff_zsum hT (M := k + 1) (by omega)]
  rw [sum_congr rfl fun n hn => chi0term_zsum n (M := k + 1) (by simp only [mem_range] at hn; omega), sum_comm,
    map_sum, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, coeff_mul_of_dvd (Sr_dvd_trunc (rj j) k (k + 1) le_rfl)]

/-- **the Hecke-type double sum**: `(q;q)_∞ χ₀ = Σ_j c_j γ_{r(j)}`, `γ_r` in Garvan's closed form. -/
theorem qfacInf_mul_chi0 : qfacInf * chi0 = zsum (fun j => cj j * Cc (rj j)) := by
  have hT : ∀ j, (X : PowerSeries ℤ) ^ j.natAbs ∣ cj j * Sr (rj j) := fun j => dvd_mul_of_dvd_left (cj_dvd j) _
  rw [chi0_eq_zsum, ← zsum_mul hT]
  refine zsum_congr fun j => ?_
  rw [← γc_eq, γc]; ring

end Chi0
