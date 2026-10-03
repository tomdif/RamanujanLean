/-
# The spt generating function

`Σ_{λ ⊢ n} (# smallest parts) = [qⁿ] Σ_{k≥1} q^k/((1−q^k)²(q^{k+1};q)_∞)`, via Mathlib's `Nat.Partition.genFun`:
for each `k`, the weights `f₂(i,c) = [i ≥ k]` and `f₁(i,c) = [i ≥ k]·(c+1 if i = k)` give
`Σ_λ [parts ≥ k]·count_k(λ) = [qⁿ](G_{f₁} − G_{f₂})`, and the product formula evaluates both.
-/
import RamanujanTau.MockTheta5PartitionCount

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey
open scoped PowerSeries.WithPiTopology

/-- `[parts ≥ k]`. -/
def wf2 (k : ℕ) : ℕ → ℕ → ℤ := fun i _ => if i < k then 0 else 1

/-- `[parts ≥ k]·(count_k + 1)`. -/
def wf1 (k : ℕ) : ℕ → ℕ → ℤ := fun i c => if i < k then 0 else if i = k then (c + 1 : ℤ) else 1

/-- the series `Σ_t (t+1) X^{kt} = 1/(1−X^k)²`. -/
noncomputable def W2 (k : ℕ) : PowerSeries ℤ := mk fun d => if k ∣ d then (((d / k : ℕ) : ℤ) + 1) else 0

lemma coeff_W2_mul {k : ℕ} (hk : 0 < k) (s : ℕ) : coeff (k * s) (W2 k) = (s : ℤ) + 1 := by
  rw [W2, coeff_mk, if_pos (dvd_mul_right k s), Nat.mul_div_cancel_left s hk]

lemma coeff_W2_not {k d : ℕ} (h : ¬ k ∣ d) : coeff d (W2 k) = 0 := by
  rw [W2, coeff_mk, if_neg h]

lemma W2_mul (k : ℕ) (hk : 1 ≤ k) : W2 k * (1 - X ^ k) ^ 2 = 1 := by
  ext d
  have e : W2 k * (1 - X ^ k : PowerSeries ℤ) ^ 2 = W2 k - C 2 * (X ^ k * W2 k) + W2 k * X ^ (2 * k) := by
    rw [show (C 2 : PowerSeries ℤ) = 2 by simp]; ring
  rw [e, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mul_X_pow', coeff_one]
  by_cases hd : k ∣ d
  · obtain ⟨t, rfl⟩ := hd
    rcases t with _ | _ | t
    · rw [coeff_W2_mul hk, if_neg (by omega), if_neg (by omega), if_pos (by simp)]; simp
    · rw [coeff_W2_mul hk, if_pos (by simp), if_neg (by omega), if_neg (by omega),
        show k * (0 + 1) - k = k * 0 by simp, coeff_W2_mul hk]
      norm_num
    · have e1 : k * (t + 1 + 1) - k = k * (t + 1) := by rw [Nat.mul_succ, Nat.add_sub_cancel]
      have e2 : k * (t + 1 + 1) - 2 * k = k * t := by rw [Nat.mul_succ, Nat.mul_succ]; omega
      rw [if_pos (by rw [Nat.mul_succ]; omega), if_pos (by rw [Nat.mul_succ, Nat.mul_succ]; omega),
        if_neg (by have := Nat.mul_pos hk (show 0 < t + 1 + 1 by omega); omega), e1, e2,
        coeff_W2_mul hk, coeff_W2_mul hk, coeff_W2_mul hk]
      push_cast; ring
  · rw [coeff_W2_not hd]
    have hd0 : d ≠ 0 := fun h0 => hd (by rw [h0]; exact dvd_zero k)
    have n1 : k ≤ d → ¬ k ∣ d - k := fun h1 h => hd (by rw [show d = d - k + k by omega]; exact dvd_add h (dvd_refl k))
    have n2 : 2 * k ≤ d → ¬ k ∣ d - 2 * k := fun h2 h => hd (by
      rw [show d = d - 2 * k + 2 * k by omega]; exact dvd_add h (dvd_mul_left k 2))
    by_cases h1 : k ≤ d <;> by_cases h2 : 2 * k ≤ d
    · rw [if_pos h1, if_pos h2, if_neg hd0, coeff_W2_not (n1 h1), coeff_W2_not (n2 h2)]; simp
    · rw [if_pos h1, if_neg h2, if_neg hd0, coeff_W2_not (n1 h1)]; simp
    · omega
    · rw [if_neg h1, if_neg h2, if_neg hd0]; simp

lemma hasSum_W2 {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun j : ℕ => ((j + 2 : ℕ) : ℤ) • (X : PowerSeries ℤ) ^ (k * (j + 1))) (W2 k - 1) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hc : ∀ n : ℤ, (n : PowerSeries ℤ) = C n := fun n => by simp
  simp only [zsmul_eq_mul, hc, coeff_C_mul, coeff_X_pow, map_sub, coeff_one, mul_ite, mul_one, mul_zero]
  by_cases hd : k ∣ d ∧ d ≠ 0
  · obtain ⟨⟨t, rfl⟩, hd0⟩ := hd
    rcases t with _ | t
    · simp at hd0
    rw [coeff_W2_mul (by omega), if_neg hd0]
    convert hasSum_single (f := fun j : ℕ => if k * (t + 1) = k * (j + 1) then ((j + 2 : ℕ) : ℤ) else 0) t
      (fun j hj => if_neg (fun h => hj (by have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) h; omega))) using 1
    simp; ring
  · have hz : ∀ j : ℕ, ¬ d = k * (j + 1) := fun j h => hd ⟨⟨j + 1, h⟩, by rw [h]; positivity⟩
    simp only [hz, if_false]
    by_cases h0 : d = 0
    · subst h0; rw [W2, coeff_mk, if_pos (dvd_zero k)]; simp
    · rw [if_neg h0, coeff_W2_not (fun h => hd ⟨h, h0⟩)]; simp

lemma factor_wf2 (k i : ℕ) :
    ((1 : PowerSeries ℤ) + ∑' j, wf2 k (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) * (1 - X ^ (i + 1))
      = if i + 1 < k then 1 - X ^ (i + 1) else 1 := by
  by_cases h : i + 1 < k
  · simp [wf2, h]
  · rw [if_neg h]
    simp only [wf2, if_neg h]
    exact genFun_factor_mul i

lemma factor_wf1 {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    ((1 : PowerSeries ℤ) + ∑' j, wf1 k (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) * (1 - X ^ (i + 1))
      * (if i = k - 1 then 1 - X ^ k else 1) = if i + 1 < k then 1 - X ^ (i + 1) else 1 := by
  by_cases h : i + 1 < k
  · rw [if_neg (by omega)]; simp [wf1, h]
  · rw [if_neg h]
    by_cases he : i = k - 1
    · subst he
      rw [if_pos rfl, show k - 1 + 1 = k by omega]
      simp only [wf1, show ¬ k < k from lt_irrefl k, if_false, if_true]
      have hs := (hasSum_W2 hk).tsum_eq
      have : (∑' j : ℕ, ((j + 1 : ℕ) + 1 : ℤ) • (X : PowerSeries ℤ) ^ (k * (j + 1)))
          = ∑' j : ℕ, ((j + 2 : ℕ) : ℤ) • (X : PowerSeries ℤ) ^ (k * (j + 1)) := by
        congr 1
      rw [this, hs, show (1 : PowerSeries ℤ) + (W2 k - 1) = W2 k by ring, mul_assoc, ← sq, W2_mul k hk]
    · rw [if_neg he, mul_one]
      simp only [wf1, show ¬ i + 1 < k from h, show i + 1 ≠ k by omega, if_false]
      exact genFun_factor_mul i

lemma qfac_tprod (k : ℕ) :
    ∏' i : ℕ, (if i + 1 < k then (1 : PowerSeries ℤ) - X ^ (i + 1) else 1) = qfac (k - 1) := by
  rw [tprod_eq_prod (s := range (k - 1)) (fun i hi => by rw [if_neg (by simp at hi; omega)]), qfac]
  exact prod_congr rfl fun i hi => by rw [if_pos (by simp at hi; omega)]

/-- `G_{f₂}·(q)_∞ = (q)_{k−1}`. -/
lemma genFun_wf2 (k : ℕ) : Nat.Partition.genFun (wf2 k) * qfacInf = qfac (k - 1) := by
  have hcomb := (Nat.Partition.hasProd_genFun (wf2 k)).mul hasProd_qfacInf
  rw [← hcomb.tprod_eq, ← qfac_tprod k]
  exact tprod_congr fun i => factor_wf2 k i

/-- `G_{f₁}·(q)_∞·(1−q^k) = (q)_{k−1}`. -/
lemma genFun_wf1 {k : ℕ} (hk : 1 ≤ k) :
    Nat.Partition.genFun (wf1 k) * qfacInf * (1 - X ^ k) = qfac (k - 1) := by
  have hcomb := ((Nat.Partition.hasProd_genFun (wf1 k)).mul hasProd_qfacInf).mul
    (hasProd_ite_eq (k - 1) ((1 : PowerSeries ℤ) - X ^ k))
  rw [← hcomb.tprod_eq, ← qfac_tprod k]
  exact tprod_congr fun i => factor_wf1 hk i

lemma prod_wf2 {n : ℕ} (k : ℕ) (l : n.Partition) :
    l.parts.toFinsupp.prod (wf2 k) = if ∀ j ∈ l.parts, k ≤ j then 1 else 0 := by
  rw [Finsupp.prod, Multiset.toFinsupp_support]
  split_ifs with h
  · exact prod_eq_one fun i hi => by rw [wf2, if_neg (not_lt.mpr (h i (Multiset.mem_toFinset.mp hi)))]
  · push Not at h
    obtain ⟨j, hj, hjk⟩ := h
    exact prod_eq_zero (Multiset.mem_toFinset.mpr hj) (by rw [wf2, if_pos hjk])

lemma prod_wf1 {n : ℕ} (k : ℕ) (l : n.Partition) :
    l.parts.toFinsupp.prod (wf1 k) = if ∀ j ∈ l.parts, k ≤ j then (l.parts.count k + 1 : ℤ) else 0 := by
  rw [Finsupp.prod, Multiset.toFinsupp_support]
  split_ifs with h
  · rw [prod_congr rfl (g := fun i => if i = k then ((l.parts.toFinsupp i : ℕ) + 1 : ℤ) else 1)
      (fun i hi => by rw [wf1, if_neg (not_lt.mpr (h i (Multiset.mem_toFinset.mp hi)))]),
      prod_ite_eq' (l.parts.toFinset) k]
    split_ifs with hk
    · rw [Multiset.toFinsupp_apply]
    · rw [Multiset.count_eq_zero.mpr (fun h' => hk (Multiset.mem_toFinset.mpr h'))]; simp
  · push Not at h
    obtain ⟨j, hj, hjk⟩ := h
    exact prod_eq_zero (Multiset.mem_toFinset.mpr hj) (by rw [wf1, if_pos hjk])

/-- **`Σ_λ [parts ≥ k]·count_k(λ) = [qⁿ](G_{f₁} − G_{f₂})`.** -/
lemma coeff_wf_diff (k n : ℕ) :
    coeff n (Nat.Partition.genFun (wf1 k)) - coeff n (Nat.Partition.genFun (wf2 k))
      = ∑ l : n.Partition, if ∀ j ∈ l.parts, k ≤ j then (l.parts.count k : ℤ) else 0 := by
  rw [Nat.Partition.coeff_genFun, Nat.Partition.coeff_genFun, ← sum_sub_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [prod_wf1, prod_wf2]
  split_ifs <;> ring

/-- **the spt generating function, term `k`**: `G_{f₁} − G_{f₂} = q^k (q)_{k−1}/((1−q^k)(q)_∞)`. -/
lemma genFun_wf_diff {k : ℕ} (hk : 1 ≤ k) :
    Nat.Partition.genFun (wf1 k) - Nat.Partition.genFun (wf2 k)
      = qfac (k - 1) * Ring.inverse qfacInf * X ^ k * Ring.inverse (1 - X ^ k) := by
  have hu1 : IsUnit (1 - X ^ k : PowerSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [zero_pow (by omega : k ≠ 0)]
  have h1 := genFun_wf1 hk
  have h2 := genFun_wf2 k
  have hq := Ring.mul_inverse_cancel _ isUnit_qfacInf
  have hx := Ring.mul_inverse_cancel _ hu1
  have e1 : Nat.Partition.genFun (wf1 k) = qfac (k - 1) * Ring.inverse qfacInf * Ring.inverse (1 - X ^ k) := by
    linear_combination (Ring.inverse qfacInf * Ring.inverse (1 - X ^ k)) * h1
      - Nat.Partition.genFun (wf1 k) * ((1 - X ^ k) * Ring.inverse (1 - X ^ k)) * hq
      - Nat.Partition.genFun (wf1 k) * hx
  have e2 : Nat.Partition.genFun (wf2 k) = qfac (k - 1) * Ring.inverse qfacInf := by
    linear_combination (Ring.inverse qfacInf) * h2 - Nat.Partition.genFun (wf2 k) * hq
  rw [e1, e2]
  linear_combination qfac (k - 1) * Ring.inverse qfacInf * hx

end MockTheta5.JTP
