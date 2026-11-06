/-
# Region sums for the non-SCS pairs
-/
import RamanujanTau.GoodSecondTerm2.Sums

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

lemma ite_ll_le (c : Prop) [Decidable c] (m n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    (if c then ll m n * w else 0) ≤
      (if c then w / 2 * lam (m + 1) ^ 2 else 0) + (if c then w / 2 * lam (n + 1) ^ 2 else 0) := by
  split_ifs
  · have := two_abs_le (lam (m + 1)) (lam (n + 1)); unfold ll; nlinarith
  · simp

/-- Near pairs with `M ≤ M₀`. -/
theorem sum_nearM {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 ≤ A * N) (M₀ K : ℕ) :
    ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then ll m n * (4 / ((n : ℝ) - m) ^ 2) else 0) ≤
      12 * A * M₀ := by
  have hw : ∀ m n : ℕ, 0 ≤ 4 / ((n : ℝ) - m) ^ 2 := fun m n => by positivity
  have step := fun m n => ite_ll_le (m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀) m n (hw m n)
  have hsplit : ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then ll m n * (4 / ((n : ℝ) - m) ^ 2) else 0) ≤
      ∑ m ∈ range K, ∑ n ∈ range K,
        (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (m + 1) ^ 2 else 0) +
      ∑ m ∈ range K, ∑ n ∈ range K,
        (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (n + 1) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun n _ => step m n
  refine hsplit.trans ?_
  -- part a
  have ha : ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (m + 1) ^ 2 else 0) ≤
      4 * A * M₀ := by
    have h1 : ∀ m ∈ range K, ∑ n ∈ range K,
        (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (m + 1) ^ 2 else 0) ≤
        (if m + 1 ≤ M₀ then 4 * lam (m + 1) ^ 2 else 0) := by
      intro m _
      split_ifs with hm
      · calc _ ≤ ∑ n ∈ range K, 2 * lam (m + 1) ^ 2 *
              (if m < n ∧ 1 ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by
              refine Finset.sum_le_sum fun n _ => ?_
              by_cases hc : m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀
              · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]; field_simp; norm_num
              · rw [if_neg hc]; split_ifs <;> positivity
          _ = 2 * lam (m + 1) ^ 2 * ∑ n ∈ range K,
              (if m < n ∧ 1 ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by rw [Finset.mul_sum]
          _ ≤ 2 * lam (m + 1) ^ 2 * (2 / ((1 : ℕ) : ℝ)) := by
              gcongr; exact sum_inv_sq_shift le_rfl m K
          _ = _ := by norm_num; ring
      · refine le_of_eq (Finset.sum_eq_zero fun n _ => ?_)
        rw [if_neg (by omega)]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have := sum_lam_sq_le hA M₀ ((range K).filter (fun m => m + 1 ≤ M₀))
      (fun m hm => (Finset.mem_filter.mp hm).2)
    linarith
  -- part b
  have hb : ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (n + 1) ^ 2 else 0) ≤
      8 * A * M₀ := by
    rw [Finset.sum_comm]
    have h1 : ∀ n ∈ range K, ∑ m ∈ range K,
        (if m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀ then 4 / ((n : ℝ) - m) ^ 2 / 2 * lam (n + 1) ^ 2 else 0) ≤
        (if n + 1 ≤ 2 * M₀ then 4 * lam (n + 1) ^ 2 else 0) := by
      intro n _
      split_ifs with hn
      · calc _ ≤ ∑ m ∈ range K, 2 * lam (n + 1) ^ 2 *
              (if m < n ∧ 1 ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by
              refine Finset.sum_le_sum fun m _ => ?_
              by_cases hc : m < n ∧ n < 2 * m + 1 ∧ m + 1 ≤ M₀
              · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]; field_simp; norm_num
              · rw [if_neg hc]; split_ifs <;> positivity
          _ = 2 * lam (n + 1) ^ 2 * ∑ m ∈ range K,
              (if m < n ∧ 1 ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by rw [Finset.mul_sum]
          _ ≤ 2 * lam (n + 1) ^ 2 * (2 / ((1 : ℕ) : ℝ)) := by
              gcongr; exact sum_inv_sq_shift' le_rfl n K
          _ = _ := by norm_num; ring
      · refine le_of_eq (Finset.sum_eq_zero fun m _ => ?_)
        rw [if_neg (by omega)]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have := sum_lam_sq_le hA (2 * M₀) ((range K).filter (fun n => n + 1 ≤ 2 * M₀))
      (fun n hn => (Finset.mem_filter.mp hn).2)
    push_cast at this
    linarith
  linarith

lemma rpow_shift_le {m n : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 3) (hn : n < 2 * m + 1) :
    ((m : ℝ) + 1) ^ (-s) ≤ 8 * ((n : ℝ) + 1) ^ (-s) := by
  have h1 : (n : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1) := by
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 2 * m + 1)
    push_cast at this; linarith
  have h2 : (2 * ((m : ℝ) + 1)) ^ (-s) ≤ ((n : ℝ) + 1) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
  have h8 : (2 : ℝ) ^ s ≤ 8 := by
    calc (2 : ℝ) ^ s ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ = 8 := by norm_num
  have h3 : (2 : ℝ) ^ (-s) ≥ 1 / 8 := by
    rw [Real.rpow_neg (by norm_num), ge_iff_le, one_div]
    exact inv_anti₀ (by positivity) h8
  have h4 : 0 ≤ ((m : ℝ) + 1) ^ (-s) := by positivity
  nlinarith

/-- Near pairs with `h ≥ h₂`. -/
theorem sum_nearH {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 2) {h₂ : ℕ} (hh : 1 ≤ h₂) (K : ℕ) :
    ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε)) else 0) ≤
      36 / (h₂ : ℝ) * Su (1 + ε) := by
  have hs1 : (1 : ℝ) < 1 + ε := by linarith
  have hw : ∀ m n : ℕ, 0 ≤ 4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) := fun m n => by positivity
  have step := fun m n => ite_ll_le (m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m) m n (hw m n)
  have hsplit : ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε)) else 0) ≤
      ∑ m ∈ range K, ∑ n ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (m + 1) ^ 2 else 0) +
      ∑ m ∈ range K, ∑ n ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (n + 1) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := step m n
    rw [show ll m n * (4 / ((n : ℝ) - m) ^ 2) * ((m : ℝ) + 1) ^ (-(1 + ε)) =
      ll m n * (4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε))) by ring]
    exact this
  refine hsplit.trans ?_
  have hSu : 0 ≤ Su (1 + ε) := tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (by positivity)
  have hh0 : (0 : ℝ) < h₂ := by exact_mod_cast hh
  have ha : ∑ m ∈ range K, ∑ n ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (m + 1) ^ 2 else 0) ≤
      4 / (h₂ : ℝ) * Su (1 + ε) := by
    have h1 : ∀ m ∈ range K, ∑ n ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (m + 1) ^ 2 else 0) ≤
        4 / (h₂ : ℝ) * (lam (m + 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε))) := by
      intro m _
      have hx : 0 ≤ lam (m + 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) := mul_nonneg (sq_nonneg _) (by positivity)
      calc _ ≤ ∑ n ∈ range K, 2 * (lam (m + 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε))) *
            (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by
            refine Finset.sum_le_sum fun n _ => ?_
            by_cases hc : m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m
            · rw [if_pos hc, if_pos ⟨hc.1, hc.2.2⟩]; field_simp; norm_num
            · rw [if_neg hc]; split_ifs <;> positivity
        _ = 2 * (lam (m + 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε))) * ∑ n ∈ range K,
            (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by rw [Finset.mul_sum]
        _ ≤ 2 * (lam (m + 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε))) * (2 / (h₂ : ℝ)) := by
            gcongr; exact sum_inv_sq_shift hh m K
        _ = _ := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    exact sum_shift_le_Su hs1 _
  have hb : ∑ m ∈ range K, ∑ n ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (n + 1) ^ 2 else 0) ≤
      32 / (h₂ : ℝ) * Su (1 + ε) := by
    rw [Finset.sum_comm]
    have h1 : ∀ n ∈ range K, ∑ m ∈ range K, (if m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m then
        4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (n + 1) ^ 2 else 0) ≤
        32 / (h₂ : ℝ) * (lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + ε))) := by
      intro n _
      have hx : 0 ≤ lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + ε)) := mul_nonneg (sq_nonneg _) (by positivity)
      calc _ ≤ ∑ m ∈ range K, 16 * (lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + ε))) *
            (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by
            refine Finset.sum_le_sum fun m _ => ?_
            by_cases hc : m < n ∧ n < 2 * m + 1 ∧ h₂ ≤ n - m
            · rw [if_pos hc, if_pos ⟨hc.1, hc.2.2⟩]
              have hr := rpow_shift_le (m := m) (n := n) (s := 1 + ε) (by linarith) (by linarith) hc.2.1
              have hd : 0 < ((n : ℝ) - m) ^ 2 := by
                have : (m : ℝ) < n := by exact_mod_cast hc.1
                have : 0 < (n : ℝ) - m := by linarith
                positivity
              have hl := sq_nonneg (lam (n + 1))
              have hd' : 0 ≤ 1 / ((n : ℝ) - m) ^ 2 := by positivity
              calc 4 / ((n : ℝ) - m) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) / 2 * lam (n + 1) ^ 2
                  = 2 * ((m : ℝ) + 1) ^ (-(1 + ε)) * lam (n + 1) ^ 2 * (1 / ((n : ℝ) - m) ^ 2) := by ring
                _ ≤ 2 * (8 * ((n : ℝ) + 1) ^ (-(1 + ε))) * lam (n + 1) ^ 2 * (1 / ((n : ℝ) - m) ^ 2) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hr (by norm_num)) hl) hd'
                _ = _ := by ring
            · rw [if_neg hc]
              split_ifs
              · exact mul_nonneg (mul_nonneg (by norm_num) hx) (by positivity)
              · simp
        _ = 16 * (lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + ε))) * ∑ m ∈ range K,
            (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) := by rw [Finset.mul_sum]
        _ ≤ 16 * (lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + ε))) * (2 / (h₂ : ℝ)) := by
            gcongr; exact sum_inv_sq_shift' hh n K
        _ = _ := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    exact sum_shift_le_Su hs1 _
  have : 4 / (h₂ : ℝ) * Su (1 + ε) + 32 / (h₂ : ℝ) * Su (1 + ε) = 36 / (h₂ : ℝ) * Su (1 + ε) := by ring
  linarith

end RamanujanTau.GoodSecondTerm2
