/-
# `τ(n) = Ω(n^{11/2})`: Deligne's exponent cannot be lowered

From the two-sided Rankin–Selberg bound `c₁N ≤ ∑_{n≤N} τ(n)²/n¹¹ ≤ c₂N`
(`RankinSelberg.rankinSelberg_two_sided`, unconditional): if `τ(n)²/n¹¹ < c₁/2` for all large
`n`, the sum would be `≤ B + c₁N/2`, which is false for large `N`. Hence `|τ(n)| ≥ c·n^{11/2}` for
infinitely many `n`, and in particular `τ(n) ≠ O(n^{11/2−δ})` for every `δ > 0`.
-/
import RamanujanTau.RankinSelberg.Main

set_option autoImplicit false

namespace RamanujanTau.TauOmega

open Finset

/-- **`τ(n)² ≥ c n¹¹` infinitely often.** -/
theorem tau_sq_ge_infinitely_often : ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ n, M ≤ n ∧
    c * (n : ℝ) ^ 11 ≤ ((tau n : ℝ)) ^ 2 := by
  obtain ⟨c₁, c₂, hc₁, -, hRS⟩ := RankinSelberg.rankinSelberg_two_sided
  refine ⟨c₁ / 2, by positivity, fun M => ?_⟩
  by_contra hcon
  push Not at hcon
  set B : ℝ := ∑ n ∈ range M, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 with hB
  have hB0 : 0 ≤ B := sum_nonneg fun n _ => by positivity
  set N : ℕ := ⌈2 * B / c₁⌉₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNr : 2 * B / c₁ < N := by
    have := Nat.le_ceil (2 * B / c₁)
    rw [hN]; push_cast; linarith
  have hlow := (hRS N hN1).1
  -- termwise: n < M → term ≤ its range-M term;  n ≥ M → term ≤ c₁/2
  have hterm : ∀ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤
      (if n < M then ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 else 0) + c₁ / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < (n : ℝ) ^ 11 := by positivity
    split_ifs with h
    · linarith
    · have := hcon n (not_lt.1 h)
      rw [zero_add, div_le_iff₀ hnpos]; linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hif : ∑ n ∈ Icc 1 N, (if n < M then ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 else 0) ≤ B := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
    simp only [mem_filter] at hn; exact mem_range.2 hn.2
  have : c₁ * N ≤ B + N * (c₁ / 2) := by linarith
  have h2 : (N : ℝ) * c₁ ≤ 2 * B := by linarith
  rw [div_lt_iff₀ hc₁] at hNr
  linarith

/-- **`|τ(n)| ≥ c n^{11/2}` infinitely often** (`τ(n) = Ω(n^{11/2})`). -/
theorem tau_omega : ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ n, M ≤ n ∧
    c * (n : ℝ) ^ (11 / 2 : ℝ) ≤ |(tau n : ℝ)| := by
  obtain ⟨c, hc, h⟩ := tau_sq_ge_infinitely_often
  refine ⟨Real.sqrt c, Real.sqrt_pos.2 hc, fun M => ?_⟩
  obtain ⟨n, hMn, hn⟩ := h M
  refine ⟨n, hMn, ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ (11 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hlhs : (Real.sqrt c * (n : ℝ) ^ (11 / 2 : ℝ)) ^ 2 ≤ |(tau n : ℝ)| ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, hpow, sq_abs]; exact hn
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).1 hlhs

/-- **No power saving below Deligne**: `τ(n) ≠ O(n^{11/2−δ})` for any `δ > 0`. -/
theorem tau_not_isBigO {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(tau n : ℝ)| ≤ C * (n : ℝ) ^ (11 / 2 - δ) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, h⟩ := tau_omega
  -- choose n large with c n^{11/2} ≤ |τ n| ≤ C n^{11/2−δ}, i.e. c n^δ ≤ C
  have hev : ∀ᶠ x : ℝ in Filter.atTop, C < c * x ^ δ := by
    have := (tendsto_rpow_atTop hδ).const_mul_atTop hc
    exact this.eventually_gt_atTop C
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨n, hMn, hn⟩ := h (⌈max X 1⌉₊)
  have hnX : max X 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hMn)
  have hn1 : (1 : ℝ) ≤ n := (le_max_right _ _).trans hnX
  have hnpos : (0 : ℝ) < n := by linarith
  have hup := hC n (by exact_mod_cast hn1)
  have hsplit : (n : ℝ) ^ (11 / 2 : ℝ) = (n : ℝ) ^ (11 / 2 - δ) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hnpos]; ring_nf
  have hbig := hX n ((le_max_left _ _).trans hnX)
  have hp : 0 < (n : ℝ) ^ (11 / 2 - δ) := Real.rpow_pos_of_pos hnpos _
  have : c * (n : ℝ) ^ δ * (n : ℝ) ^ (11 / 2 - δ) ≤ C * (n : ℝ) ^ (11 / 2 - δ) := by
    calc c * (n : ℝ) ^ δ * (n : ℝ) ^ (11 / 2 - δ) = c * (n : ℝ) ^ (11 / 2 : ℝ) := by
          rw [hsplit]; ring
      _ ≤ _ := hn.trans hup
  have := le_of_mul_le_mul_right this hp
  linarith

end RamanujanTau.TauOmega

#print axioms RamanujanTau.TauOmega.tau_sq_ge_infinitely_often
#print axioms RamanujanTau.TauOmega.tau_omega
#print axioms RamanujanTau.TauOmega.tau_not_isBigO
