/-
# `a_f(n) = Ω(n^{(k−1)/2})` for every nonzero level-one cusp form

Same argument as `TauOmega.Main`, from `RankinSelbergGeneral.rankinSelberg_two_sided`.
-/
import RamanujanTau.RankinSelbergGeneral.Positive

set_option autoImplicit false

namespace RamanujanTau.TauOmega

open Finset RamanujanTau.RankinSelbergGeneral ModularForm
open scoped MatrixGroups
open UpperHalfPlane hiding I

variable {k : ℕ}

/-- `|a_f(n)|² ≥ c n^{k−1}` for infinitely many `n`. -/
theorem coeffSq_ge_infinitely_often (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ n, M ≤ n ∧ c * (n : ℝ) ^ (k - 1) ≤ coeffSq f n := by
  obtain ⟨n₀, -, -, -, c₁, c₂, hc₁, -, hRS⟩ := rankinSelberg_two_sided f hf hk
  refine ⟨c₁ / 2, by positivity, fun M => ?_⟩
  by_contra hcon
  push Not at hcon
  set B : ℝ := ∑ n ∈ range M, coeffSq f n / (n : ℝ) ^ (k - 1) with hB
  have hB0 : 0 ≤ B := sum_nonneg fun n _ => by unfold coeffSq; positivity
  set N : ℕ := ⌈2 * B / c₁⌉₊ + 1 + n₀ with hN
  have hNn : n₀ ≤ N := by omega
  have hNr : 2 * B / c₁ < N := by
    have := Nat.le_ceil (2 * B / c₁)
    rw [hN]; push_cast; linarith [(Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)]
  have hlow := (hRS N hNn).1
  unfold S at hlow
  have hterm : ∀ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) ≤
      (if n < M then coeffSq f n / (n : ℝ) ^ (k - 1) else 0) + c₁ / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < (n : ℝ) ^ (k - 1) := by positivity
    split_ifs with h
    · linarith
    · have := hcon n (not_lt.1 h)
      rw [zero_add, div_le_iff₀ hnpos]; linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hif : ∑ n ∈ Icc 1 N, (if n < M then coeffSq f n / (n : ℝ) ^ (k - 1) else 0) ≤ B := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      (fun n _ _ => by unfold coeffSq; positivity)
    simp only [mem_filter] at hn; exact mem_range.2 hn.2
  have h2 : (N : ℝ) * c₁ ≤ 2 * B := by linarith
  rw [div_lt_iff₀ hc₁] at hNr
  linarith

/-- **`|a_f(n)| ≥ c n^{(k−1)/2}` infinitely often.** -/
theorem coeff_omega (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ n, M ≤ n ∧
      c * (n : ℝ) ^ (((k : ℝ) - 1) / 2) ≤ ‖(qExpansion 1 f).coeff n‖ := by
  obtain ⟨c, hc, h⟩ := coeffSq_ge_infinitely_often f hf hk
  refine ⟨Real.sqrt c, Real.sqrt_pos.2 hc, fun M => ?_⟩
  obtain ⟨n, hMn, hn⟩ := h M
  refine ⟨n, hMn, ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2 = (n : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, ← Real.rpow_natCast]
    congr 1; push_cast [Nat.cast_sub hk]; ring
  have hlhs : (Real.sqrt c * (n : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2 ≤
      ‖(qExpansion 1 f).coeff n‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, hpow]; exact hn
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hlhs

/-- **No power saving below Deligne for any nonzero cusp form**. -/
theorem coeff_not_isBigO (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) : ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(qExpansion 1 f).coeff n‖ ≤ C * (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, h⟩ := coeff_omega f hf hk
  have hev : ∀ᶠ x : ℝ in Filter.atTop, C < c * x ^ δ :=
    ((tendsto_rpow_atTop hδ).const_mul_atTop hc).eventually_gt_atTop C
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨n, hMn, hn⟩ := h (⌈max X 1⌉₊)
  have hnX : max X 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hMn)
  have hn1 : (1 : ℝ) ≤ n := (le_max_right _ _).trans hnX
  have hnpos : (0 : ℝ) < n := by linarith
  have hup := hC n (by exact_mod_cast hn1)
  have hsplit : (n : ℝ) ^ (((k : ℝ) - 1) / 2) =
      (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hnpos]; ring_nf
  have hbig := hX n ((le_max_left _ _).trans hnX)
  have hp : 0 < (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ) := Real.rpow_pos_of_pos hnpos _
  have : c * (n : ℝ) ^ δ * (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ) ≤
      C * (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ) := by
    calc c * (n : ℝ) ^ δ * (n : ℝ) ^ (((k : ℝ) - 1) / 2 - δ)
        = c * (n : ℝ) ^ (((k : ℝ) - 1) / 2) := by rw [hsplit]; ring
      _ ≤ _ := hn.trans hup
  have := le_of_mul_le_mul_right this hp
  linarith

end RamanujanTau.TauOmega

#print axioms RamanujanTau.TauOmega.coeffSq_ge_infinitely_often
#print axioms RamanujanTau.TauOmega.coeff_omega
#print axioms RamanujanTau.TauOmega.coeff_not_isBigO
