/-
# R2 building block: Rankin–Selberg against a decreasing weight

From `Σ_{n≤N} λ(n)² ≤ A N` (`SubconvexityCond.exists_sum_lam_sq_le`) and Abel summation:
for `G ≥ 0` non-increasing, `Σ_{m≤N} λ(m)² G(m) ≤ A Σ_{m≤N} G(m)` (`sum_lam_sq_mul_le`).
This is the device for the far part (R2): split `|λ(m)λ(n)| ≤ (λ(m)² + λ(n)²)/2`, sum the
majorant over the partner variable (injective along each line), and apply this lemma.
Level 1.
-/
import RamanujanTau.SelbergKey5.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey6

open Finset RamanujanTau.SubconvexityCond

/-- **Rankin–Selberg against a non-increasing weight.** -/
theorem sum_lam_sq_mul_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ (G : ℕ → ℝ) (N : ℕ), (∀ m, 0 ≤ G m) →
    (∀ m, G (m + 1) ≤ G m) →
    ∑ i ∈ range N, lam (i + 1) ^ 2 * G (i + 1) ≤ A * ∑ i ∈ range N, G (i + 1) := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_lam_sq_le
  refine ⟨A, hA0, fun G N hG0 hG => ?_⟩
  -- partial sums in `range` form
  have hS : ∀ n : ℕ, ∑ i ∈ range n, lam (i + 1) ^ 2 ≤ A * n := by
    intro n
    have e : ∑ i ∈ range n, lam (i + 1) ^ 2 = ∑ k ∈ Icc 1 n, lam k ^ 2 := by
      induction n with
      | zero => simp
      | succ k ih => rw [sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    rw [e]; exact hA n
  have h1 := sum_range_by_parts (fun i => G (i + 1)) (fun i => lam (i + 1) ^ 2) N
  have h2 := sum_range_by_parts (fun i => G (i + 1)) (fun _ => (1 : ℝ)) N
  simp only [smul_eq_mul, mul_one, sum_const, card_range, nsmul_eq_mul] at h1 h2
  rw [show (∑ i ∈ range N, lam (i + 1) ^ 2 * G (i + 1)) =
      ∑ i ∈ range N, G (i + 1) * lam (i + 1) ^ 2 from sum_congr rfl fun i _ => mul_comm _ _, h1, h2]
  have hlast : G (N - 1 + 1) * ∑ i ∈ range N, lam (i + 1) ^ 2 ≤ G (N - 1 + 1) * (A * N) :=
    mul_le_mul_of_nonneg_left (hS N) (hG0 _)
  have hmid : ∀ i ∈ range (N - 1), -((G (i + 1 + 1) - G (i + 1)) * ∑ j ∈ range (i + 1), lam (j + 1) ^ 2) ≤
      -((G (i + 1 + 1) - G (i + 1)) * (A * ((i + 1 : ℕ) : ℝ))) := by
    intro i _
    have hd : 0 ≤ G (i + 1) - G (i + 1 + 1) := by linarith [hG (i + 1)]
    have := mul_le_mul_of_nonneg_left (hS (i + 1)) hd
    nlinarith
  have hm := sum_le_sum hmid
  simp only [sum_neg_distrib] at hm
  have e2 : ∑ i ∈ range (N - 1), (G (i + 1 + 1) - G (i + 1)) * (A * ((i + 1 : ℕ) : ℝ)) =
      A * ∑ i ∈ range (N - 1), (G (i + 1 + 1) - G (i + 1)) * ((i + 1 : ℕ) : ℝ) := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => by ring
  rw [e2] at hm
  push_cast at hm ⊢
  nlinarith [hlast, hm]

/-- **Frequency lower bound**: `|log X − log Y| ≥ |X − Y| / max X Y` for `X, Y > 0`. Applied with
`X = bdn`, `Y = acm`, it gives `|ω| ≥ |ℓ|/max(bdn, acm)` for the off-diagonal frequencies. -/
theorem abs_log_sub_ge {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    |X - Y| / max X Y ≤ |Real.log X - Real.log Y| := by
  rcases le_total Y X with h | h
  · rw [max_eq_left h, abs_of_nonneg (by linarith), abs_of_nonneg (by
      linarith [Real.log_le_log hY h])]
    have := Real.log_le_sub_one_of_pos (div_pos hY hX)
    rw [Real.log_div hY.ne' hX.ne'] at this
    rw [div_le_iff₀ hX]
    have e : (Y / X - 1) * X = Y - X := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right this hX.le]
  · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by
      linarith [Real.log_le_log hX h])]
    have := Real.log_le_sub_one_of_pos (div_pos hX hY)
    rw [Real.log_div hX.ne' hY.ne'] at this
    rw [div_le_iff₀ hY]
    have e : (X / Y - 1) * Y = X - Y := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right this hY.le]

end RamanujanTau.SelbergKey6
