/-
# Rankin-weighted sums

`u(n) = λ(n)²`, `Σ_{n≤N} u(n) ≤ A N` (Rankin). For antitone `w ≥ 0`: `Σ_{n≤N} u(n)w(n) ≤ A Σ_{n≤N} w(n)`
(`sum_u_mul_le`), hence `Σ λ(n)² n^{−s} ≤ A ζ(s)` for `s > 1`.
-/
import RamanujanTau.GoodSecondTerm2.IBP
import RamanujanTau.SubconvexityCond.Defs

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.ZetaAFE

lemma lam_zero : lam 0 = 0 := by simp [lam, tau_zero]

lemma sum_Icc_succ (f : ℕ → ℝ) (N : ℕ) : ∑ n ∈ Icc 1 (N + 1), f n = ∑ n ∈ Icc 1 N, f n + f (N + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- **Master Rankin lemma**: `Σ_{n≤N} λ(n)² w(n) ≤ A Σ_{n≤N} w(n)` for antitone `w ≥ 0`. -/
theorem sum_u_mul_le {A : ℝ} (hA : ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 ≤ A * N) {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw : ∀ n, 1 ≤ n → w (n + 1) ≤ w n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, lam n ^ 2 * w n ≤ A * ∑ n ∈ Icc 1 N, w n := by
  -- F(N) = A Σ w − Σ u w − (A N − S N) w N ≥ 0
  have key : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, lam n ^ 2 * w n + (A * N - ∑ n ∈ Icc 1 N, lam n ^ 2) * w N ≤
      A * ∑ n ∈ Icc 1 N, w n := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp; linarith
      · have ih' := ih h0
        rw [sum_Icc_succ, sum_Icc_succ, sum_Icc_succ]
        have hS := hA N
        have hwN := hw N h0
        have h1 : 0 ≤ (A * N - ∑ n ∈ Icc 1 N, lam n ^ 2) * (w N - w (N + 1)) :=
          mul_nonneg (by linarith) (by linarith)
        push_cast
        nlinarith
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · have := key N h0
    have hS := hA N
    have : 0 ≤ (A * N - ∑ n ∈ Icc 1 N, lam n ^ 2) * w N := mul_nonneg (by linarith) (hw0 N)
    linarith

lemma exists_rankin : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 ≤ A * N :=
  exists_sum_lam_sq_le

/-- `Σ_{n≥1} λ(n)² n^{−s}` converges for `s > 1`, with sum `≤ A ζ(s)`. -/
theorem summable_u_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => lam n ^ 2 * (n : ℝ) ^ (-s)) ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∑' n : ℕ, lam n ^ 2 * (n : ℝ) ^ (-s) ≤ A * ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  obtain ⟨A, hA0, hA⟩ := exists_rankin
  have hz := GoodSecondTerm.summable_rpow_nat (p := s) hs
  have hw0 : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-s) := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-s) := by
    intro n hn
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith) (by linarith)
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, lam n ^ 2 * (n : ℝ) ^ (-s) ≤ A * ∑' n : ℕ, (n : ℝ) ^ (-s) := by
    intro N
    have h1 : ∑ n ∈ Finset.range N, lam n ^ 2 * (n : ℝ) ^ (-s) ≤ ∑ n ∈ Icc 1 N, lam n ^ 2 * (n : ℝ) ^ (-s) := by
      rw [Finset.range_eq_Ico]
      calc ∑ n ∈ Ico 0 N, lam n ^ 2 * (n : ℝ) ^ (-s) = ∑ n ∈ Ico 1 N, lam n ^ 2 * (n : ℝ) ^ (-s) := by
            rcases Nat.eq_zero_or_pos N with h | h
            · subst h; simp
            · rw [Finset.sum_eq_sum_diff_singleton_add (i := 0) (by simp; omega)]
              rw [show Ico 0 N \ {0} = Ico 1 N by ext x; simp; omega]
              simp [lam_zero]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp at hx ⊢; omega)
            (fun i _ _ => mul_nonneg (sq_nonneg _) (hw0 i))
    refine h1.trans ((sum_u_mul_le hA hw0 hw N).trans ?_)
    gcongr
    calc ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s) ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-s) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp at hx ⊢; omega)
            (fun i _ _ => hw0 i)
      _ ≤ _ := hz.sum_le_tsum _ (fun i _ => hw0 i)
  have hsum : Summable (fun n : ℕ => lam n ^ 2 * (n : ℝ) ^ (-s)) :=
    summable_of_sum_range_le (fun n => mul_nonneg (sq_nonneg _) (hw0 n)) hpart
  exact ⟨hsum, A, hA0, Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (sq_nonneg _) (hw0 n)) hpart⟩

end RamanujanTau.GoodSecondTerm2
