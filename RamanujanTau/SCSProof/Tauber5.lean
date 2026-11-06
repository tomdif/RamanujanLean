/-
# Tauberian step 5: `|Σ_{n≤N} τ(n)τ(n+h)| ≤ C h (N+h)^{12−ρ}`
-/
import RamanujanTau.SCSProof.Tauber4

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.RankinError
open scoped Real

/-- `A(N) = Σ_{n ≤ N} τ(n)τ(n+h)`. -/
noncomputable def Asum (h N : ℕ) : ℝ := ∑ n ∈ range (N + 1), aR h n

lemma lam_zero' : lam 0 = 0 := by simp [lam, RamanujanTau.tau_zero]

lemma Icc_one_eq_map (M : ℕ) : Icc 1 M = (range M).map (addRightEmbedding 1) := by
  ext n; simp only [mem_Icc, mem_map, mem_range, addRightEmbedding_apply]
  constructor
  · intro h; exact ⟨n - 1, by omega, by omega⟩
  · rintro ⟨m, hm, rfl⟩; omega

lemma sum_range_eq_Slam (M : ℕ) : ∑ n ∈ range (M + 1), lam n ^ 2 = Slam M := by
  rw [sum_range_succ', lam_zero', Slam, Icc_one_eq_map, sum_map]
  simp

lemma sum_lam_shift (h N : ℕ) :
    ∑ n ∈ range (N + 1), lam (n + h) ^ 2 ≤ Slam (N + h) := by
  rw [← sum_range_eq_Slam]
  calc ∑ n ∈ range (N + 1), lam (n + h) ^ 2 = ∑ m ∈ (range (N + 1)).map (addRightEmbedding h),
        lam m ^ 2 := by rw [sum_map]; rfl
    _ ≤ ∑ m ∈ range (N + h + 1), lam m ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun _ _ _ => sq_nonneg _)
        simp only [mem_map, mem_range, addRightEmbedding_apply] at hm ⊢
        obtain ⟨n, hn, rfl⟩ := hm; omega

/-- Trivial bound `Σ_{n≤N} |a_n| ≤ A (N+h)^{12}`. -/
theorem sum_aabs_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ h N : ℕ,
    ∑ n ∈ range (N + 1), aabs h n ≤ A * ((N : ℝ) + h) ^ 12 := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_lam_sq_le
  refine ⟨A, hA0, fun h N => ?_⟩
  have hNh : (0 : ℝ) ≤ (N : ℝ) + h := by positivity
  calc ∑ n ∈ range (N + 1), aabs h n
      ≤ ∑ n ∈ range (N + 1), (lam n ^ 2 + lam (n + h) ^ 2) / 2 * ((N : ℝ) + h) ^ 11 := by
        refine sum_le_sum fun n hn => (aabs_le_lam h n).trans ?_
        have : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
        gcongr
    _ = (∑ n ∈ range (N + 1), lam n ^ 2 + ∑ n ∈ range (N + 1), lam (n + h) ^ 2) / 2 *
          ((N : ℝ) + h) ^ 11 := by rw [← sum_mul, ← sum_div, sum_add_distrib]
    _ ≤ (Slam N + Slam (N + h)) / 2 * ((N : ℝ) + h) ^ 11 := by
        rw [sum_range_eq_Slam]; gcongr; exact sum_lam_shift h N
    _ ≤ (A * N + A * ((N : ℝ) + h)) / 2 * ((N : ℝ) + h) ^ 11 := by
        gcongr
        · exact hA N
        · have := hA (N + h); push_cast at this; exact this
    _ ≤ A * ((N : ℝ) + h) * ((N : ℝ) + h) ^ 11 := by
        have : (N : ℝ) ≤ N + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
        gcongr; nlinarith
    _ = A * ((N : ℝ) + h) ^ 12 := by ring

end RamanujanTau.SCSProof
