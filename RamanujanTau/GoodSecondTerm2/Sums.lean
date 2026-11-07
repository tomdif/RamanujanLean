/-
# Finite double-sum estimates for the non-SCS pairs
-/
import RamanujanTau.GoodSecondTerm2.NonS

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

/-- `Zl s = Σ_{n≥1} |λ(n)| n^{−s}`. -/
noncomputable def Zl (s : ℝ) : ℝ := ∑' n : ℕ, |lam (n + 1)| * ((n : ℝ) + 1) ^ (-s)

lemma abs_lam_succ (n : ℕ) (s : ℝ) :
    |lam (n + 1)| * ((n : ℝ) + 1) ^ (-s) = |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(11 / 2 + s)) := by
  unfold lam
  push_cast
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_assoc, ← Real.rpow_add (by positivity)]
  ring_nf

lemma summable_Zl {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => |lam (n + 1)| * ((n : ℝ) + 1) ^ (-s) := by
  have h := summable_abs_tau_shift (σ := 11 / 2 + s) (by linarith)
  exact h.congr fun n => (abs_lam_succ n s).symm

lemma Zl_nonneg (s : ℝ) : 0 ≤ Zl s := tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (by positivity)

lemma sum_le_Zl {s : ℝ} (hs : 1 < s) (t : Finset ℕ) :
    ∑ n ∈ t, |lam (n + 1)| * ((n : ℝ) + 1) ^ (-s) ≤ Zl s :=
  (summable_Zl hs).sum_le_tsum t (fun n _ => mul_nonneg (abs_nonneg _) (by positivity))

/-- Product sums: `Σ_{m,n<K} a_m b_n ≤ Zl(s) Zl(s')`. -/
lemma sum_prod_le {s s' : ℝ} (hs : 1 < s) (hs' : 1 < s') (K : ℕ) (P : ℕ → ℕ → Prop) [∀ m n, Decidable (P m n)] :
    ∑ m ∈ range K, ∑ n ∈ range K, (if P m n then (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-s)) *
      (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-s')) else 0) ≤ Zl s * Zl s' := by
  have h1 : ∀ m ∈ range K, ∑ n ∈ range K, (if P m n then (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-s)) *
      (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-s')) else 0) ≤ (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-s)) * Zl s' := by
    intro m _
    have ha : 0 ≤ |lam (m + 1)| * ((m : ℝ) + 1) ^ (-s) := mul_nonneg (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ n ∈ range K, (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-s)) * (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-s')) := by
          refine Finset.sum_le_sum fun n _ => ?_
          split_ifs
          · exact le_rfl
          · exact mul_nonneg ha (mul_nonneg (abs_nonneg _) (by positivity))
      _ = (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-s)) * ∑ n ∈ range K, |lam (n + 1)| * ((n : ℝ) + 1) ^ (-s') := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact sum_le_Zl hs' _
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  · exact Zl_nonneg s'
  · exact sum_le_Zl hs _

/-- `Σ_{d ∈ [h₂, D)} 1/d² ≤ 2/h₂`. -/
lemma sum_inv_sq_tail {h₂ : ℕ} (hh : 1 ≤ h₂) (D : ℕ) :
    ∑ d ∈ Ico h₂ D, 1 / ((d : ℝ) ^ 2) ≤ 2 / (h₂ : ℝ) := by
  have key : ∀ k : ℕ, ∑ d ∈ Ico h₂ (h₂ + k), 1 / ((d : ℝ) ^ 2) ≤ 2 / (h₂ : ℝ) - 2 / ((h₂ + k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show h₂ + (k + 1) = (h₂ + k) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
      have hd : (1 : ℝ) ≤ ((h₂ + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ h₂ + k)
      have : 1 / (((h₂ + k : ℕ) : ℝ) ^ 2) ≤ 2 / ((h₂ + k : ℕ) : ℝ) - 2 / ((h₂ + k + 1 : ℕ) : ℝ) := by
        push_cast
        push_cast at hd
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases le_total D h₂ with h | h
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, D = h₂ + k := ⟨D - h₂, by omega⟩
    refine (key k).trans ?_
    have : 0 ≤ 2 / ((h₂ + k : ℕ) : ℝ) := by positivity
    linarith

/-- Shifted version: `Σ_{n<K, n − m ≥ h₂, m < n} 1/(n−m)² ≤ 2/h₂`. -/
lemma sum_inv_sq_shift {h₂ : ℕ} (hh : 1 ≤ h₂) (m K : ℕ) :
    ∑ n ∈ range K, (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) ≤ 2 / (h₂ : ℝ) := by
  have : ∑ n ∈ range K, (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) ≤
      ∑ d ∈ Ico h₂ (K + 1), 1 / ((d : ℝ) ^ 2) := by
    rw [← Finset.sum_filter]
    have hinj : ∀ a ∈ (range K).filter (fun n => m < n ∧ h₂ ≤ n - m),
        ∀ b ∈ (range K).filter (fun n => m < n ∧ h₂ ≤ n - m), a - m = b - m → a = b := by
      intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb; omega
    calc ∑ n ∈ (range K).filter (fun n => m < n ∧ h₂ ≤ n - m), 1 / (((n : ℝ) - m) ^ 2)
        = ∑ n ∈ (range K).filter (fun n => m < n ∧ h₂ ≤ n - m), 1 / ((((n - m : ℕ) : ℝ)) ^ 2) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_filter] at hn
          rw [Nat.cast_sub hn.2.1.le]
      _ = ∑ d ∈ ((range K).filter (fun n => m < n ∧ h₂ ≤ n - m)).image (fun n => n - m), 1 / ((d : ℝ) ^ 2) := by
          rw [Finset.sum_image hinj]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro d hd
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
          obtain ⟨n, ⟨hn1, hn2, hn3⟩, rfl⟩ := hd
          simp only [Finset.mem_Ico]; omega
  exact this.trans (sum_inv_sq_tail hh _)

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

lemma sum_inv_sq_shift' {h₂ : ℕ} (hh : 1 ≤ h₂) (n K : ℕ) :
    ∑ m ∈ range K, (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) ≤ 2 / (h₂ : ℝ) := by
  have : ∑ m ∈ range K, (if m < n ∧ h₂ ≤ n - m then 1 / (((n : ℝ) - m) ^ 2) else 0) ≤
      ∑ d ∈ Ico h₂ (n + 1), 1 / ((d : ℝ) ^ 2) := by
    rw [← Finset.sum_filter]
    have hinj : ∀ a ∈ (range K).filter (fun m => m < n ∧ h₂ ≤ n - m),
        ∀ b ∈ (range K).filter (fun m => m < n ∧ h₂ ≤ n - m), n - a = n - b → a = b := by
      intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb; omega
    calc ∑ m ∈ (range K).filter (fun m => m < n ∧ h₂ ≤ n - m), 1 / (((n : ℝ) - m) ^ 2)
        = ∑ m ∈ (range K).filter (fun m => m < n ∧ h₂ ≤ n - m), 1 / ((((n - m : ℕ) : ℝ)) ^ 2) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          simp only [Finset.mem_filter] at hm
          rw [Nat.cast_sub hm.2.1.le]
      _ = ∑ d ∈ ((range K).filter (fun m => m < n ∧ h₂ ≤ n - m)).image (fun m => n - m), 1 / ((d : ℝ) ^ 2) := by
          rw [Finset.sum_image hinj]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro d hd
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
          obtain ⟨m, ⟨hm1, hm2, hm3⟩, rfl⟩ := hd
          simp only [Finset.mem_Ico]; omega
  exact this.trans (sum_inv_sq_tail hh _)

lemma two_abs_le (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- `Su s = Σ λ(n)² n^{−s}`. -/
noncomputable def Su (s : ℝ) : ℝ := ∑' n : ℕ, lam n ^ 2 * (n : ℝ) ^ (-s)

lemma sum_shift_le_Su {s : ℝ} (hs : 1 < s) (t : Finset ℕ) :
    ∑ n ∈ t, lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-s) ≤ Su s := by
  have hsum := (summable_u_rpow hs).1
  have h1 := (summable_nat_add_iff 1).mpr hsum
  calc ∑ n ∈ t, lam (n + 1) ^ 2 * ((n : ℝ) + 1) ^ (-s)
      = ∑ n ∈ t, lam (n + 1) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ (-s) := by push_cast; rfl
    _ ≤ ∑' n : ℕ, lam (n + 1) ^ 2 * (((n + 1 : ℕ) : ℝ)) ^ (-s) :=
        h1.sum_le_tsum t (fun n _ => mul_nonneg (sq_nonneg _) (by positivity))
    _ ≤ Su s := by
        unfold Su
        rw [hsum.tsum_eq_zero_add]
        have : 0 ≤ lam 0 ^ 2 * ((0 : ℕ) : ℝ) ^ (-s) := mul_nonneg (sq_nonneg _) (by
          rw [Nat.cast_zero, Real.zero_rpow (by linarith)])
        linarith

lemma sum_lam_sq_le {A : ℝ} (hA : ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 ≤ A * N) (L : ℕ) (t : Finset ℕ)
    (ht : ∀ n ∈ t, n + 1 ≤ L) : ∑ n ∈ t, lam (n + 1) ^ 2 ≤ A * L := by
  calc ∑ n ∈ t, lam (n + 1) ^ 2 = ∑ k ∈ t.image (· + 1), lam k ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => by omega)]
    _ ≤ ∑ k ∈ Icc 1 L, lam k ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
        intro k hk; simp only [Finset.mem_image] at hk; obtain ⟨n, hn, rfl⟩ := hk
        simp only [Finset.mem_Icc]; exact ⟨by omega, ht n hn⟩
    _ ≤ A * L := hA L

end RamanujanTau.GoodSecondTerm2
