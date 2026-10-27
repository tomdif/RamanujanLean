/-
# A certified table of `p(n)` and the finite range of the log-concavity check

`ptab N = [p(N), p(N−1), …, p(0)]`, built by Euler's pentagonal recurrence; `ptab_spec` identifies its
entries with `#(Nat.Partition n)`. The kernel then checks `p(n)² > p(n−1)p(n+1)` for `26 ≤ n ≤ 548`
(`logConcave_table`).
-/
import RamanujanTau.MockTheta5PentagonalRecurrence

set_option autoImplicit false

namespace LogConcave
open PowerSeries MockTheta5.JTP MockTheta5.Bailey

/-- the generalized pentagonal numbers `g₁(m) = (m+1)(3m+2)/2`, `g₂(m) = (m+1)(3m+4)/2`. -/
def g1 (m : ℕ) : ℕ := (m + 1) * (3 * m + 2) / 2
def g2 (m : ℕ) : ℕ := (m + 1) * (3 * m + 4) / 2

/-- the next value from the reversed table `R = [c(N−1), …, c(0)]`. -/
def nextP (R : List ℤ) : ℤ :=
  ∑ m ∈ Finset.range (Nat.sqrt R.length + 1), (-1 : ℤ) ^ m * (R.getD (g1 m - 1) 0 + R.getD (g2 m - 1) 0)

/-- `ptab N = [p(N), …, p(0)]`. -/
def ptab : ℕ → List ℤ
  | 0 => [1]
  | N + 1 => nextP (ptab N) :: ptab N

lemma ptab_length (N : ℕ) : (ptab N).length = N + 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [ptab, ih]

local notation "c" => fun n : ℕ => coeff n partitionGF

lemma g1_pos (m : ℕ) : 1 ≤ g1 m := by
  unfold g1; have : 2 ≤ (m + 1) * (3 * m + 2) := by nlinarith
  omega

lemma g2_pos (m : ℕ) : 1 ≤ g2 m := by
  unfold g2; have : 2 ≤ (m + 1) * (3 * m + 4) := by nlinarith
  omega

lemma sq_lt_g1 {N m : ℕ} (hm : Nat.sqrt N + 1 ≤ m) : N < g1 m := by
  have h1 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  unfold g1
  have : (m + 1) * (m + 1) * 2 ≤ (m + 1) * (3 * m + 2) := by nlinarith
  have : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

lemma g1_le_g2 (m : ℕ) : g1 m ≤ g2 m := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))

lemma getD_ptab (N : ℕ) : ∀ i, (ptab N).getD i 0 = if i ≤ N then c (N - i) else 0 := by
  induction N with
  | zero =>
    intro i
    rcases i with _ | i
    · simp only [ptab, List.getD_cons_zero, le_refl, if_true, Nat.sub_zero]
      rw [coeff_partitionGF_eq_card]; rfl
    · simp [ptab]
  | succ N ih =>
    intro i
    rcases i with _ | i
    · simp only [ptab, List.getD_cons_zero, zero_le, if_true, Nat.sub_zero]
      rw [partition_pentagonal_recurrence (N + 1) (by omega), nextP, ptab_length]
      have hterm : ∀ m, (-1 : ℤ) ^ m * ((ptab N).getD (g1 m - 1) 0 + (ptab N).getD (g2 m - 1) 0) =
          (-1 : ℤ) ^ m * ((if (m + 1) * (3 * m + 2) / 2 ≤ N + 1 then
              coeff (N + 1 - (m + 1) * (3 * m + 2) / 2) partitionGF else 0) +
            (if (m + 1) * (3 * m + 4) / 2 ≤ N + 1 then
              coeff (N + 1 - (m + 1) * (3 * m + 4) / 2) partitionGF else 0)) := by
        intro m
        have h1 := g1_pos m
        have h2 := g2_pos m
        rw [ih, ih]
        unfold g1 g2 at *
        congr 2
        · by_cases h : (m + 1) * (3 * m + 2) / 2 ≤ N + 1
          · rw [if_pos (by omega), if_pos h, show N - ((m + 1) * (3 * m + 2) / 2 - 1) = N + 1 - (m + 1) * (3 * m + 2) / 2 by omega]
          · rw [if_neg (by omega), if_neg h]
        · by_cases h : (m + 1) * (3 * m + 4) / 2 ≤ N + 1
          · rw [if_pos (by omega), if_pos h, show N - ((m + 1) * (3 * m + 4) / 2 - 1) = N + 1 - (m + 1) * (3 * m + 4) / 2 by omega]
          · rw [if_neg (by omega), if_neg h]
      simp only [hterm]
      apply Finset.sum_subset
      · exact Finset.range_subset_range.mpr (by have := Nat.sqrt_le_self (N + 1); omega)
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        have h1 := sq_lt_g1 (N := N + 1) hm
        have h2 := g1_le_g2 m
        unfold g1 g2 at *
        rw [if_neg (by omega), if_neg (by omega)]; ring
    · simp only [ptab, List.getD_cons_succ, ih]
      by_cases h : i ≤ N
      · rw [if_pos h, if_pos (by omega), show N + 1 - (i + 1) = N - i by omega]
      · rw [if_neg h, if_neg (by omega)]

def getP (R : List ℤ) (N m : ℕ) : ℤ := R.getD (N - m) 0

def lcCheck (N lo hi : ℕ) : Bool :=
  (List.range' lo (hi + 1 - lo)).all fun n =>
    decide (getP (ptab N) N (n - 1) * getP (ptab N) N (n + 1) < getP (ptab N) N n ^ 2)

lemma getP_eq {N m : ℕ} (hm : m ≤ N) : getP (ptab N) N m = (Fintype.card (Nat.Partition m) : ℤ) := by
  rw [getP, getD_ptab, if_pos (by omega), show N - (N - m) = m by omega]
  exact coeff_partitionGF_eq_card m

lemma lcCheck_spec {N lo hi : ℕ} (h : lcCheck N lo hi = true) (hN : hi + 1 ≤ N) {n : ℕ} (hlo : lo ≤ n)
    (hhi : n ≤ hi) :
    (Fintype.card (Nat.Partition (n - 1)) : ℤ) * Fintype.card (Nat.Partition (n + 1)) <
      (Fintype.card (Nat.Partition n) : ℤ) ^ 2 := by
  rw [lcCheck, List.all_eq_true] at h
  have := h n (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
  rw [decide_eq_true_eq, getP_eq (by omega), getP_eq (by omega), getP_eq (by omega)] at this
  exact this

theorem lcCheck_548 : lcCheck 549 26 548 = true := by decide +kernel

/-- **`p(n)² > p(n−1)p(n+1)` for `26 ≤ n ≤ 548`**, by kernel computation. -/
theorem logConcave_table {n : ℕ} (h1 : 26 ≤ n) (h2 : n ≤ 548) :
    (Fintype.card (Nat.Partition (n - 1)) : ℤ) * Fintype.card (Nat.Partition (n + 1)) <
      (Fintype.card (Nat.Partition n) : ℤ) ^ 2 :=
  lcCheck_spec lcCheck_548 (by norm_num) h1 h2

end LogConcave
