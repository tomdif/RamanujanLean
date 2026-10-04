/-
# Kolberg's theorem (1959): `p(n)` is even infinitely often and odd infinitely often

From Euler's pentagonal recurrence modulo 2. If `p(n) ≡ c (mod 2)` for all `n ≥ N`, take `n = ω(N) + r` with
`r < N` and `ω(N) = (N+1)(3N+2)/2`. The pentagonal numbers around `ω(N)` are more than `N` apart, so in
`p(n) ≡ Σ_m (p(n − ω₁(m)) + p(n − ω₂(m)))` every `m < N` contributes `c + c ≡ 0`, `m = N` contributes `p(r)`,
and larger `m` contribute nothing. So `p(r) ≡ c` for all `r < N` as well, contradicting `p(0) = 1`, `p(2) = 2`.
-/
import RamanujanTau.MockTheta5PentagonalRecurrence

set_option autoImplicit false

namespace MockTheta5.JTP.Kolberg
open PowerSeries Finset

/-- the generalized pentagonal numbers `ω₁(m) = (m+1)(3m+2)/2`, `ω₂(m) = (m+1)(3m+4)/2`. -/
def g1 (m : ℕ) : ℕ := (m + 1) * (3 * m + 2) / 2
def g2 (m : ℕ) : ℕ := (m + 1) * (3 * m + 4) / 2

lemma g2_eq (m : ℕ) : g2 m = g1 m + (m + 1) := by
  rw [g2, g1, show (m + 1) * (3 * m + 4) = (m + 1) * (3 * m + 2) + (m + 1) * 2 by ring, Nat.add_mul_div_right _ _ two_pos]

lemma g1_succ (m : ℕ) : g1 (m + 1) = g2 m + (2 * m + 3) := by
  rw [g2, g1, show (m + 1 + 1) * (3 * (m + 1) + 2) = (m + 1) * (3 * m + 4) + (2 * m + 3) * 2 by ring,
    Nat.add_mul_div_right _ _ two_pos]

lemma g1_mono {m m' : ℕ} (h : m ≤ m') : g1 m ≤ g1 m' :=
  Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

lemma g2_mono {m m' : ℕ} (h : m ≤ m') : g2 m ≤ g2 m' :=
  Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

lemma le_g1 (m : ℕ) : m ≤ g1 m := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih => rw [g1_succ, g2_eq]; omega

/-- `p(n)` modulo 2. -/
noncomputable def P (n : ℕ) : ZMod 2 := ((coeff n partitionGF : ℤ) : ZMod 2)

/-- Euler's recurrence modulo 2. -/
lemma P_rec (n : ℕ) (hn : 0 < n) :
    P n = ∑ m ∈ range (n + 1), ((if g1 m ≤ n then P (n - g1 m) else 0) + (if g2 m ≤ n then P (n - g2 m) else 0)) := by
  have h := congrArg (fun z : ℤ => (z : ZMod 2)) (partition_pentagonal_recurrence n hn)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_add] at h
  rw [P, h]
  refine sum_congr rfl fun m _ => ?_
  rw [show ((-1 : ZMod 2)) = 1 by decide, one_pow, one_mul]
  simp only [g1, g2, P]
  split_ifs <;> simp

/-- if `p` is eventually constant mod 2, it is constant mod 2. -/
lemma P_const {N : ℕ} {c : ZMod 2} (H : ∀ n, N ≤ n → P n = c) (r : ℕ) (hr : r < N) : P r = c := by
  set n := g1 N + r with hn
  have hNn : N ≤ n := by have := le_g1 N; omega
  have hgap : g1 N = g2 (N - 1) + (2 * N + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [g1_succ, show k + 1 - 1 = k by omega]; ring
  rw [← H n hNn, P_rec n (by omega)]
  have hsplit : range (n + 1) = range N ∪ ({N} ∪ Ico (N + 1) (n + 1)) := by
    ext m; simp only [mem_union, mem_range, mem_singleton, mem_Ico]; omega
  rw [hsplit, sum_union (by simp [disjoint_left]; omega), sum_union (by simp), sum_singleton]
  -- `m < N`: both indices are `≥ N`, so the pair contributes `c + c = 0`
  rw [sum_eq_zero (s := range N) fun m hm => by
    simp only [mem_range] at hm
    have h1 : g2 m ≤ g2 (N - 1) := g2_mono (by omega)
    have h2 := g2_eq m
    rw [if_pos (by omega), if_pos (by omega), H _ (by omega), H _ (by omega)]
    fin_cases c <;> decide]
  -- `m > N`: no contribution
  rw [sum_eq_zero (s := Ico (N + 1) (n + 1)) fun m hm => by
    simp only [mem_Ico] at hm
    have h1 : g1 (N + 1) ≤ g1 m := g1_mono (by omega)
    have h2 := g1_succ N
    have h3 := g2_eq N
    have h4 := g2_eq m
    rw [if_neg (by omega), if_neg (by omega), add_zero]]
  have h3 := g2_eq N
  rw [if_pos (by omega), if_neg (by omega), show n - g1 N = r by omega]
  simp

lemma P_zero : P 0 = 1 := by
  rw [P, coeff_partitionGF_eq_card]; decide

lemma P_one : P 1 = 1 := by
  rw [P_rec 1 (by norm_num)]; simp [sum_range_succ, g1, g2, P_zero]

lemma P_two : P 2 = 0 := by
  rw [P_rec 2 (by norm_num)]; simp [sum_range_succ, g1, g2, P_zero, P_one]; decide

/-- **Kolberg's theorem**: `p(n)` takes even values and odd values infinitely often. -/
theorem kolberg (N : ℕ) :
    (∃ n, N ≤ n ∧ Even (Fintype.card (Nat.Partition n))) ∧ (∃ n, N ≤ n ∧ Odd (Fintype.card (Nat.Partition n))) := by
  have hP : ∀ n, P n = 0 ↔ Even (Fintype.card (Nat.Partition n)) := by
    intro n
    rw [P, coeff_partitionGF_eq_card, Int.cast_natCast, ZMod.natCast_eq_zero_iff_even]
  constructor
  · by_contra hc
    push Not at hc
    have H : ∀ n, N + 3 ≤ n → P n = 1 := fun n hn => by
      have := hc n (by omega)
      rw [← hP] at this
      revert this; generalize P n = x; fin_cases x <;> intro h <;> first | exact absurd rfl h | rfl
    have := P_const H 2 (by omega)
    rw [P_two] at this; exact absurd this (by decide)
  · by_contra hc
    push Not at hc
    have H : ∀ n, N + 3 ≤ n → P n = 0 := fun n hn => by
      have := hc n (by omega)
      rw [Nat.not_odd_iff_even, ← hP] at this
      exact this
    have := P_const H 0 (by omega)
    rw [P_zero] at this; exact absurd this (by decide)

end MockTheta5.JTP.Kolberg
