/-
# Counting lemmas for the subgroups `⟨s⟩ ⊂ Tate(s^p)`

The nonzero points of `⟨s⟩` are `u = s^k` (`1 ≤ k < p`), and the monomials `s^{d(pn ± k)}` of the
Tate series at these points are reorganised by the divisors of the exponent (`comb`):
every `e ≥ 1` with `p ∤ e` is `pn + k` (`n ≥ 0`) for exactly one `k`, and `pn − k` (`n ≥ 1`) for
exactly one `k`.
-/
import Mathlib

set_option autoImplicit false

noncomputable section

namespace TateQuot

open Finset

variable {K : Type*} [Field K] [CharZero K]

lemma count_plus {p k e B : ℕ} (hk : k < p) (hB : e < B) :
    ∑ n ∈ range B, (if p * n + k = e then (1 : K) else 0) = if e % p = k then 1 else 0 := by
  have hp : 0 < p := by omega
  have key : ∀ n, (p * n + k = e ↔ n = e / p ∧ e % p = k) := fun n => by
    rw [eq_comm (a := n), Nat.div_mod_unique hp]; constructor
    · intro h; exact ⟨by rw [← h]; ring, hk⟩
    · rintro ⟨h, -⟩; rw [← h]; ring
  simp only [key]
  by_cases h : e % p = k
  · simp only [h, and_true, if_true]
    rw [sum_ite_eq', if_pos]
    rw [mem_range]
    exact lt_of_le_of_lt (Nat.div_le_self e p) hB
  · simp [h]

lemma count_minus {p k e B : ℕ} (hk1 : 1 ≤ k) (hk : k < p) (he : 1 ≤ e) (hB : e < B) :
    ∑ n ∈ range B, (if n ≠ 0 ∧ p * n - k = e then (1 : K) else 0) =
      if (e + k) % p = 0 then 1 else 0 := by
  have hp : 0 < p := by omega
  have key : ∀ n, (n ≠ 0 ∧ p * n - k = e ↔ n = (e + k) / p ∧ (e + k) % p = 0) := fun n => by
    constructor
    · rintro ⟨hn, h⟩
      have h1 : p ≤ p * n := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hn)
      have h2 : p * n = e + k := by omega
      rw [← h2, Nat.mul_div_cancel_left _ hp, Nat.mul_mod_right]; exact ⟨rfl, rfl⟩
    · rintro ⟨h, h0⟩
      have h2 : p * n = e + k := by rw [h]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
      refine ⟨?_, by omega⟩
      rintro rfl; omega
  simp only [key]
  by_cases h : (e + k) % p = 0
  · simp only [h, and_true, if_true]
    rw [sum_ite_eq', if_pos]
    rw [mem_range]
    have : (e + k) / p ≤ e := by
      rw [Nat.div_le_iff_le_mul_add_pred hp]
      nlinarith
    omega
  · simp [h]

lemma count_k {p e : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ Ico 1 p, ((if e % p = k then (1 : K) else 0) + (if (e + k) % p = 0 then 1 else 0)) =
      if p ∣ e then 0 else 2 := by
  have hp0 : 0 < p := by omega
  have hr : e % p < p := Nat.mod_lt e hp0
  have hmod : ∀ k ∈ Ico 1 p, ((e + k) % p = 0 ↔ k = p - e % p ∧ e % p ≠ 0) := by
    intro k hk
    rw [mem_Ico] at hk
    rw [Nat.add_mod, Nat.mod_eq_of_lt hk.2]
    constructor
    · intro h
      have h1 : (e % p + k) % p = 0 := h
      have h2 : e % p + k < 2 * p := by omega
      have h3 : e % p + k = p := by
        rcases Nat.lt_or_ge (e % p + k) p with h4 | h4
        · rw [Nat.mod_eq_of_lt h4] at h1; omega
        · have := Nat.mod_eq_sub_mod h4
          rw [this, Nat.mod_eq_of_lt (by omega)] at h1; omega
      omega
    · rintro ⟨h1, h2⟩
      rw [h1, Nat.add_sub_cancel' hr.le, Nat.mod_self]
  have h2 : ∑ k ∈ Ico 1 p, (if (e + k) % p = 0 then (1 : K) else 0) =
      ∑ k ∈ Ico 1 p, (if k = p - e % p ∧ e % p ≠ 0 then (1 : K) else 0) :=
    sum_congr rfl fun k hk => if_congr (hmod k hk) rfl rfl
  rw [sum_add_distrib, h2]
  simp only [Nat.dvd_iff_mod_eq_zero]
  by_cases hd : e % p = 0
  · simp only [hd, ne_eq, not_true_eq_false, and_false, if_false, sum_const_zero, add_zero,
      if_true]
    rw [sum_ite_eq, if_neg (by simp)]
  · simp only [hd, ne_eq, not_false_eq_true, and_true, if_false]
    rw [sum_ite_eq, sum_ite_eq', if_pos (by simp only [mem_Ico]; omega),
      if_pos (by simp only [mem_Ico]; omega)]
    norm_num

lemma exp_plus (p k d n : ℕ) (hk : k ≤ p) : k * (d * n + d) + (p - k) * (d * n) = d * (p * n + k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]; ring

lemma exp_minus (p k d n : ℕ) (hk : k < p) (hn : 1 ≤ n) :
    k * (d * n - d) + (p - k) * (d * n) = d * (p * n - k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : d * (1 + n') - d = d * n' := by rw [mul_add, mul_one, Nat.add_sub_cancel_left]
  have h2 : (k + j + 1) * (1 + n') = k * n' + (j + 1) * (1 + n') + k := by ring
  rw [h1, h2, Nat.add_sub_cancel, show k + j + 1 - k = j + 1 by omega]; ring

/-- The bracket `[e ≡ k] + [e ≡ −k] (mod p)`. -/
def br (p e k : ℕ) : K := (if e % p = k then 1 else 0) + (if (e + k) % p = 0 then 1 else 0)

/-- The count for fixed `d ≥ 1` and `1 ≤ k < p`. -/
lemma per_dk {p : ℕ} (hp : 2 ≤ p) (M d : ℕ) (hd : 1 ≤ d) {k : ℕ} (hk : 1 ≤ k ∧ k < p) :
    (if d * k = M then (1 : K) else 0) +
      ∑ n ∈ range (M + 1), (if n ≠ 0 ∧ d * n ≤ M then
        ((if k * (d * n + d) + (p - k) * (d * n) = M then (1 : K) else 0) +
          (if k * (d * n - d) + (p - k) * (d * n) = M then 1 else 0)) else 0) =
      if d ∣ M ∧ M ≠ 0 then br p (M / d) k else 0 := by
  have hd0 : d ≠ 0 := by omega
  have hsum : ∑ n ∈ range (M + 1), (if n ≠ 0 ∧ d * n ≤ M then
        ((if k * (d * n + d) + (p - k) * (d * n) = M then (1 : K) else 0) +
          (if k * (d * n - d) + (p - k) * (d * n) = M then 1 else 0)) else 0) =
      ∑ n ∈ range (M + 1), ((if n ≠ 0 ∧ d * (p * n + k) = M then (1 : K) else 0) +
          (if n ≠ 0 ∧ d * (p * n - k) = M then 1 else 0)) := by
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [exp_plus p k d n hk.2.le, exp_minus p k d n hk.2 hn1]
      by_cases hle : d * n ≤ M
      · simp [hn, hle]
      · have h1 : ¬ d * (p * n + k) = M := by
          intro h; apply hle; rw [← h]; apply Nat.mul_le_mul_left; nlinarith
        have h2 : ¬ d * (p * n - k) = M := by
          intro h; apply hle; rw [← h]; apply Nat.mul_le_mul_left
          have : p * n - k ≥ n := by
            have h3 : p * n + 1 ≥ p + n := by
              obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn1
              nlinarith
            omega
          omega
        simp [hn, hle, h1, h2]
  rw [hsum]
  by_cases hM : d ∣ M ∧ M ≠ 0
  · obtain ⟨⟨e, rfl⟩, hM0⟩ := hM
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hM0
      · exact h
    rw [if_pos (show d ∣ d * e ∧ d * e ≠ 0 from ⟨dvd_mul_right d e, hM0⟩),
      Nat.mul_div_cancel_left _ (by omega)]
    simp only [mul_right_inj' hd0]
    have hB : e < d * e + 1 := by nlinarith
    rw [br, sum_add_distrib, ← add_assoc]
    congr 1
    · rw [← count_plus (K := K) hk.2 hB, sum_range_succ' _ (d * e), sum_range_succ' _ (d * e)]
      simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, true_and, mul_zero, zero_add,
        not_true_eq_false, false_and, if_false, add_zero]
      rw [add_comm]
    · rw [← count_minus (K := K) hk.1 hk.2 he hB]
  · rw [if_neg hM]
    have h0 : ¬ d * k = M := by
      intro h; exact hM ⟨⟨k, h.symm⟩, by rw [← h]; exact mul_ne_zero hd0 (by omega)⟩
    rw [if_neg h0, zero_add]
    refine sum_eq_zero fun n _ => ?_
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hpos2 : 0 < p * n - k := by
        have : p * n ≥ p := Nat.le_mul_of_pos_right p hn1
        omega
      have h1 : ¬ d * (p * n + k) = M := by
        intro h; exact hM ⟨⟨_, h.symm⟩, by rw [← h]; exact mul_ne_zero hd0 (by omega)⟩
      have h2 : ¬ d * (p * n - k) = M := by
        intro h; exact hM ⟨⟨_, h.symm⟩, by rw [← h]; exact mul_ne_zero hd0 (by omega)⟩
      simp [h1, h2]

lemma sum_divisors_range {M N : ℕ} (hN : N ≤ M) (H : ℕ → K) :
    ∑ d ∈ N.divisors, H d = ∑ d ∈ range (M + 1), (if N ≠ 0 ∧ d ∣ N then H d else 0) := by
  rw [← sum_filter]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1; omega, h2, h1⟩
  · rintro ⟨-, h2, h1⟩; exact ⟨h1, h2⟩

lemma reindex_mul {M d : ℕ} (hd : 1 ≤ d) (G : ℕ → K) :
    ∑ N ∈ range (M + 1), (if N ≠ 0 ∧ d ∣ N then G N else 0) =
      ∑ n ∈ range (M + 1), (if n ≠ 0 ∧ d * n ≤ M then G (d * n) else 0) := by
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (fun N => N / d) (fun n => d * n) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    simp only [mem_coe, mem_filter, mem_range] at hN ⊢
    obtain ⟨hN1, hN0, c, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left _ (by omega)]
    refine ⟨?_, ?_, by omega⟩
    · have : c ≤ d * c := Nat.le_mul_of_pos_left c (by omega)
      omega
    · rintro rfl; simp at hN0
  · intro n hn
    simp only [mem_coe, mem_filter, mem_range] at hn ⊢
    exact ⟨by omega, mul_ne_zero (by omega) hn.2.1, dvd_mul_right d n⟩
  · intro N hN
    simp only [mem_coe, mem_filter] at hN
    exact Nat.mul_div_cancel' hN.2.2
  · intro n _
    exact Nat.mul_div_cancel_left _ (by omega)
  · intro N hN
    simp only [mem_filter] at hN
    rw [Nat.mul_div_cancel' hN.2.2]

/-- **The reorganisation at one point `s^k`.** -/
theorem comb_k {p : ℕ} (hp : 2 ≤ p) (f : ℕ → K) (hf0 : f 0 = 0) (M : ℕ) {k : ℕ}
    (hk : k ∈ Ico 1 p) :
    (if k ∣ M then f (M / k) else 0) +
      ∑ N ∈ range (M + 1), ∑ d ∈ N.divisors, f d *
        ((if k * (N + d) + (p - k) * N = M then 1 else 0) +
          (if k * (N - d) + (p - k) * N = M then 1 else 0)) =
      ∑ d ∈ M.divisors, f d * br p (M / d) k := by
  have hk' := mem_Ico.mp hk
  have hconst : (if k ∣ M then f (M / k) else 0) =
      ∑ d ∈ range (M + 1), f d * (if d * k = M then 1 else 0) := by
    by_cases h : k ∣ M
    · obtain ⟨c, rfl⟩ := h
      rw [if_pos (dvd_mul_right k c), Nat.mul_div_cancel_left _ (by omega)]
      simp only [mul_comm _ k, mul_right_inj' (by omega : k ≠ 0)]
      rw [sum_congr rfl fun d _ => by rw [mul_ite, mul_one, mul_zero], sum_ite_eq', if_pos]
      rw [mem_range]
      have : c ≤ k * c := Nat.le_mul_of_pos_left c (by omega)
      omega
    · rw [if_neg h]
      refine (sum_eq_zero fun d _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl; exact h (dvd_mul_left k d)
  rw [hconst, sum_congr rfl fun N hN => sum_divisors_range
      (Nat.lt_succ_iff.mp (mem_range.mp hN)) _, sum_comm, ← sum_add_distrib,
    sum_divisors_range le_rfl]
  refine sum_congr rfl fun d hd => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · simp [hf0]
  have hG : f d * (if d * k = M then 1 else 0) +
      ∑ N ∈ range (M + 1), (if N ≠ 0 ∧ d ∣ N then f d *
        ((if k * (N + d) + (p - k) * N = M then 1 else 0) +
          (if k * (N - d) + (p - k) * N = M then 1 else 0)) else 0) =
      f d * ((if d * k = M then (1 : K) else 0) +
      ∑ n ∈ range (M + 1), (if n ≠ 0 ∧ d * n ≤ M then
        ((if k * (d * n + d) + (p - k) * (d * n) = M then (1 : K) else 0) +
          (if k * (d * n - d) + (p - k) * (d * n) = M then 1 else 0)) else 0)) := by
    rw [reindex_mul hd1, mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [hG, per_dk hp M d hd1 hk']
  by_cases h : d ∣ M ∧ M ≠ 0
  · simp only [h.1, h.2, true_and, and_true, ne_eq, not_false_eq_true, if_true]
  · have h' : ¬(M ≠ 0 ∧ d ∣ M) := fun h' => h ⟨h'.2, h'.1⟩
    rw [if_neg h, if_neg h', mul_zero]

/-- `br` is symmetric under `k ↦ p − k`. -/
lemma br_sym {p e k : ℕ} (hk : k ∈ Ico 1 p) : br (K := K) p e (p - k) = br p e k := by
  rw [mem_Ico] at hk
  have hp0 : 0 < p := by omega
  have key : ∀ j, 1 ≤ j → j < p → ((e + j) % p = 0 ↔ e % p = p - j) := by
    intro j hj1 hj2
    rw [Nat.add_mod, Nat.mod_eq_of_lt hj2]
    have hr : e % p < p := Nat.mod_lt e hp0
    constructor
    · intro h
      rcases Nat.lt_or_ge (e % p + j) p with h4 | h4
      · rw [Nat.mod_eq_of_lt h4] at h; omega
      · rw [Nat.mod_eq_sub_mod h4, Nat.mod_eq_of_lt (by omega)] at h; omega
    · intro h; rw [h, Nat.sub_add_cancel hj2.le, Nat.mod_self]
  unfold br
  rw [if_congr (key (p - k) (by omega) (by omega)) rfl rfl, if_congr (key k hk.1 hk.2) rfl rfl,
    Nat.sub_sub_self hk.2.le, add_comm]

/-- **The reorganisation over all the points `s^k`, `1 ≤ k < p`.** -/
theorem comb {p : ℕ} (hp : 2 ≤ p) (f : ℕ → K) (hf0 : f 0 = 0) (M : ℕ) :
    ∑ k ∈ Ico 1 p, ((if k ∣ M then f (M / k) else 0) +
      ∑ N ∈ range (M + 1), ∑ d ∈ N.divisors, f d *
        ((if k * (N + d) + (p - k) * N = M then 1 else 0) +
          (if k * (N - d) + (p - k) * N = M then 1 else 0))) =
      ∑ d ∈ M.divisors, f d * (if p ∣ M / d then 0 else 2) := by
  rw [sum_congr rfl fun k hk => comb_k hp f hf0 M hk, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum]
  congr 1
  exact count_k hp

end TateQuot
