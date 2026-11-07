/-
# The `τ(p)` form: `Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N)` (Deligne)

Abel summation (`TauPNT.abel_identity`) with weights `w(n) = n^{11/2}`: if every partial sum
`S(m) = Σ_{p<m} λ(p) log p`, `m ≤ N`, is bounded by `B`, then `|Σ_{p<N} τ(p) log p| ≤ 2B N^{11/2}`.
From `tau_PNT_error`: for `√N < m ≤ N`, `|S(m)| ≤ K N exp(−b√log √N) ≤ K N exp(−(b/2)√log N)`;
for `m ≤ √N` the trivial `K √N`; together `B ≪ N exp(−(b/2)√log N)`.
-/
import RamanujanTau.TauPNTError.Unsmooth

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Filter Topology
open RamanujanTau.TauPNT RamanujanTau.EdgeNonvanishing

/-- Abel summation with a uniform bound on the partial sums. -/
lemma abel_bound (a w : ℕ → ℝ) (N : ℕ) {B : ℝ} (hw0 : w 0 = 0) (hw : ∀ n, w n ≤ w (n + 1))
    (hS : ∀ m, m ≤ N → |∑ k ∈ Finset.range m, a k| ≤ B) :
    |∑ n ∈ Finset.range N, a n * w n| ≤ 2 * B * w N := by
  rw [abel_identity a w N]
  have hwN : 0 ≤ w N := by
    have : ∀ n, w 0 ≤ w n := fun n => by
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (hw n)
    rw [← hw0]; exact this N
  have h1 : |(∑ m ∈ Finset.range N, a m) * w N| ≤ B * w N := by
    rw [abs_mul, abs_of_nonneg hwN]
    exact mul_le_mul_of_nonneg_right (hS N le_rfl) hwN
  have h2 : |∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n + 1), a m) * (w (n + 1) - w n)| ≤
      B * w N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range N, |(∑ m ∈ Finset.range (n + 1), a m) * (w (n + 1) - w n)|
        ≤ ∑ n ∈ Finset.range N, B * (w (n + 1) - w n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hd : 0 ≤ w (n + 1) - w n := sub_nonneg.mpr (hw n)
          rw [abs_mul, abs_of_nonneg hd]
          exact mul_le_mul_of_nonneg_right (hS (n + 1) (Finset.mem_range.mp hn)) hd
      _ = B * w N := by rw [← Finset.mul_sum, Finset.sum_range_sub (fun n => w n), hw0, sub_zero]
  have := abs_sub ((∑ m ∈ Finset.range N, a m) * w N)
    (∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n + 1), a m) * (w (n + 1) - w n))
  linarith

lemma sqrt_log_sqrt_ge {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (Real.log N) / 2 ≤ Real.sqrt (Real.log (Real.sqrt N)) := by
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN
  rw [Real.log_sqrt (by linarith)]
  rw [show Real.sqrt (Real.log N) / 2 = Real.sqrt (Real.log N / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
  exact Real.sqrt_le_sqrt (by linarith)

set_option maxHeartbeats 1000000 in
/-- Partial summation: a de la Vallée-Poussin bound for `Σ_{p≤N} λ(p) log p` gives one for
`Σ_{p<N} τ(p) log p` (with `b` halved). -/
theorem tau_form_of_prime_bound {b K : ℝ} (hb : 0 < b) (hb256 : b ≤ 1 / 4) (hK : 0 ≤ K)
    (hT : ∀ N : ℕ, 3 ≤ N → |∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p| ≤
      K * N * Real.exp (-b * Real.sqrt (Real.log N))) :
    ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 9 ≤ N →
    |∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p| ≤
      K * (N : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-b * Real.sqrt (Real.log N)) := by
  set K₂ : ℝ := |lam 2 * Real.log 2| with hK₂
  have hK₂0 : 0 ≤ K₂ := abs_nonneg _
  refine ⟨b / 2, by positivity, 2 * (5 * K + 4 * K₂), by positivity, fun N hN => ?_⟩
  have hN9 : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ℓ := Real.sqrt (Real.log N) with hℓ
  set E : ℝ := Real.exp (-(b / 2) * ℓ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set a : ℕ → ℝ := fun n => if n.Prime then lam n * Real.log n else 0 with ha
  set w : ℕ → ℝ := fun n => (n : ℝ) ^ (11 / 2 : ℝ) with hw
  have hw0 : w 0 = 0 := by simp [w]
  have hwmono : ∀ n, w n ≤ w (n + 1) := fun n => by
    simp only [w]; exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
  have hS : ∀ m : ℕ, ∑ k ∈ Finset.range m, a k =
      ∑ p ∈ Finset.range m with p.Prime, lam p * Real.log p := by
    intro m; rw [Finset.sum_filter]
  -- `√N ≤ 4 N E`
  have hsq : Real.sqrt N ≤ 4 * N * E := by
    have h := sqrt_log_le (b := b / 2) (by positivity) (by linarith) (by linarith : (3 : ℝ) ≤ N)
    have hlog : 1 ≤ Real.log N := one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
    have : Real.sqrt N ≤ Real.sqrt N * Real.log N := le_mul_of_one_le_right (Real.sqrt_nonneg _) hlog
    linarith
  have hsqrt3 : 3 ≤ Real.sqrt N := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN9
  set B : ℝ := K * N * E + K * Real.sqrt N + K₂ with hB
  have hbound : ∀ m, m ≤ N → |∑ k ∈ Finset.range m, a k| ≤ B := by
    intro m hm
    have hB1 : 0 ≤ K * N * E := by positivity
    have hB2 : 0 ≤ K * Real.sqrt N := by positivity
    rw [hS]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp only [Finset.range_zero, Finset.filter_empty, Finset.sum_empty, abs_zero]
      linarith
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rcases lt_or_ge j 3 with hj | hj
    · -- small `j`
      have : |∑ p ∈ Finset.range (j + 1) with p.Prime, lam p * Real.log p| ≤ K₂ := by
        interval_cases j
        · simp [Finset.sum_filter, Finset.sum_range_succ]; exact hK₂0
        · simp [Finset.sum_filter, Finset.sum_range_succ, Nat.not_prime_one]; exact hK₂0
        · simp [Finset.sum_filter, Finset.sum_range_succ, Nat.not_prime_one, Nat.prime_two, hK₂]
      linarith
    · have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
      have hjN : (j : ℝ) ≤ N := by exact_mod_cast (by omega : j ≤ N)
      have hTj := hT j hj
      have hEj : Real.exp (-b * Real.sqrt (Real.log j)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have := Real.sqrt_nonneg (Real.log j)
          nlinarith)
      rcases le_or_gt (j : ℝ) (Real.sqrt N) with hjs | hjs
      · have : K * j * Real.exp (-b * Real.sqrt (Real.log j)) ≤ K * Real.sqrt N := by
          calc K * j * Real.exp (-b * Real.sqrt (Real.log j)) ≤ K * j * 1 := by gcongr
            _ ≤ K * Real.sqrt N := by rw [mul_one]; gcongr
        linarith
      · have h1 : ℓ / 2 ≤ Real.sqrt (Real.log j) := by
          refine (sqrt_log_sqrt_ge (by linarith)).trans ?_
          exact Real.sqrt_le_sqrt (Real.log_le_log (by positivity) hjs.le)
        have h2 : Real.exp (-b * Real.sqrt (Real.log j)) ≤ E := by
          rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
        have : K * j * Real.exp (-b * Real.sqrt (Real.log j)) ≤ K * N * E := by
          gcongr
        linarith
  have habel := abel_bound a w N hw0 hwmono hbound
  have hsum : ∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p =
      ∑ n ∈ Finset.range N, a n * w n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [a, w]
    split_ifs with h
    · rw [TauPNT.tau_eq_lam_mul h]; ring
    · simp
  rw [hsum]
  refine habel.trans ?_
  have hN132 : (N : ℝ) ^ (13 / 2 : ℝ) = N * w N := by
    simp only [w]
    rw [show (13 / 2 : ℝ) = 1 + 11 / 2 by norm_num, Real.rpow_add hN0, Real.rpow_one]
  have hwN : 0 ≤ w N := by simp only [w]; positivity
  have hBle : B ≤ (5 * K + 4 * K₂) * N * E := by
    have h1 : K * Real.sqrt N ≤ K * (4 * N * E) := by gcongr
    have h2 : K₂ ≤ K₂ * (4 * N * E) := by
      have : 1 ≤ 4 * N * E := le_trans (by linarith) hsq
      nlinarith
    have : (5 * K + 4 * K₂) * N * E = K * N * E + K * (4 * N * E) + K₂ * (4 * N * E) := by ring
    linarith
  rw [hN132]
  have : 2 * B * w N ≤ 2 * ((5 * K + 4 * K₂) * N * E) * w N := by gcongr
  calc 2 * B * w N ≤ 2 * ((5 * K + 4 * K₂) * N * E) * w N := this
    _ = _ := by rw [hE]; ring

section Deligne

variable [DeligneBound]

/-- **PNT for `τ`, `τ(p)` form, with de la Vallée-Poussin error term** (Deligne):
`Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N)`. -/
theorem tau_PNT_tau_error : ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 9 ≤ N →
    |∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p| ≤
      K * (N : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-b * Real.sqrt (Real.log N)) := by
  obtain ⟨b, hb, hb256, K, hK, hT⟩ := tau_PNT_error
  exact tau_form_of_prime_bound hb (by linarith) hK hT

end Deligne

end RamanujanTau.TauPNTError
