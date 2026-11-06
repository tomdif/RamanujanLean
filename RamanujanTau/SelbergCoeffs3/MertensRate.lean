/-
# Mertens II for `λ(p)²` with the rate `O(1/log N)` (unconditional)

    |Σ_{p≤N} λ(p)²/p − log log N − c_Δ| ≤ C / log N      (N ≥ 2).

From `SelbergCoeffs2.TT_decomp`: `T(N) − log log N − c_Δ = −(tail of Σ h_k) + (LL(N+1) − LL(N))
+ (P(N)/log(N+1) − 1)`; each piece is `≪ 1/log N`:
* tail: `Σ_{k>N} |h_k| ≤ Σ_{k>N} (1/(k² log²2) + E(w_k − w_{k+1})) ≤ 1/(N log²2) + E/log(N+1)`
  (both telescoping, finite sums then a limit);
* `0 ≤ LL(N+1) − LL(N) ≤ (log(N+1) − log N)/log N ≤ 1/log N`;
* `|P(N) − log(N+1)| ≤ E + 1`.
-/
import RamanujanTau.SelbergCoeffs2.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs3

open Finset Filter Topology
open RamanujanTau.EdgeNonvanishing (lam)
open RamanujanTau.SelbergCoeffs2

noncomputable section

lemma sum_Ioc_hh_eq_range (N : ℕ) : ∑ k ∈ Ioc 0 N, hh k = ∑ k ∈ range (N + 1), hh k := by
  have h0 : hh 0 = 0 := by simp [hh, ww, LL, PP]
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [sum_range_succ, ← ih, sum_Ioc_succ_top (Nat.zero_le N)]

lemma tendsto_sum_hh : Tendsto (fun M : ℕ => ∑ k ∈ Ioc 0 M, hh k) atTop (𝓝 (∑' k, hh k)) := by
  have h := (summable_hh.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  exact h.congr fun M => (sum_Ioc_hh_eq_range M).symm

lemma ww_nonneg (k : ℕ) : 0 ≤ ww k := by
  unfold ww; exact div_nonneg zero_le_one (Real.log_natCast_nonneg _)

lemma inv_sq_le_tele {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / k := by
  have hk1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
  have e : ((k - 1 : ℕ) : ℝ) = k - 1 := by push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
  rw [e] at hk1 ⊢
  have hk0 : (0 : ℝ) < k - 1 := by linarith
  rw [div_sub_div _ _ hk0.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma sum_inv_sq_Ioc_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ k ∈ Ioc N M, 1 / (k : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((max M N : ℕ) : ℝ) := by
  induction M with
  | zero => rw [max_eq_right (Nat.zero_le N)]; simp
  | succ M ih =>
    rcases le_or_gt N M with h | h
    · rw [sum_Ioc_succ_top h, max_eq_left (by omega : N ≤ M + 1)]
      rw [max_eq_left h] at ih
      have := inv_sq_le_tele (k := M + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      push_cast at this ⊢
      linarith
    · rw [Ioc_eq_empty (by omega), max_eq_right (by omega)]; simp

lemma sum_ww_Ioc (N M : ℕ) (h : N ≤ M) :
    ∑ k ∈ Ioc N M, (ww k - ww (k + 1)) = ww (N + 1) - ww (M + 1) := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hNM ih => rw [sum_Ioc_succ_top hNM, ih]; ring

/-- Tail bound for `Σ h_k`. -/
lemma tail_hh_le : ∃ D : ℝ, ∀ N : ℕ, 2 ≤ N →
    |∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k| ≤ D / Real.log N := by
  obtain ⟨E, hE⟩ := mertens1_prime
  have hE' : ∀ N : ℕ, 1 ≤ N → |PP N - Real.log N| ≤ E := hE
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE' 1 le_rfl)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2 ^ 2 + E, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : 0 < Real.log N := hl2.trans_le (log_two_le_log hN)
  have hfin : ∀ M : ℕ, N ≤ M → |∑ k ∈ Ioc 0 M, hh k - ∑ k ∈ Ioc 0 N, hh k| ≤
      1 / (Real.log 2 ^ 2 * N) + E * ww (N + 1) := by
    intro M hM
    rw [← sum_Ioc_consecutive hh (Nat.zero_le N) hM, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ k ∈ Ioc N M, |hh k| ≤ 1 / Real.log 2 ^ 2 * (1 / (k : ℝ) ^ 2) +
        E * (ww k - ww (k + 1)) := by
      intro k hk
      have := abs_hh_le hE' (k := k) (by have := (mem_Ioc.mp hk).1; omega)
      rw [show 1 / (Real.log 2 ^ 2 * (k : ℝ) ^ 2) = 1 / Real.log 2 ^ 2 * (1 / (k : ℝ) ^ 2) by
        rw [one_div_mul_one_div]] at this
      exact this
    refine (sum_le_sum hb).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_ww_Ioc N M hM]
    have h1 := sum_inv_sq_Ioc_le (by omega : 1 ≤ N) M
    have hmax : 0 ≤ 1 / ((max M N : ℕ) : ℝ) := by positivity
    have h2 : 0 ≤ ww (M + 1) := ww_nonneg _
    have : 1 / Real.log 2 ^ 2 * (1 / (N : ℝ)) = 1 / (Real.log 2 ^ 2 * N) := one_div_mul_one_div _ _
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / Real.log 2 ^ 2 by positivity),
      mul_nonneg (show 0 ≤ 1 / Real.log 2 ^ 2 by positivity) hmax, mul_nonneg hE0 h2]
  have hlim : Tendsto (fun M : ℕ => |∑ k ∈ Ioc 0 M, hh k - ∑ k ∈ Ioc 0 N, hh k|) atTop
      (𝓝 |∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k|) :=
    (tendsto_sum_hh.sub_const _).abs
  have hle := le_of_tendsto hlim (eventually_atTop.mpr ⟨N, hfin⟩)
  -- `1/(log²2 · N) ≤ (1/log²2)/log N` and `ww(N+1) ≤ 1/log N`
  have hNlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have h1 : 1 / (Real.log 2 ^ 2 * N) ≤ 1 / Real.log 2 ^ 2 / Real.log N := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.log 2)]
  have h2 : ww (N + 1) ≤ 1 / Real.log N := by
    unfold ww
    exact one_div_le_one_div_of_le hLN (Real.log_le_log hN0 (by push_cast; linarith))
  calc |∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k| ≤ 1 / (Real.log 2 ^ 2 * N) + E * ww (N + 1) := hle
    _ ≤ 1 / Real.log 2 ^ 2 / Real.log N + E * (1 / Real.log N) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hE0)
    _ = (1 / Real.log 2 ^ 2 + E) / Real.log N := by ring

/-- **Mertens II with rate** (unconditional):
`|Σ_{p≤N} λ(p)²/p − log log N − c_Δ| ≤ C/log N` for `N ≥ 2`. -/
theorem mertens2_rate : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    |∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p - Real.log (Real.log N) - cMertens| ≤
      C / Real.log N := by
  obtain ⟨D, hD⟩ := tail_hh_le
  obtain ⟨E, hE⟩ := mertens1_prime
  have hE' : ∀ N : ℕ, 1 ≤ N → |PP N - Real.log N| ≤ E := hE
  refine ⟨D + 1 + (E + 1), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLN : 0 < Real.log N := hl2.trans_le (log_two_le_log hN)
  have hLL' : Real.log N ≤ Real.log (N + 1 : ℕ) := Real.log_le_log hN0 (by push_cast; linarith)
  have hL'0 : 0 < Real.log (N + 1 : ℕ) := hLN.trans_le hLL'
  have hd := log_succ_sub_le (k := N) (by omega)
  have hdec := TT_decomp N
  simp only [TT] at hdec
  -- (b)
  have hb : |LL (N + 1) - LL N| ≤ 1 / Real.log N := by
    obtain ⟨lb, ub⟩ := log_sub_bounds hLN hLL'
    have hlb : 0 ≤ 1 - Real.log N / Real.log (N + 1 : ℕ) := by
      rw [sub_nonneg, div_le_one hL'0]; exact hLL'
    have hN1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast (show 1 ≤ N by omega)
    have hub : Real.log (N + 1 : ℕ) / Real.log N - 1 ≤ 1 / Real.log N := by
      rw [div_sub_one hLN.ne']
      exact div_le_div_of_nonneg_right (hd.trans hN1) hLN.le
    simp only [LL]
    rw [abs_le]; constructor <;> linarith
  -- (c)
  have hc : |ww (N + 1) * PP N - 1| ≤ (E + 1) / Real.log N := by
    have e : ww (N + 1) * PP N - 1 = (PP N - Real.log (N + 1 : ℕ)) / Real.log (N + 1 : ℕ) := by
      simp only [ww]; field_simp
    rw [e, abs_div, abs_of_pos hL'0]
    have h1 : |PP N - Real.log (N + 1 : ℕ)| ≤ E + 1 := by
      have := hE' N (by omega)
      have hd0 : 0 ≤ Real.log (N + 1 : ℕ) - Real.log N := by linarith
      have hN1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast (show 1 ≤ N by omega)
      rw [abs_le] at this ⊢; constructor <;> linarith
    calc |PP N - Real.log (N + 1 : ℕ)| / Real.log (N + 1 : ℕ) ≤ (E + 1) / Real.log (N + 1 : ℕ) :=
          div_le_div_of_nonneg_right h1 hL'0.le
      _ ≤ (E + 1) / Real.log N :=
          div_le_div_of_nonneg_left ((abs_nonneg _).trans h1) hLN hLL'
  have ha := hD N hN
  have hsplit : ∑ p ∈ (Ioc 0 N).filter Nat.Prime, lam p ^ 2 / p - Real.log (Real.log N) - cMertens =
      -(∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k) + (LL (N + 1) - LL N) + (ww (N + 1) * PP N - 1) := by
    rw [cMertens]
    have : LL N = Real.log (Real.log N) := rfl
    linarith
  rw [hsplit]
  calc |-(∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k) + (LL (N + 1) - LL N) + (ww (N + 1) * PP N - 1)|
      ≤ |∑' k, hh k - ∑ k ∈ Ioc 0 N, hh k| + |LL (N + 1) - LL N| + |ww (N + 1) * PP N - 1| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
        rw [abs_neg]
    _ ≤ D / Real.log N + 1 / Real.log N + (E + 1) / Real.log N := by gcongr
    _ = (D + 1 + (E + 1)) / Real.log N := by ring

end

end RamanujanTau.SelbergCoeffs3
