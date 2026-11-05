/-
# Rankin 1939: absolute convergence of `L(Δ,s)` for `Re s > 13/2`

From the unconditional Rankin–Selberg asymptotic
`(1/N) ∑_{n ≤ N} τ(n)²/n¹¹ → c` (`rankinSelberg_asymptotic_zagier_unconditional`) we get
`∑_{n ≤ N} τ(n)²/n¹¹ ≤ B N`, hence `∑_{n ≤ N} τ(n)² ≤ B N¹²`, and Cauchy–Schwarz gives
`∑_{n ≤ N} |τ(n)| ≤ √B N^{13/2}`. Mathlib's partial-summation criterion
`LSeriesSummable_of_sum_norm_bigO` then gives absolute convergence for `Re s > 13/2`.
-/
import RamanujanTau.EisensteinReal.HoroIdent
import RamanujanTau.HeckeL.Main

set_option autoImplicit false

namespace RamanujanTau.HeckeConvex

open Real Filter Topology Finset Asymptotics LSeries

/-- `∑_{n ≤ N} τ(n)²/n¹¹ ≤ B N` for all `N`. -/
lemma exists_sum_sq_div_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ B * N := by
  have h := RamanujanTau.EisensteinReal.rankinSelberg_asymptotic_zagier_unconditional
  obtain ⟨B, hB⟩ := h.bddAbove_range
  refine ⟨max B 0, le_max_right _ _, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have := hB ⟨N, rfl⟩
    rw [div_le_iff₀ hNpos] at this
    nlinarith [le_max_left B 0]

/-- `∑_{n ≤ N} τ(n)² ≤ B N¹²`. -/
lemma sum_sq_le {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ B * N) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 ≤ B * (N : ℝ) ^ 12 := by
  have hterm : ∀ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 ≤
      ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 * (N : ℝ) ^ 11 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0.le hnN 11) (sq_nonneg _)
  calc ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2
      ≤ ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 * (N : ℝ) ^ 11 := sum_le_sum hterm
    _ = (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) * (N : ℝ) ^ 11 := by
        rw [Finset.sum_mul]
    _ ≤ (B * N) * (N : ℝ) ^ 11 := by gcongr; exact hB N
    _ = B * (N : ℝ) ^ 12 := by ring

/-- **Rankin's mean bound** `∑_{n ≤ N} |τ(n)| ≤ √B N^{13/2}`. -/
theorem exists_sum_abs_tau_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, |(tau n : ℝ)| ≤ A * (N : ℝ) ^ (13 / 2 : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := exists_sum_sq_div_le
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun N => ?_⟩
  have hcs := sq_sum_le_card_mul_sum_sq (s := Icc 1 N) (f := fun n => |(tau n : ℝ)|)
  simp only [sq_abs, Nat.card_Icc, add_tsub_cancel_right] at hcs
  have h2 := sum_sq_le hB N
  have hsq : (∑ n ∈ Icc 1 N, |(tau n : ℝ)|) ^ 2 ≤ B * (N : ℝ) ^ 13 := by
    calc _ ≤ (N : ℝ) * ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 := hcs
      _ ≤ (N : ℝ) * (B * (N : ℝ) ^ 12) := by gcongr
      _ = B * (N : ℝ) ^ 13 := by ring
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, |(tau n : ℝ)| := sum_nonneg fun _ _ => abs_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrpow : ((N : ℝ) ^ (13 / 2 : ℝ)) ^ 2 = (N : ℝ) ^ 13 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hrhs : (Real.sqrt B * (N : ℝ) ^ (13 / 2 : ℝ)) ^ 2 = B * (N : ℝ) ^ 13 := by
    rw [mul_pow, Real.sq_sqrt hB0, hrpow]
  have hR0 : 0 ≤ Real.sqrt B * (N : ℝ) ^ (13 / 2 : ℝ) := by positivity
  rw [← hrhs] at hsq
  exact (pow_le_pow_iff_left₀ hS0 hR0 (by norm_num)).1 hsq

/-- **Rankin 1939**: `∑ τ(n) n^{−s}` converges absolutely for `Re s > 13/2`. -/
theorem LSeriesSummable_tau_of_gt_13_2 {s : ℂ} (hs : 13 / 2 < s.re) :
    LSeriesSummable tauC s := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_abs_tau_le
  refine LSeriesSummable_of_sum_norm_bigO (r := 13 / 2) ?_ (by norm_num) hs
  refine IsBigO.of_bound A (Eventually.of_forall fun N => ?_)
  have e : ∀ n, ‖tauC n‖ = |(tau n : ℝ)| := fun n => by
    simp [tauC, Complex.norm_intCast]
  simp_rw [e]
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => abs_nonneg _),
    Real.norm_of_nonneg (by positivity)]
  exact hA N

/-- The real form: `∑ |τ(n)| n^{−σ} < ∞` for every real `σ > 13/2`. -/
theorem summable_abs_tau_div_rpow {σ : ℝ} (hσ : 13 / 2 < σ) :
    Summable fun n : ℕ => |(tau n : ℝ)| / (n : ℝ) ^ σ := by
  have h := (LSeriesSummable_tau_of_gt_13_2 (s := (σ : ℂ)) (by simpa using hσ)).norm
  refine h.congr fun n => ?_
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tau_zero]
  · rw [if_neg hn]; simp [tauC, Complex.norm_intCast]

end RamanujanTau.HeckeConvex
