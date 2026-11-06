/-
# Coefficient data for the general truncated Voronoi formula

The whole development of `VoronoiTruncGeneral` is carried out for a real sequence `a : ℕ → ℝ`
and a weight `k = 2m` satisfying the three properties bundled in `VData m a`:

* `a 0 = 0`;
* the modular relation `D(z) = (−1)^m z^{−2m} D(1/z)` for `Re z > 0`, `D(z) = Σ a(n) e^{−2πnz}`
  (for a cusp form `f` of weight `k = 2m`: `D(z) = f(iz)` and `(iz)^{−k} = (−1)^m z^{−k}`);
* Rankin's mean bound `Σ_{n≤N} a(n)² ≤ B N^{2m}`.

`Cusp.lean` proves `VData` for every level-one cusp form with real coefficients.  This file
derives the consequences that the analytic part uses:
`|a(n)| ≤ A n^{m+1}`, `Σ_{n≤N}|a(n)| ≤ A N^{m+1/2}`, `Σ |a(n)| n^{−β} < ∞` (`β > m+1/2`) and
`Σ a(n)² n^{−β} < ∞` (`β > 2m`).
-/
import RamanujanTau.VoronoiTrunc.Avg

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real Filter Topology Finset Asymptotics LSeries

/-- `D(z) = Σ a(n) e^{−2πnz}`. -/
noncomputable def Dq (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, (a n : ℂ) * cexp (-2 * π * n * z)

/-- The hypotheses on the coefficients (weight `k = 2m`). -/
structure VData (m : ℕ) (a : ℕ → ℝ) : Prop where
  two_le : 2 ≤ m
  zero : a 0 = 0
  modular : ∀ z : ℂ, 0 < z.re → Dq a z = (-1 : ℂ) ^ m * ((z ^ (2 * m))⁻¹ * Dq a z⁻¹)
  rankin : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ^ 2 ≤ B * (N : ℝ) ^ (2 * m)

variable {m : ℕ} {a : ℕ → ℝ}

theorem VData.one_le (hd : VData m a) : 1 ≤ m := le_trans (by norm_num) hd.two_le

/-- `Σ_{n≤N} |a(n)| ≤ A N^{m+1/2}` (Cauchy–Schwarz). -/
theorem VData.sum_abs_le (hd : VData m a) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, |a n| ≤ A * (N : ℝ) ^ ((m : ℝ) + 1 / 2) := by
  obtain ⟨B, hB0, hB⟩ := hd.rankin
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun N => ?_⟩
  have hcs := sq_sum_le_card_mul_sum_sq (s := Icc 1 N) (f := fun n => |a n|)
  simp only [Nat.card_Icc, add_tsub_cancel_right, sq_abs] at hcs
  have hsq : (∑ n ∈ Icc 1 N, |a n|) ^ 2 ≤ B * (N : ℝ) ^ (2 * m + 1) := by
    calc _ ≤ (N : ℝ) * ∑ n ∈ Icc 1 N, a n ^ 2 := hcs
      _ ≤ (N : ℝ) * (B * (N : ℝ) ^ (2 * m)) := by gcongr; exact hB N
      _ = B * (N : ℝ) ^ (2 * m + 1) := by ring
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, |a n| := sum_nonneg fun _ _ => abs_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrpow : ((N : ℝ) ^ ((m : ℝ) + 1 / 2)) ^ 2 = (N : ℝ) ^ (2 * m + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hrhs : (Real.sqrt B * (N : ℝ) ^ ((m : ℝ) + 1 / 2)) ^ 2 = B * (N : ℝ) ^ (2 * m + 1) := by
    rw [mul_pow, Real.sq_sqrt hB0, hrpow]
  have hR0 : 0 ≤ Real.sqrt B * (N : ℝ) ^ ((m : ℝ) + 1 / 2) := by positivity
  rw [← hrhs] at hsq
  exact (pow_le_pow_iff_left₀ hS0 hR0 (by norm_num)).1 hsq

/-- `|a(n)| ≤ A n^{m+1}`. -/
theorem VData.abs_le (hd : VData m a) : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, |a n| ≤ A * (n : ℝ) ^ (m + 1) := by
  obtain ⟨A, hA0, hA⟩ := hd.sum_abs_le
  refine ⟨A, hA0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hd.zero]
  · have h1 : |a n| ≤ ∑ k ∈ Icc 1 n, |a k| :=
      single_le_sum (f := fun k => |a k|) (fun _ _ => abs_nonneg _) (mem_Icc.2 ⟨hn, le_rfl⟩)
    have h2 : (n : ℝ) ^ ((m : ℝ) + 1 / 2) ≤ (n : ℝ) ^ (m + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by push_cast; linarith)
    calc |a n| ≤ A * (n : ℝ) ^ ((m : ℝ) + 1 / 2) := h1.trans (hA n)
      _ ≤ A * (n : ℝ) ^ (m + 1) := by gcongr

/-- `Σ |a(n)| n^{−β} < ∞` for `β > m + 1/2`. -/
theorem VData.summable_abs_div (hd : VData m a) {β : ℝ} (hβ : (m : ℝ) + 1 / 2 < β) :
    Summable fun n : ℕ => |a n| / (n : ℝ) ^ β := by
  obtain ⟨A, hA0, hA⟩ := hd.sum_abs_le
  set f : ℕ → ℂ := fun n => (a n : ℂ)
  have hf : ∀ n, ‖f n‖ = |a n| := fun n => by simp only [f, Complex.norm_real, Real.norm_eq_abs]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n => (n : ℝ) ^ ((m : ℝ) + 1 / 2) := by
    refine IsBigO.of_bound A (Eventually.of_forall fun N => ?_)
    simp_rw [hf]
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => abs_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    exact hA N
  have hL : LSeriesSummable f (β : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO hO (by positivity) (by simpa using hβ)
  refine hL.norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [f, hd.zero]
  · rw [LSeries.norm_term_eq, if_neg hn.ne', hf, Complex.ofReal_re]

/-- `Σ a(n)² n^{−β} < ∞` for `β > 2m`. -/
theorem VData.summable_sq (hd : VData m a) {β : ℝ} (hβ : 2 * (m : ℝ) < β) :
    Summable fun n : ℕ => a n ^ 2 * (n : ℝ) ^ (-β) := by
  obtain ⟨B, hB0, hB⟩ := hd.rankin
  set f : ℕ → ℂ := fun n => ((a n ^ 2 : ℝ) : ℂ)
  have hf : ∀ n, ‖f n‖ = a n ^ 2 := fun n => by
    simp only [f, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n => (n : ℝ) ^ (2 * (m : ℝ)) := by
    refine IsBigO.of_bound B (Eventually.of_forall fun N => ?_)
    simp_rw [hf]
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    rw [show (N : ℝ) ^ (2 * (m : ℝ)) = (N : ℝ) ^ (2 * m) by
      rw [← Real.rpow_natCast]; push_cast; ring_nf]
    exact hB N
  have hL : LSeriesSummable f (β : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO hO (by positivity) (by simpa using hβ)
  refine hL.norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [f, hd.zero]
  · rw [LSeries.norm_term_eq, if_neg hn.ne', hf, Complex.ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Scaling: `VData` is preserved by `a ↦ c·a`. -/
theorem VData.smul (hd : VData m a) (c : ℝ) : VData m (fun n => c * a n) where
  two_le := hd.two_le
  zero := by simp [hd.zero]
  modular := by
    intro z hz
    have hs : ∀ w : ℂ, Dq (fun n => c * a n) w = (c : ℂ) * Dq a w := by
      intro w; unfold Dq; rw [← tsum_mul_left]; congr 1; funext n; push_cast; ring
    rw [hs, hs, hd.modular z hz]; ring
  rankin := by
    obtain ⟨B, hB0, hB⟩ := hd.rankin
    refine ⟨c ^ 2 * B, by positivity, fun N => ?_⟩
    have : ∑ n ∈ Icc 1 N, (c * a n) ^ 2 = c ^ 2 * ∑ n ∈ Icc 1 N, a n ^ 2 := by
      rw [mul_sum]; refine sum_congr rfl fun n _ => by ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB N) (sq_nonneg c)

end RamanujanTau.VoronoiTruncGeneral
