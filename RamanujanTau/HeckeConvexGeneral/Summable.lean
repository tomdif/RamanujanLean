/-
# Rankin's mean bound and absolute convergence of `L(f,s)` for every level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `k ≥ 1`, with q-expansion coefficients `a(n)`, the Rankin–Selberg
asymptotic `(1/N) ∑_{n ≤ N} |a(n)|²/n^{k−1} → c_f`
(`RankinSelbergGeneral.rankinSelberg_asymptotic`) gives `∑_{n ≤ N} |a(n)|² ≤ B N^k`, hence by
Cauchy–Schwarz `∑_{n ≤ N} |a(n)| ≤ √B N^{(k+1)/2}`, and partial summation gives absolute
convergence of `L(f,s) = ∑ a(n) n^{−s}` for `Re s > (k+1)/2`.

Generalizes `HeckeConvex/Summable.lean` (`f = Δ`, `k = 12`).
-/
import RamanujanTau.RankinSelbergGeneral.Cusp

set_option autoImplicit false

namespace RamanujanTau.HeckeConvexGeneral

open Real Filter Topology Finset Asymptotics LSeries
open Complex ModularForm
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- The `n`-th q-expansion coefficient `a_f(n)` of a level-one cusp form. -/
noncomputable def coef (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

lemma coef_zero (f : CuspForm 𝒮ℒ (k : ℤ)) : coef f 0 = 0 := coeff_zero_eq_zero f

lemma coeffSq_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : coeffSq f n = ‖coef f n‖ ^ 2 := rfl

/-- `∑_{n ≤ N} |a(n)|²/n^{k−1} ≤ B N` for all `N`. -/
lemma exists_sum_sq_div_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) ≤ B * N := by
  have h := rankinSelberg_asymptotic f hk
  obtain ⟨B, hB⟩ := h.bddAbove_range
  refine ⟨max B 0, le_max_right _ _, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have := hB ⟨N, rfl⟩
    simp only [coeffSq_eq] at this
    rw [div_le_iff₀ hNpos] at this
    nlinarith [le_max_left B 0]

/-- `∑_{n ≤ N} |a(n)|² ≤ B N^k`. -/
lemma sum_sq_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) ≤ B * N) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 ≤ B * (N : ℝ) ^ k := by
  have hterm : ∀ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 ≤
      ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) * (N : ℝ) ^ (k - 1) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0.le hnN _) (sq_nonneg _)
  have hk' : (N : ℝ) * (N : ℝ) ^ (k - 1) = (N : ℝ) ^ k := by
    rw [← pow_succ']; congr 1; omega
  calc ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2
      ≤ ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) * (N : ℝ) ^ (k - 1) := sum_le_sum hterm
    _ = (∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1)) * (N : ℝ) ^ (k - 1) := by
        rw [Finset.sum_mul]
    _ ≤ (B * N) * (N : ℝ) ^ (k - 1) := by gcongr; exact hB N
    _ = B * (N : ℝ) ^ k := by rw [← hk']; ring

/-- **Rankin's mean bound** `∑_{n ≤ N} |a_f(n)| ≤ A N^{(k+1)/2}`. -/
theorem exists_sum_norm_coef_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ∑ n ∈ Icc 1 N, ‖coef f n‖ ≤ A * (N : ℝ) ^ (((k : ℝ) + 1) / 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_sum_sq_div_le f hk
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun N => ?_⟩
  have hcs := sq_sum_le_card_mul_sum_sq (s := Icc 1 N) (f := fun n => ‖coef f n‖)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hcs
  have h2 := sum_sq_le f hk hB N
  have hsq : (∑ n ∈ Icc 1 N, ‖coef f n‖) ^ 2 ≤ B * (N : ℝ) ^ (k + 1) := by
    calc _ ≤ (N : ℝ) * ∑ n ∈ Icc 1 N, ‖coef f n‖ ^ 2 := hcs
      _ ≤ (N : ℝ) * (B * (N : ℝ) ^ k) := by gcongr
      _ = B * (N : ℝ) ^ (k + 1) := by ring
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, ‖coef f n‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrpow : ((N : ℝ) ^ (((k : ℝ) + 1) / 2)) ^ 2 = (N : ℝ) ^ (k + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hrhs : (Real.sqrt B * (N : ℝ) ^ (((k : ℝ) + 1) / 2)) ^ 2 = B * (N : ℝ) ^ (k + 1) := by
    rw [mul_pow, Real.sq_sqrt hB0, hrpow]
  have hR0 : 0 ≤ Real.sqrt B * (N : ℝ) ^ (((k : ℝ) + 1) / 2) := by positivity
  rw [← hrhs] at hsq
  exact (pow_le_pow_iff_left₀ hS0 hR0 (by norm_num)).1 hsq

/-- **Absolute convergence**: `∑ a_f(n) n^{−s}` converges absolutely for `Re s > (k+1)/2`. -/
theorem LSeriesSummable_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ}
    (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable (coef f) s := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_norm_coef_le f hk
  refine LSeriesSummable_of_sum_norm_bigO (r := ((k : ℝ) + 1) / 2) ?_ (by positivity) hs
  refine IsBigO.of_bound A (Eventually.of_forall fun N => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (by positivity)]
  exact hA N

/-- The real form: `∑ |a_f(n)| n^{−σ} < ∞` for every real `σ > (k+1)/2`. -/
theorem summable_norm_coef_div_rpow (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {σ : ℝ}
    (hσ : ((k : ℝ) + 1) / 2 < σ) :
    Summable fun n : ℕ => ‖coef f n‖ / (n : ℝ) ^ σ := by
  have h := (LSeriesSummable_coef f hk (s := (σ : ℂ)) (by simpa using hσ)).norm
  refine h.congr fun n => ?_
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coef_zero]
  · rw [if_neg hn]; simp

end RamanujanTau.HeckeConvexGeneral
