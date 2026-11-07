/-
# The normalized Rankin–Selberg series `R(s) = ∑ τ(n)² n^{−11} n^{−s}`

From Rankin's theorem with error `O(N^{3/5})` (`RankinExact.rankinSelberg_exact`, unconditional):

* `rs_summable`: `R` converges absolutely on `Re s > 1`;
* `rs_sub_zeta_bound`: `‖R(s) − c·ζ(s)‖ ≤ K‖s‖/(Re s − 3/5)` on `Re s > 1` (Abel summation,
  Mathlib's `LSeries_eq_mul_integral`) — so `R` is bounded near every `1 + iu`, `u ≠ 0`, and
  `R(σ) = O(1/(σ−1))`;
* `rs_le_linear`: `τ(n)²/n¹¹ ≤ K n`;
* `rs_eulerProduct`: the Euler product `R(s) = ∏_p ∑_e τ(p^e)² p^{−11e} p^{−es}`.
-/
import RamanujanTau.RankinExact.Main

set_option autoImplicit false

namespace RamanujanTau.EdgeNonvanishing

open Complex Finset Filter Asymptotics MeasureTheory LSeries

/-- Normalized Rankin–Selberg coefficients `b(n) = τ(n)²/n¹¹`. -/
noncomputable def rsb (n : ℕ) : ℝ := ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11

/-- The complex coefficient sequence. -/
noncomputable def rsB (n : ℕ) : ℂ := (rsb n : ℂ)

/-- Rankin's constant `c = (3/π)(4π)¹²‖Δ‖²/11!`. -/
noncomputable def rsc : ℝ :=
  3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ)

/-- The Rankin–Selberg L-series `R(s)`. -/
noncomputable def RS (s : ℂ) : ℂ := LSeries rsB s

lemma rsb_nonneg (n : ℕ) : 0 ≤ rsb n := by unfold rsb; positivity

lemma rsb_zero : rsb 0 = 0 := by simp [rsb]

lemma rs_partial :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, rsb n - rsc * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC⟩ := RankinExact.rankinSelberg_exact
  refine ⟨C, ?_, fun N hN => by simpa [rsb, rsc] using hC N hN⟩
  have := hC 1 le_rfl
  simp at this
  exact (abs_nonneg _).trans this

lemma rs_partial_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, rsb n ≤ K * N := by
  obtain ⟨C, hC0, hC⟩ := rs_partial
  refine ⟨|rsc| + C, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := hC N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ ((3 : ℝ) / 5) ≤ N := by
    calc (N : ℝ) ^ ((3 : ℝ) / 5) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have h1 := (abs_le.mp h).2
  have h2 : rsc * N ≤ |rsc| * N := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  nlinarith

lemma rs_le_linear : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, rsb n ≤ K * n := by
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  refine ⟨K, hK0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rsb_zero]
  calc rsb n ≤ ∑ k ∈ Icc 1 n, rsb k :=
        single_le_sum (fun k _ => rsb_nonneg k) (mem_Icc.mpr ⟨hn, le_rfl⟩)
    _ ≤ K * n := hK n

lemma rs_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable rsB s := by
  obtain ⟨K, hK0, hK⟩ := rs_partial_le
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, rsb k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_of_nonneg (sum_nonneg fun k _ => rsb_nonneg k),
      Real.norm_of_nonneg (by positivity)]
    exact hK n
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO rsb_nonneg zero_le_one hs

/-- **Abel summation bound**: `‖R(s) − c ζ(s)‖ ≤ K‖s‖/(Re s − 3/5)` on `Re s > 1`. -/
theorem rs_sub_zeta_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 < s.re →
      ‖RS s - rsc * riemannZeta s‖ ≤ K * ‖s‖ / (s.re - 3 / 5) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial
  refine ⟨C, hC0, fun s hs => ?_⟩
  set f : ℕ → ℂ := fun n => rsB n - (rsc : ℂ)
  have hf1 : LSeriesSummable (fun _ : ℕ => (rsc : ℂ)) s := by
    have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
    have := h1.smul (rsc : ℂ)
    convert this using 1
    funext n; simp
  have hfS : LSeriesSummable f s := (rs_summable hs).sub hf1
  have hLf : LSeries f s = RS s - rsc * riemannZeta s := by
    have : f = rsB - (rsc : ℂ) • (1 : ℕ → ℂ) := by funext n; simp [f]
    rw [this, LSeries_sub (rs_summable hs), LSeries_smul, LSeries_one_eq_riemannZeta hs]
    · rfl
    · have := (LSeriesSummable_one_iff.mpr hs).smul (rsc : ℂ); exact this
  have hpart : ∀ N : ℕ, ‖∑ k ∈ Icc 1 N, f k‖ ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have : ∑ k ∈ Icc 1 N, f k = ((∑ n ∈ Icc 1 N, rsb n - rsc * N : ℝ) : ℂ) := by
      simp [f, rsB, sum_sub_distrib, mul_comm]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hC N hN
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 5) := by
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpart n
  have hs35 : (3 : ℝ) / 5 < s.re := by linarith
  rw [← hLf, LSeries_eq_mul_integral f (by norm_num) hs35 hfS hO, norm_mul]
  set a : ℝ := (3 : ℝ) / 5 - s.re - 1
  have ha : a < -1 := by simp only [a]; linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ a) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  have hbound : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), C * t ^ a := by
    refine norm_integral_le_of_norm_le hint ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 1 < t) => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have h1 : ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤ C * t ^ ((3 : ℝ) / 5) :=
      (hpart _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hfl (by norm_num)) hC0)
    have h2 : t ^ a = t ^ ((3 : ℝ) / 5) * t ^ (-(s + 1)).re := by
      rw [← Real.rpow_add ht0]; congr 1; simp [a]; ring
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hval : ∫ t in Set.Ioi (1 : ℝ), C * t ^ a = C / (s.re - 3 / 5) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]
    have : a + 1 = -(s.re - 3 / 5) := by simp only [a]; ring
    rw [this]; field_simp
  rw [hval] at hbound
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (C / (s.re - 3 / 5)) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = C * ‖s‖ / (s.re - 3 / 5) := by ring

lemma rsb_mul_coprime {m n : ℕ} (h : m.Coprime n) : rsb (m * n) = rsb m * rsb n := by
  simp only [rsb, tau_mul_coprime h]
  push_cast
  ring

/-- **Euler product** of `R(s)` on `Re s > 1`. -/
theorem rs_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e, term rsB s (p ^ e)) (RS s) := by
  have hf1 : term rsB s 1 = 1 := by
    simp [term_of_ne_zero, rsB, rsb, tau_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → term rsB s (m * n) = term rsB s m * term rsB s n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp
    rw [term_of_ne_zero (Nat.mul_ne_zero hm.ne' hn.ne'), term_of_ne_zero hm.ne',
      term_of_ne_zero hn.ne', rsB, rsb_mul_coprime hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
    simp only [rsB]; push_cast; field_simp
  have hsum : Summable (‖term rsB s ·‖) := summable_norm_iff.mpr (rs_summable hs)
  exact EulerProduct.eulerProduct_hasProd hf1 hmul hsum (term_zero _ _)

end RamanujanTau.EdgeNonvanishing
