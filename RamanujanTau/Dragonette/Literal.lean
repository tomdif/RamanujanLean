/-
# Dragonette's theorem in its original normalization

  `α(n) ~ (−1)^{n−1} e^{π√(n/6 − 1/144)} / (2√(n − 1/24))`.

From `Dragonette.dragonette_isEquivalent`, since `√(n/6) − √(n/6 − 1/144) → 0` and `√(n − 1/24)/√n → 1`.
-/
import RamanujanTau.Dragonette.Main

set_option autoImplicit false

namespace Dragonette
open Filter Asymptotics
open scoped Real Topology

lemma sqrt_diff_tendsto :
    Tendsto (fun n : ℕ => √((n : ℝ) / 6) - √((n : ℝ) / 6 - 1 / 144)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => √((n : ℝ) / 6)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num))
  have hb : Tendsto (fun n : ℕ => 1 / 144 / √((n : ℝ) / 6)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) / 6 - 1 / 144 ≤ n / 6 := by linarith
    linarith [Real.sqrt_le_sqrt this]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set a := √((n : ℝ) / 6)
    set b := √((n : ℝ) / 6 - 1 / 144)
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = n / 6 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = n / 6 - 1 / 144 := Real.sq_sqrt (by linarith)
    rw [le_div_iff₀ ha]
    have : (a - b) * (a + b) = 1 / 144 := by nlinarith
    nlinarith

lemma ratio_tendsto :
    Tendsto (fun n : ℕ => √((n : ℝ) - 1 / 24) / √(n : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / 24 / n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 / 24 : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using this.const_sub (1 : ℝ)
  have h2 := (Real.continuous_sqrt.tendsto 1).comp h
  rw [Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [← Real.sqrt_div' _ hn'.le]
  congr 1; field_simp

/-- **Dragonette's asymptotic, original form**. -/
theorem dragonette_literal :
    IsEquivalent atTop (fun n : ℕ => (α n : ℝ))
      (fun n : ℕ => (-1) ^ (n + 1) * Real.exp (π * √(n / 6 - 1 / 144)) / (2 * √((n : ℝ) - 1 / 24))) := by
  refine dragonette_isEquivalent.trans (isEquivalent_of_tendsto_one ?_)
  have h := ((Real.continuous_exp.tendsto 0).comp (by simpa using sqrt_diff_tendsto.const_mul π)).mul ratio_tendsto
  simp only [Real.exp_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < √((n : ℝ) - 1 / 24) := Real.sqrt_pos.mpr (by linarith)
  have hs : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hs0 : (-1 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [Function.comp, Pi.div_apply]
  rw [mul_sub, Real.exp_sub]
  field_simp
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 6), mul_div_assoc]
  ring
end Dragonette
