/-
# Selberg–Delange for the coefficients of `R(s)^{−1/2}` (unconditional)

`fR = recF (−ΛR/2)`: `fR(1) = 1`, `fR · log = (−ΛR/2) ∗ fR`, i.e. the coefficients of
`R(s)^{−1/2}`, `R(s) = Σ λ(n)² n^{−s}`; `fR(p) = −λ(p)²/2` (`fR_prime`).

**Theorem** (`logmean_fR`).  There are `C₁, K₁, X₀, c₀` with, for `x ≥ X₀`,

  `|Σ_{n≤x} fR(n)/n − C₁ (log x − c₀)^{−1/2}| ≤ K₁ (1 + log(1+log x)) (log x)^{−3/2}`.

Inputs: `mertens_LamR_err` (`Σ_{m≤y} ΛR(m)/m = log y + c + O(1/log y)`, from `psiR_error`);
the density bound `Σ_{n≤y} |fR(n)| ≪ y (log y)^{−1/2}` via the majorant `recF |ΛR|/2`
(`density_nonneg`, with Chebyshev `cheb_LamR` and Mertens for `|ΛR|`).  No Deligne.
-/
import RamanujanTau.SelbergDelange3.MertensErr
import RamanujanTau.SelbergDelange3.Coeff
import RamanujanTau.SelbergDelange3.Density
import RamanujanTau.SelbergDelange2.LSD

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset Filter Topology ArithmeticFunction
open RamanujanTau.TauPNTUncond (vR vR_nonneg)
open RamanujanTau.SelbergCoeffs2 (LamR sqL sqL_nonneg sqL_sq sqL_zero_of_not LamR_zero)
open RamanujanTau.SelbergDelange2 (Ssum Msum Err logmean_LSD)
open scoped ArithmeticFunction.vonMangoldt

lemma sum_range_succ_Ioc (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 1), g k = g 0 + ∑ n ∈ Ioc 0 N, g n := by
  rw [sum_range_succ', sum_Ioc_eq_range, add_comm]

lemma summable_sqL_78 : Summable fun n : ℕ => sqL n * (n : ℝ) ^ (-(7 / 8 : ℝ)) := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective two_ne_zero
  refine (hinj.summable_iff (f := fun n : ℕ => sqL n * (n : ℝ) ^ (-(7 / 8 : ℝ))) (fun n hn => by
    simp [sqL_zero_of_not hn])).mp ?_
  have hs : Summable fun m : ℕ => 2 * (m : ℝ) ^ (-(5 / 4 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sqL_nonneg _) (by positivity))
    (fun m => ?_) hs
  simp only [Function.comp_apply, sqL_sq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : vonMangoldt m ≤ 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 : (m : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (m : ℝ) ^ (1 / 2 : ℝ) := by ring
    linarith [ArithmeticFunction.vonMangoldt_le_log (n := m)]
  have hm2 : ((m ^ 2 : ℕ) : ℝ) ^ (-(7 / 8 : ℝ)) = (m : ℝ) ^ (-(7 / 4 : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  rw [hm2]
  have hp : 0 ≤ (m : ℝ) ^ (-(7 / 4 : ℝ)) := by positivity
  calc vonMangoldt m * (m : ℝ) ^ (-(7 / 4 : ℝ)) ≤ 2 * (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (-(7 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hl hp
    _ = 2 * (m : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hm0]; norm_num

lemma summable_sqL_div' : Summable fun n : ℕ => sqL n / n := SelbergCoeffs2.summable_sqL_div

/-- The tail of `Σ sqL(n)/n`. -/
lemma sqL_tail : ∃ S S78 : ℝ, 0 ≤ S78 ∧ ∀ N : ℕ, 1 ≤ N →
    0 ≤ S - ∑ n ∈ Ioc 0 N, sqL n / n ∧
      S - ∑ n ∈ Ioc 0 N, sqL n / n ≤ S78 * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  set f : ℕ → ℝ := fun n => sqL n / n with hf
  set h : ℕ → ℝ := fun n => sqL n * (n : ℝ) ^ (-(7 / 8 : ℝ)) with hh
  have hfs : Summable f := summable_sqL_div'
  have hhs : Summable h := summable_sqL_78
  have hf0 : ∀ n, 0 ≤ f n := fun n => div_nonneg (sqL_nonneg n) (Nat.cast_nonneg n)
  have hh0 : ∀ n, 0 ≤ h n := fun n => mul_nonneg (sqL_nonneg n) (by positivity)
  refine ⟨∑' n, f n, ∑' n, h n, tsum_nonneg hh0, fun N hN => ?_⟩
  have hsplit := hfs.sum_add_tsum_nat_add (N + 1)
  rw [sum_range_succ_Ioc] at hsplit
  have hf00 : f 0 = 0 := by simp [hf]
  rw [hf00, zero_add] at hsplit
  have htail : ∑' n, f n - ∑ n ∈ Ioc 0 N, sqL n / n = ∑' k, f (k + (N + 1)) := by
    rw [← hsplit]; simp [hf]
  rw [htail]
  have hft : Summable fun k => f (k + (N + 1)) := (summable_nat_add_iff (N + 1)).mpr hfs
  have hht : Summable fun k => h (k + (N + 1)) := (summable_nat_add_iff (N + 1)).mpr hhs
  refine ⟨tsum_nonneg fun k => hf0 _, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ k, f (k + (N + 1)) ≤ (N : ℝ) ^ (-(1 / 8 : ℝ)) * h (k + (N + 1)) := by
    intro k
    set m : ℕ := k + (N + 1)
    have hm0 : (0 : ℝ) < m := by positivity
    have hmN : (N : ℝ) ≤ m := by simp only [m]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hf, hh]
    have e : sqL m / m = sqL m * (m : ℝ) ^ (-(7 / 8 : ℝ)) * (m : ℝ) ^ (-(1 / 8 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hm0]; norm_num; rw [Real.rpow_neg_one]; ring
    rw [e]
    have h1 : (m : ℝ) ^ (-(1 / 8 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hmN (by norm_num)
    have h2 : 0 ≤ sqL m * (m : ℝ) ^ (-(7 / 8 : ℝ)) := mul_nonneg (sqL_nonneg m) (by positivity)
    nlinarith
  have hle : ∑' k, f (k + (N + 1)) ≤ ∑' k, (N : ℝ) ^ (-(1 / 8 : ℝ)) * h (k + (N + 1)) :=
    hft.tsum_le_tsum hpt (hht.mul_left _)
  rw [tsum_mul_left] at hle
  have htl : ∑' k, h (k + (N + 1)) ≤ ∑' n, h n := by
    have := hhs.sum_add_tsum_nat_add (N + 1)
    have : 0 ≤ ∑ k ∈ range (N + 1), h k := sum_nonneg fun k _ => hh0 k
    linarith
  have : 0 ≤ (N : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
  nlinarith

/-- `N^{−1/8} ≤ 9/(1 + log N)`. -/
lemma rpow_neg_eighth_le {N : ℝ} (hN : 1 ≤ N) : N ^ (-(1 / 8 : ℝ)) ≤ 9 / (1 + Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hl := Real.log_le_rpow_div hN0.le (ε := 1 / 8) (by norm_num)
  have hl0 := Real.log_nonneg hN
  rw [le_div_iff₀ (by linarith)]
  have hp : 0 < N ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hp1 : N ^ (-(1 / 8 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have e : N ^ (-(1 / 8 : ℝ)) * N ^ (1 / 8 : ℝ) = 1 := by
    rw [← Real.rpow_add hN0]; norm_num
  have : N ^ (-(1 / 8 : ℝ)) * Real.log N ≤ 8 := by
    calc N ^ (-(1 / 8 : ℝ)) * Real.log N ≤ N ^ (-(1 / 8 : ℝ)) * (N ^ (1 / 8 : ℝ) / (1 / 8)) :=
          mul_le_mul_of_nonneg_left hl hp.le
      _ = (N ^ (-(1 / 8 : ℝ)) * N ^ (1 / 8 : ℝ)) * 8 := by ring
      _ = 8 := by rw [e]; norm_num
  nlinarith

lemma one_div_floor_le {y : ℝ} (hy : 1 ≤ y) : 1 / (⌊y⌋₊ : ℝ) ≤ 2 / (1 + Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hN1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_floor_iff y |>.2 hy
  have hlt : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  rw [div_le_div_iff₀ (by linarith) (by have := Real.log_nonneg hy; linarith)]
  have := Real.log_le_sub_one_of_pos hy0
  linarith

lemma log_floor_close {y : ℝ} (hy : 1 ≤ y) :
    |Real.log y - Real.log (⌊y⌋₊ : ℝ)| ≤ 2 / (1 + Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hN1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_floor_iff y |>.2 hy
  have hN0 : (0 : ℝ) < ⌊y⌋₊ := by linarith
  have hNy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  have hlt : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have h1 : 0 ≤ Real.log y - Real.log (⌊y⌋₊ : ℝ) := by
    have := Real.log_le_log hN0 hNy; linarith
  have h2 : Real.log y - Real.log (⌊y⌋₊ : ℝ) ≤ 1 / (⌊y⌋₊ : ℝ) := by
    rw [← Real.log_div hy0.ne' hN0.ne']
    have := Real.log_le_sub_one_of_pos (x := y / ⌊y⌋₊) (by positivity)
    have e : y / ⌊y⌋₊ - 1 ≤ 1 / (⌊y⌋₊ : ℝ) := by
      rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  rw [abs_of_nonneg h1]
  exact h2.trans (one_div_floor_le hy)

lemma log_le_floor_bound {y : ℝ} (hy : 1 ≤ y) :
    1 + Real.log y ≤ 2 * (1 + Real.log (⌊y⌋₊ : ℝ)) := by
  have hy0 : 0 < y := by linarith
  have hN1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_floor_iff y |>.2 hy
  have hlt : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have h1 : Real.log y ≤ Real.log (2 * ⌊y⌋₊) := Real.log_le_log hy0 (by linarith)
  rw [Real.log_mul (by norm_num) (by linarith)] at h1
  have := Real.log_two_lt_d9
  have := Real.log_nonneg hN1
  linarith

/-- **Mertens for `ΛR` with error `O(1/log y)`.** -/
theorem mertens_LamR_err : ∃ c B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 1 ≤ y →
    |Msum LamR y - Real.log y - c| ≤ B / (1 + Real.log y) := by
  obtain ⟨cv, Bv, hBv, hv⟩ := mertens_vR_err
  obtain ⟨S, S78, hS78, hS⟩ := sqL_tail
  refine ⟨cv - 2 * S, 4 * Bv + 36 * S78 + 2, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set N := ⌊y⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff y |>.2 hy
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hsplit : Msum LamR y = ∑ n ∈ Ioc 0 N, vR n / n - 2 * ∑ n ∈ Ioc 0 N, sqL n / n := by
    rw [Msum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [LamR]; ring
  have h1 := hv N hN1
  obtain ⟨h2a, h2b⟩ := hS N hN1
  have h3 := log_floor_close hy
  have h4 := log_le_floor_bound hy
  have h5 := rpow_neg_eighth_le hN1r
  have hl0 : 0 < 1 + Real.log y := by have := Real.log_nonneg hy; linarith
  have hlN : 0 < 1 + Real.log N := by have := Real.log_nonneg hN1r; linarith
  have hBN : Bv / (1 + Real.log N) ≤ 2 * Bv / (1 + Real.log y) := by
    rw [div_le_div_iff₀ hlN hl0]; nlinarith
  have h9 : 9 / (1 + Real.log N) ≤ 18 / (1 + Real.log y) := by
    rw [div_le_div_iff₀ hlN hl0]; nlinarith
  have hsq : S - ∑ n ∈ Ioc 0 N, sqL n / n ≤ S78 * (18 / (1 + Real.log y)) := by
    refine h2b.trans ?_
    exact mul_le_mul_of_nonneg_left (h5.trans h9) hS78
  rw [hsplit]
  have e : ∑ n ∈ Ioc 0 N, vR n / n - 2 * ∑ n ∈ Ioc 0 N, sqL n / n - Real.log y - (cv - 2 * S) =
      (∑ n ∈ Ioc 0 N, vR n / n - Real.log N - cv) + 2 * (S - ∑ n ∈ Ioc 0 N, sqL n / n) +
        (Real.log N - Real.log y) := by ring
  rw [e]
  have hfin : (4 * Bv + 36 * S78 + 2) / (1 + Real.log y) =
      2 * Bv / (1 + Real.log y) + 2 * (S78 * (18 / (1 + Real.log y))) + 2 / (1 + Real.log y) +
        2 * Bv / (1 + Real.log y) := by ring
  rw [hfin]
  have hB2 : 0 ≤ 2 * Bv / (1 + Real.log y) := by positivity
  rw [abs_sub_comm] at h3
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * (S - ∑ n ∈ Ioc 0 N, sqL n / n))]
  linarith [h1.trans hBN]

/-! ### The coefficients of `R^{−1/2}` -/

/-- `Λ_f = −ΛR/2`. -/
noncomputable def gR (n : ℕ) : ℝ := -(LamR n) / 2

lemma gR_zero : gR 0 = 0 := by simp [gR, LamR_zero]

lemma LamR_one : LamR 1 = 0 := by
  have h1 : vR 1 = 0 := TauPNTUncond.vR_of_not not_isPrimePow_one
  simp [LamR, h1, sqL]

lemma gR_one : gR 1 = 0 := by simp [gR, LamR_one]

/-- **The coefficients of `R(s)^{−1/2}`.** -/
noncomputable def fR : ℕ → ℝ := recF gR

lemma fR_one : fR 1 = 1 := recF_one gR

lemma fR_prime {p : ℕ} (hp : p.Prime) : fR p = -(RamanujanTau.EdgeNonvanishing.lam p) ^ 2 / 2 := by
  rw [fR, recF_eq, if_neg hp.ne_zero, if_neg hp.one_lt.ne', Nat.Prime.properDivisors hp]
  simp only [sum_singleton, Nat.div_one, recF_one, mul_one]
  rw [gR, SelbergCoeffs2.LamR_prime hp]
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  field_simp

lemma fR_log (n : ℕ) (hn : 0 < n) :
    recFA gR n * Real.log n = (toA gR gR_zero * recFA gR) n :=
  recF_log gR gR_zero gR_one n hn

/-- Mertens upper bound for `|gR| = |ΛR|/2`. -/
lemma mertens_abs_gR : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℝ, 1 ≤ z →
    Msum (fun m => |gR m|) z ≤ 1 / 2 * Real.log z + A := by
  obtain ⟨cv, Bv, hBv, hv⟩ := mertens_vR_err
  obtain ⟨S, S78, hS78, hS⟩ := sqL_tail
  refine ⟨max 0 ((|cv| + Bv) / 2 + |S|), le_max_left _ _, fun z hz => ?_⟩
  have hz0 : 0 < z := by linarith
  set N := ⌊z⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff z |>.2 hz
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpt : ∀ n ∈ Ioc 0 N, |gR n| / n ≤ (1 / 2) * (vR n / n) + sqL n / n := by
    intro n _
    have := SelbergCoeffs2.abs_LamR_le n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [gR, abs_div, abs_neg, abs_two]
    rw [div_div, show (2 : ℝ) * n = n * 2 by ring, ← div_div]
    have : |LamR n| / n ≤ (vR n + 2 * sqL n) / n := div_le_div_of_nonneg_right this hn
    have e : (vR n + 2 * sqL n) / n / 2 = 1 / 2 * (vR n / n) + sqL n / n := by ring
    linarith [div_le_div_of_nonneg_right this (show (0:ℝ) ≤ 2 by norm_num)]
  have h1 := sum_le_sum hpt
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 := hv N hN1
  have hlN : 0 < 1 + Real.log N := by have := Real.log_nonneg hN1r; linarith
  have h2' : ∑ n ∈ Ioc 0 N, vR n / n ≤ Real.log N + cv + Bv := by
    rw [abs_le] at h2
    have : Bv / (1 + Real.log N) ≤ Bv := div_le_self hBv (by have := Real.log_nonneg hN1r; linarith)
    linarith
  obtain ⟨h3a, _⟩ := hS N hN1
  have hlog : Real.log N ≤ Real.log z := Real.log_le_log (by linarith) (Nat.floor_le hz0.le)
  have : Msum (fun m => |gR m|) z = ∑ n ∈ Ioc 0 N, |gR n| / n := rfl
  rw [this]
  have hc := le_abs_self cv
  have hs := le_abs_self S
  have hm := le_max_right 0 ((|cv| + Bv) / 2 + |S|)
  linarith

lemma cheb_abs_gR : ∃ A₂ : ℝ, 0 ≤ A₂ ∧ ∀ z : ℝ, 1 ≤ z →
    ∑ d ∈ Ioc 0 ⌊z⌋₊, |gR d| ≤ A₂ * z := by
  obtain ⟨B, hB0, hB⟩ := SelbergCoeffs2.cheb_LamR
  refine ⟨B / 2, by positivity, fun z hz => ?_⟩
  have h := hB ⌊z⌋₊
  have hNz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have e : ∑ d ∈ Ioc 0 ⌊z⌋₊, |gR d| = (∑ d ∈ Ioc 0 ⌊z⌋₊, |LamR d|) / 2 := by
    rw [sum_div]; refine sum_congr rfl fun d _ => ?_
    rw [gR, abs_div, abs_neg, abs_two]
  rw [e]
  have : B * ⌊z⌋₊ ≤ B * z := mul_le_mul_of_nonneg_left hNz hB0
  linarith

/-- Density bound for `|fR|`. -/
lemma density_fR : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
    ∑ n ∈ Ioc 0 ⌊y⌋₊, |fR n| ≤ K * y * (1 + Real.log y) ^ ((1 / 2 : ℝ) - 1) := by
  set ga : ℕ → ℝ := fun m => |gR m| with hga
  have ha0 : ga 0 = 0 := by simp [hga, gR_zero]
  have ha1 : ga 1 = 0 := by simp [hga, gR_one]
  obtain ⟨A, hA, hMu⟩ := mertens_abs_gR
  obtain ⟨A₂, hA2, hCh⟩ := cheb_abs_gR
  have hF0 : ∀ n, 0 ≤ recFA ga n := fun n => (abs_recF_le gR n).1
  have hG0 : ∀ n, 0 ≤ toA ga ha0 n := fun n => abs_nonneg _
  obtain ⟨K, hK, hD⟩ := density_nonneg (recFA ga) (toA ga ha0) hF0 hG0
    (recF_log ga ha0 ha1) (σ := 1 / 2) (by norm_num) (by norm_num) hA hMu hCh
  refine ⟨K, hK, fun y hy => ?_⟩
  refine (sum_le_sum fun n _ => (abs_recF_le gR n).2).trans ?_
  exact hD y hy

/-- **Selberg–Delange for the coefficients of `R(s)^{−1/2}`** (unconditional). -/
theorem logmean_fR : ∃ C₁ K₁ X₀ c₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
    |Ssum fR x - C₁ * (Real.log x - c₀) ^ (-(1 / 2 : ℝ))| ≤
      K₁ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (-(1 / 2 : ℝ) - 1) := by
  obtain ⟨c, B, hB, hM⟩ := mertens_LamR_err
  obtain ⟨K, hK, hC⟩ := density_fR
  have hM' : ∀ y : ℝ, 1 ≤ y → |Err (toA gR gR_zero) (-(1 / 2)) (-(c / 2)) y| ≤
      (B / 2) / (1 + Real.log y) := by
    intro y hy
    have h := hM y hy
    have e : Err (toA gR gR_zero) (-(1 / 2)) (-(c / 2)) y =
        -(1 / 2) * (Msum LamR y - Real.log y - c) := by
      unfold Err Msum
      rw [mul_sub, mul_sub, mul_sum]
      have : ∑ m ∈ Ioc 0 ⌊y⌋₊, (toA gR gR_zero) m / m = ∑ m ∈ Ioc 0 ⌊y⌋₊, -(1 / 2) * (LamR m / m) :=
        sum_congr rfl fun m _ => by simp only [toA, coe_mk, gR]; ring
      rw [this]; ring
    rw [e, abs_mul]
    have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [this]
    have hl : 0 < 1 + Real.log y := by have := Real.log_nonneg hy; linarith
    calc 1 / 2 * |Msum LamR y - Real.log y - c| ≤ 1 / 2 * (B / (1 + Real.log y)) := by gcongr
      _ = B / 2 / (1 + Real.log y) := by ring
  obtain ⟨C₁, K₁, X₀, h⟩ := logmean_LSD (recFA gR) (toA gR gR_zero) (κ := -(1 / 2)) (c₀ := -(c / 2))
    (σ := 1 / 2) (B := B / 2) (K := K) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hK fR_log hM' (fun y hy => hC y hy)
  exact ⟨C₁, K₁, X₀, -(c / 2), fun x hx => h x hx⟩

end RamanujanTau.SelbergDelange3
