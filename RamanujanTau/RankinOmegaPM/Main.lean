/-
# `RankinOmegaPM`: mean-square and signed Ω-results for the Rankin–Selberg error term

`R(x) = ∑_{n≤x} τ(n)²/n¹¹ − c x` (more generally `|a_f(n)|²/n^{k−1}` for a nonzero level-one cusp
form `f`). See `docs/RANKIN_OMEGA_PM.md`.

1. `tau_rankin_mellin_mean_sq_lower` (every real `c`):
   `∫₁^∞ |R(x)|² x^{−2σ−1} dx ≥ K/(σ − 3/8)` for `3/8 < σ ≤ 3/8 + 1/32`.
2. `tau_rankin_log_mean_sq_omega` (every real `c`):
   `∫₁^X |R(x)|² x^{−7/4} dx ≥ κ log X` for arbitrarily large `X`.
3. `tau_rankin_omega_pm` (Rankin's constant `c`): for every `β < 3/20` and every real `c₁`,
   `R(x) < −c₁ x^β` and `R(x) > c₁ x^β` both occur for arbitrarily large `x`, i.e.
   `R(x) = Ω±(x^{3/20−ε})`.
-/
import RamanujanTau.RankinOmegaPM.MeanOmega
import RamanujanTau.RankinOmegaPM.OmegaPM

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega
open scoped ENNReal

section Conv

variable {a : ℕ → ℝ}

lemma norm_Rf_of_one_lt (c : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖Rf a c x‖ = |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x| := by
  rw [Rf_eq_re c x, Complex.norm_real, Real.norm_eq_abs, Rf_re_of_one_lt c hx]

/-- An integer bound `|A(N) − cN| ≤ C N^{3/5}` gives the real-variable bound for `R`. -/
lemma hR_of_nat {c C : ℝ}
    (h : ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Finset.Icc 1 N, a n - c * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5)) :
    ∀ x : ℝ, 1 ≤ x → ‖Rf a c x‖ ≤ (|C| + |c|) * x ^ ((3 : ℝ) / 5) := by
  intro x hx
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x - N < 1 := by have := Nat.lt_floor_add_one x; linarith
  have hb := h N hN1
  have hNp : (N : ℝ) ^ ((3 : ℝ) / 5) ≤ x ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
  have hx1 : 1 ≤ x ^ ((3 : ℝ) / 5) := Real.one_le_rpow hx (by norm_num)
  have hCN : C * (N : ℝ) ^ ((3 : ℝ) / 5) ≤ |C| * x ^ ((3 : ℝ) / 5) := by
    have h0 : 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc C * (N : ℝ) ^ ((3 : ℝ) / 5) ≤ |C| * (N : ℝ) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ |C| * x ^ ((3 : ℝ) / 5) := mul_le_mul_of_nonneg_left hNp (abs_nonneg C)
  have hc1 : |c| ≤ |c| * x ^ ((3 : ℝ) / 5) := le_mul_of_one_le_right (abs_nonneg c) hx1
  have key : ‖Rf a c x‖ ≤ |∑ n ∈ Finset.Icc 1 N, a n - c * N| + |c| := by
    rcases eq_or_lt_of_le hx with h1 | h1
    · subst h1
      have hN' : N = 1 := by rw [hN]; simp
      have e : Rf a c 1 = ((a 1 : ℝ) : ℂ) := by
        rw [Rf, Asum, Ind, indicator_of_notMem (show (1 : ℝ) ∉ Ioi 1 by simp)]; simp
      rw [e, Complex.norm_real, Real.norm_eq_abs, hN']
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, mul_one]
      have := abs_sub_abs_le_abs_sub (a 1) c
      linarith
    · rw [norm_Rf_of_one_lt c h1, ← hN]
      have e : ∑ n ∈ Finset.Icc 1 N, a n - c * x =
          (∑ n ∈ Finset.Icc 1 N, a n - c * N) - c * (x - N) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - N)]
      have := abs_nonneg c
      nlinarith
  linarith

end Conv

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include d habs in
/-- **Mellin mean-square lower bound**, explicit form (abstract data, every real `c`). -/
theorem rs_mellin_mean_sq_lower (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 32 →
      ENNReal.ofReal (K / δ) ≤ ∫⁻ x in Ioi (1 : ℝ),
        ENNReal.ofReal (|∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x| ^ 2 *
          x ^ (-(2 * (3 / 8 + δ)) - 1)) := by
  obtain ⟨K, hK, h⟩ := mellin_mean_sq_lower d habs hm hne c
  refine ⟨K, hK, fun δ hδ0 hδ1 => (h δ hδ0 hδ1).trans_eq ?_⟩
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [norm_Rf_of_one_lt c hx]

include d habs in
/-- **Log-averaged mean square, Ω form**, explicit (abstract data, every real `c`). -/
theorem rs_log_mean_sq_omega (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ X0 : ℝ, ∃ X : ℝ, X0 ≤ X ∧
      κ' * Real.log X ≤ ∫ x in (1 : ℝ)..X,
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x| ^ 2 * x ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨κ', hκ, h⟩ := log_mean_sq_omega d habs hm hne c
  refine ⟨κ', hκ, fun X0 => ?_⟩
  obtain ⟨X, hX, hb⟩ := h (max X0 1)
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  refine ⟨X, le_trans (le_max_left _ _) hX, hb.trans_eq ?_⟩
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
  rw [uIoc_of_le hX1] at hx
  rw [norm_Rf_of_one_lt c hx.1]

end Data

section Cusp

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn
open ModularForm
open scoped MatrixGroups

variable {k : ℕ}

/-- **Mellin mean-square lower bound, every nonzero level-one cusp form, every real `c`.** -/
theorem cuspForm_mellin_mean_sq_lower (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 32 →
      ENNReal.ofReal (K / δ) ≤ ∫⁻ x in Ioi (1 : ℝ),
        ENNReal.ofReal (|∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x| ^ 2 *
          x ^ (-(2 * (3 / 8 + δ)) - 1)) := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  exact rs_mellin_mean_sq_lower rsDataG (abscissa_aF_le_one hm) (by omega) hne c

/-- **Log-averaged mean square, Ω form, every nonzero level-one cusp form, every real `c`.** -/
theorem cuspForm_log_mean_sq_omega (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ X0 : ℝ, ∃ X : ℝ, X0 ≤ X ∧
      κ' * Real.log X ≤ ∫ x in (1 : ℝ)..X,
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x| ^ 2 *
          x ^ (-(7 / 4 : ℝ)) := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  exact rs_log_mean_sq_omega rsDataG (abscissa_aF_le_one hm) (by omega) hne c

/-- **Ω± for every nonzero level-one cusp form**, given a `3/5` bound with constant `c`. -/
theorem cuspForm_omega_pm_of_bound (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ)
    (hC : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - c * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5))
    {β : ℝ} (hβ : β < 3 / 20) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x) := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  obtain ⟨C, hC⟩ := hC
  have hR := hR_of_nat (a := aF) (c := c) (C := C) hC
  exact rs_omega_pm rsDataG (abscissa_aF_le_one hm) (by omega) hne hR hβ c1 X

/-- **Ω±(x^β), `β < 3/20`, for every nonzero level-one cusp form** with its Rankin constant. -/
theorem cuspForm_rankin_omega_pm (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    {β : ℝ} (hβ : β < 3 / 20) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * x) :=
  cuspForm_omega_pm_of_bound f hf _ (RankinExact.rankinSelberg_exact_general f) hβ c1 X

end Cusp

section Tau

open RamanujanTau.RankinSelbergGeneral
open ModularForm
open scoped MatrixGroups

/-- **Headline 1 (τ, every real `c`): Mellin mean-square lower bound.**
`∫₁^∞ |∑_{n≤x} τ(n)²/n¹¹ − c x|² x^{−2σ−1} dx ≥ K/(σ − 3/8)`, `σ = 3/8 + δ`, `0 < δ ≤ 1/32`. -/
theorem tau_rankin_mellin_mean_sq_lower (c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 32 →
      ENNReal.ofReal (K / δ) ≤ ∫⁻ x in Ioi (1 : ℝ),
        ENNReal.ofReal (|∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - c * x| ^ 2 *
          x ^ (-(2 * (3 / 8 + δ)) - 1)) := by
  obtain ⟨K, hK, h⟩ := cuspForm_mellin_mean_sq_lower (k := 12) _ discriminant_ne_zero' c
  refine ⟨K, hK, fun δ hδ0 hδ1 => ?_⟩
  have hb := h δ hδ0 hδ1
  simp only [coeffSq_discriminant] at hb
  exact hb

/-- **Headline 2 (τ, every real `c`): the log-averaged mean square is not `o(log X)`.**
`∫₁^X |∑_{n≤x} τ(n)²/n¹¹ − c x|² x^{−7/4} dx ≥ κ log X` for arbitrarily large `X`. -/
theorem tau_rankin_log_mean_sq_omega (c : ℝ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ X0 : ℝ, ∃ X : ℝ, X0 ≤ X ∧
      κ' * Real.log X ≤ ∫ x in (1 : ℝ)..X,
        |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - c * x| ^ 2 *
          x ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨κ', hκ, h⟩ := cuspForm_log_mean_sq_omega (k := 12) _ discriminant_ne_zero' c
  refine ⟨κ', hκ, fun X0 => ?_⟩
  obtain ⟨X, hX, hb⟩ := h X0
  refine ⟨X, hX, ?_⟩
  simp only [coeffSq_discriminant] at hb
  exact hb

/-- **Headline 3 (τ, Rankin's constant): `R(x) = Ω±(x^β)` for every `β < 3/20`.**
For every real `c₁` and every `X` there are `x, x' ≥ X` with
`R(x) < −c₁ x^β` and `R(x') > c₁ x'^β`, `R(x) = ∑_{n≤x} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11!·x`. -/
theorem tau_rankin_omega_pm {β : ℝ} (hβ : β < 3 / 20) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * x
        < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * x) := by
  have hC : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, coeffSq (k := 12)
          (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n / (n : ℝ) ^ (12 - 1) -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
    obtain ⟨C, hC⟩ := RankinExact.rankinSelberg_exact
    refine ⟨C, fun N hN => ?_⟩
    simp only [coeffSq_discriminant]
    exact hC N hN
  have h := cuspForm_omega_pm_of_bound (k := 12) _ discriminant_ne_zero' _ hC hβ c1 X
  simp only [coeffSq_discriminant] at h
  exact h

end Tau

end RamanujanTau.RankinOmegaPM

-- headlines
#print axioms RamanujanTau.RankinOmegaPM.tau_rankin_mellin_mean_sq_lower
#print axioms RamanujanTau.RankinOmegaPM.tau_rankin_log_mean_sq_omega
#print axioms RamanujanTau.RankinOmegaPM.tau_rankin_omega_pm
#print axioms RamanujanTau.RankinOmegaPM.cuspForm_mellin_mean_sq_lower
#print axioms RamanujanTau.RankinOmegaPM.cuspForm_log_mean_sq_omega
#print axioms RamanujanTau.RankinOmegaPM.cuspForm_rankin_omega_pm
#print axioms RamanujanTau.RankinOmegaPM.cuspForm_omega_pm_of_bound
#print axioms RamanujanTau.RankinOmegaPM.rs_mellin_mean_sq_lower
#print axioms RamanujanTau.RankinOmegaPM.rs_log_mean_sq_omega
#print axioms RamanujanTau.RankinOmegaPM.rs_omega_pm
-- abstract core results
#print axioms RamanujanTau.RankinOmegaPM.mellin_mean_sq_lower
#print axioms RamanujanTau.RankinOmegaPM.log_mean_sq_omega
#print axioms RamanujanTau.RankinOmegaPM.core_lower
#print axioms RamanujanTau.RankinOmegaPM.Lam_eq_mellin_conv
#print axioms RamanujanTau.RankinOmegaPM.hfun_sq
#print axioms RamanujanTau.RankinOmegaPM.lintegral_weight_le
#print axioms RamanujanTau.RankinOmegaPM.conv_of_one_sided
#print axioms RamanujanTau.RankinOmegaPM.false_of_conv
#print axioms RamanujanTau.RankinOmegaPM.M_eq_cont
#print axioms RamanujanTau.RankinOmegaPM.landau_mellin_strip
#print axioms RamanujanTau.RankinOmegaPM.Z1_real_ne_zero
#print axioms RamanujanTau.RankinOmegaPM.exists_strip
#print axioms RamanujanTau.RankinOmegaPM.hR_of_nat
