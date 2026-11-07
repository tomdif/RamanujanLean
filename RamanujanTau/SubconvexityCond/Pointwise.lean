/-
# Pointwise from mean (Gallagher / Sobolev on a unit interval) for Dirichlet polynomials

    |P(T)|² ≤ 2e ( ∫ w |P|² + ∫ w |P_log|² ),   w(t) = e^{−((t−T)/H)²}, H ≥ 1,

where `P_log(t) = ∑ aₙ log n · n^{−it}` is `i·P'(t)` (`norm_sq_le_window`).  Proof: FTC on
`[T, t]`, averaging over `t ∈ [T, T+1]`, `(∫₀¹ f)² ≤ ∫₀¹ f²`, and `w ≥ e^{−1}` on `[T, T+1]`.
-/
import RamanujanTau.SubconvexityCond.Expand

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Complex MeasureTheory Finset
open RamanujanTau.MeanSquare

lemma hasDerivAt_ex (l t : ℝ) : HasDerivAt (fun s : ℝ => ex l s) ((l : ℂ) * I * ex l t) t := by
  unfold ex
  have h1 : HasDerivAt (fun s : ℝ => ((l * s : ℝ) : ℂ)) (l : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul l).ofReal_comp
    simpa using this
  have h2 := (h1.mul_const I).cexp
  convert h2 using 1
  ring

/-- `P' = −i P_log`. -/
lemma hasDerivAt_rpoly (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (rpoly a N) (-I * rpoly (fun n => a n * Real.log n) N t) t := by
  unfold rpoly dpoly
  have h : ∀ n ∈ Icc 1 N, HasDerivAt (fun s : ℝ => (a n : ℂ) * ex (-Real.log n) s)
      ((a n : ℂ) * (((-Real.log n : ℝ) : ℂ) * I * ex (-Real.log n) t)) t :=
    fun n _ => (hasDerivAt_ex _ t).const_mul _
  have := HasDerivAt.fun_sum h
  convert this using 1
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  push_cast; ring

lemma norm_deriv_rpoly (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ‖-I * rpoly (fun n => a n * Real.log n) N t‖ = ‖rpoly (fun n => a n * Real.log n) N t‖ := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- **Gallagher's inequality on `[T, T+1]`.** -/
theorem norm_rpoly_le (a : ℕ → ℝ) (N : ℕ) (T : ℝ) :
    ‖rpoly a N T‖ ≤ (∫ t in T..T + 1, ‖rpoly a N t‖) +
      ∫ t in T..T + 1, ‖rpoly (fun n => a n * Real.log n) N t‖ := by
  set Q := rpoly (fun n => a n * Real.log n) N
  have hQc : Continuous Q := continuous_rpoly _ N
  have hPc : Continuous (rpoly a N) := continuous_rpoly a N
  set I1 := ∫ t in T..T + 1, ‖Q t‖
  have hpt : ∀ t ∈ Set.Icc T (T + 1), ‖rpoly a N T‖ ≤ ‖rpoly a N t‖ + I1 := by
    intro t ht
    have hD : Continuous fun s => -I * Q s := continuous_const.mul hQc
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := rpoly a N) (a := T) (b := t)
      (fun x _ => hasDerivAt_rpoly a N x) (hD.intervalIntegrable _ _)
    have e : rpoly a N T = rpoly a N t - ∫ s in T..t, -I * Q s := by rw [hftc]; ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    have hn : ∀ s, ‖-I * Q s‖ = ‖Q s‖ := fun s => by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    simp_rw [hn]
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun s => norm_nonneg _) (hQc.norm.intervalIntegrable _ _)
  have h1 : ∫ _ in T..T + 1, ‖rpoly a N T‖ ≤ ∫ t in T..T + 1, (‖rpoly a N t‖ + I1) :=
    intervalIntegral.integral_mono_on (by linarith) (continuous_const.intervalIntegrable _ _)
      ((hPc.norm.add continuous_const).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hPc.norm.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const] at h1
  simp only [add_sub_cancel_left, one_smul] at h1
  exact h1

/-- `(∫_T^{T+1} f)² ≤ ∫_T^{T+1} f²`. -/
lemma sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    (∫ t in T..T + 1, f t) ^ 2 ≤ ∫ t in T..T + 1, f t ^ 2 := by
  set c := ∫ t in T..T + 1, f t
  have h0 : 0 ≤ ∫ t in T..T + 1, (f t - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
  have e : ∫ t in T..T + 1, (f t - c) ^ 2 = (∫ t in T..T + 1, f t ^ 2) - c ^ 2 := by
    have e1 : (fun t => (f t - c) ^ 2) = fun t => (f t ^ 2 - (2 * c) * f t) + c ^ 2 := by
      funext t; ring
    rw [e1, intervalIntegral.integral_add
      ((((hf.pow 2).sub (hf.const_mul _))).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_sub
      ((hf.pow 2).intervalIntegrable _ _) ((hf.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul, add_sub_cancel_left, one_mul]
    ring
  linarith

/-- On `[T, T+1]` the window is `≥ e^{−1}` (for `H ≥ 1`). -/
lemma integral_unit_le_window {H : ℝ} (hH : 1 ≤ H) (a : ℕ → ℝ) (N : ℕ) (T : ℝ) :
    ∫ t in T..T + 1, ‖rpoly a N t‖ ^ 2 ≤
      Real.exp 1 * ∫ t : ℝ, gw H T t * ‖rpoly a N t‖ ^ 2 := by
  have hH0 : 0 < H := by linarith
  have hint := integrable_gw_normSq hH0 T a N
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ t in Set.Ioc T (T + 1), ‖rpoly a N t‖ ^ 2 ≤
      ∫ t in Set.Ioc T (T + 1), Real.exp 1 * (gw H T t * ‖rpoly a N t‖ ^ 2) := by
    refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
    · exact ((continuous_rpoly a N).norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · intro t ht
      have hw : Real.exp (-1) ≤ gw H T t := by
        unfold gw
        refine Real.exp_le_exp.2 ?_
        have h0 : 0 ≤ (t - T) / H := div_nonneg (by linarith [ht.1]) hH0.le
        have h1 : (t - T) / H ≤ 1 := by rw [div_le_one hH0]; linarith [ht.2]
        nlinarith
      have hp := sq_nonneg ‖rpoly a N t‖
      have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      calc ‖rpoly a N t‖ ^ 2 = Real.exp 1 * (Real.exp (-1) * ‖rpoly a N t‖ ^ 2) := by
            rw [← mul_assoc, this, one_mul]
        _ ≤ Real.exp 1 * (gw H T t * ‖rpoly a N t‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hp) (Real.exp_pos 1).le
  refine h1.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (gw_pos H T t).le (sq_nonneg _))

/-- **Pointwise from mean.** -/
theorem norm_sq_le_window {H : ℝ} (hH : 1 ≤ H) (a : ℕ → ℝ) (N : ℕ) (T : ℝ) :
    ‖rpoly a N T‖ ^ 2 ≤ 2 * Real.exp 1 * ((∫ t : ℝ, gw H T t * ‖rpoly a N t‖ ^ 2) +
      ∫ t : ℝ, gw H T t * ‖rpoly (fun n => a n * Real.log n) N t‖ ^ 2) := by
  set a' := fun n => a n * Real.log n
  have hg := norm_rpoly_le a N T
  set A := ∫ t in T..T + 1, ‖rpoly a N t‖
  set B := ∫ t in T..T + 1, ‖rpoly a' N t‖
  have hA := sq_integral_le (continuous_rpoly a N).norm T
  have hB := sq_integral_le (continuous_rpoly a' N).norm T
  have hA2 := integral_unit_le_window hH a N T
  have hB2 := integral_unit_le_window hH a' N T
  have h0 : 0 ≤ ‖rpoly a N T‖ := norm_nonneg _
  have hsq : ‖rpoly a N T‖ ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A - B)]
  nlinarith

end RamanujanTau.SubconvexityCond
