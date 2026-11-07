/-
# `ZetaCritical`: Hardy–Littlewood (1918) on the critical line

See `docs/ZETA_CRITICAL.md`.

* `zeta_critical_mean_square_bound`: `∃ C, ∀ T ≥ 3,
  |∫₀ᵀ |ζ(1/2+it)|² dt − T log T| ≤ C · T √(log T)`;
* `zeta_critical_mean_square`: `(∫₀ᵀ |ζ(1/2+it)|² dt) / (T log T) → 1`.

Ingham's second term `(2γ − 1 − log 2π) T` is **not** reached: the method (mean-square
approximation by `∑_{n≤T} n^{−s}` plus a monotone averaging sandwich) has error `T √(log T)`.
-/
import RamanujanTau.ZetaCritical.Critical

set_option autoImplicit false

namespace RamanujanTau.ZetaCritical

open Complex MeasureTheory Set Filter Topology

lemma half_line_ne_one (t : ℝ) : (1 / 2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

lemma continuous_half_line : Continuous fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  exact ((differentiableAt_riemannZeta (half_line_ne_one t)).continuousAt.comp
    (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) (x := t) (by fun_prop)).norm.pow 2

lemma integral_one_eq_Iz {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 = Iz T := by
  have h := RamanujanTau.ZetaMeanSquare.integral_plus_eq_minus (1 / 2) one_pos hT
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [← e, h]; rfl

/-- The constant `∫₀¹ |ζ(1/2+it)|² dt`. -/
noncomputable def c0 : ℝ := ∫ t in (0 : ℝ)..1, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2

lemma c0_nonneg : 0 ≤ c0 := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => by positivity

lemma integral_zero_eq {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 = c0 + Iz T := by
  rw [← integral_one_eq_Iz hT, c0]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (continuous_half_line.intervalIntegrable _ _) (continuous_half_line.intervalIntegrable _ _)).symm

/-- **Hardy–Littlewood (1918), quantitative form.** -/
theorem zeta_critical_mean_square_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T →
    |(∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - T * Real.log T| ≤
      C * (T * Real.sqrt (Real.log T)) := by
  refine ⟨c0 + 731 + 3 * CE, by linarith [c0_nonneg, CE_nonneg], fun T hT => ?_⟩
  rw [integral_zero_eq (by linarith)]
  have h := Iz_sqrt T hT
  have hL1 : 1 ≤ Real.log T := one_le_log_three.trans (Real.log_le_log (by norm_num) hT)
  have hr1 : 1 ≤ Real.sqrt (Real.log T) := Real.one_le_sqrt.2 hL1
  have hTr : 1 ≤ T * Real.sqrt (Real.log T) := by nlinarith
  have hc := c0_nonneg
  have : c0 ≤ c0 * (T * Real.sqrt (Real.log T)) := le_mul_of_one_le_right hc hTr
  calc |c0 + Iz T - T * Real.log T| ≤ |c0| + |Iz T - T * Real.log T| := by
        rw [add_sub_assoc]; exact abs_add_le _ _
    _ ≤ c0 + (731 + 3 * CE) * (T * Real.sqrt (Real.log T)) := by
        rw [abs_of_nonneg hc]; linarith
    _ ≤ (c0 + 731 + 3 * CE) * (T * Real.sqrt (Real.log T)) := by nlinarith

/-- **Hardy–Littlewood (1918):** `∫₀ᵀ |ζ(1/2+it)|² dt ~ T log T`. -/
theorem zeta_critical_mean_square :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) /
      (T * Real.log T)) atTop (𝓝 1) := by
  obtain ⟨C, hC, h⟩ := zeta_critical_mean_square_bound
  have hlim : Tendsto (fun T : ℝ => C / Real.sqrt (Real.log T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_sqrt_atTop).comp Real.tendsto_log_atTop)
  have hsub : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) /
      (T * Real.log T) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hL1 : 1 ≤ Real.log T := one_le_log_three.trans (Real.log_le_log (by norm_num) hT)
    have hT0 : 0 < T := by linarith
    have hTL : 0 < T * Real.log T := by positivity
    have hr0 : 0 < Real.sqrt (Real.log T) := Real.sqrt_pos.2 (by linarith)
    have hrr : Real.sqrt (Real.log T) * Real.sqrt (Real.log T) = Real.log T :=
      Real.mul_self_sqrt (by linarith)
    rw [Real.norm_eq_abs, div_sub_one hTL.ne', abs_div, abs_of_pos hTL, div_le_iff₀ hTL]
    calc |(∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) - T * Real.log T|
        ≤ C * (T * Real.sqrt (Real.log T)) := h T hT
      _ = C / Real.sqrt (Real.log T) * (T * Real.log T) := by
          rw [div_mul_eq_mul_div, eq_div_iff hr0.ne',
            show T * Real.log T = T * (Real.sqrt (Real.log T) * Real.sqrt (Real.log T)) by
              rw [hrr]]
          ring
  have := hsub.add_const 1
  simpa using this

end RamanujanTau.ZetaCritical

#print axioms RamanujanTau.ZetaCritical.zeta_critical_mean_square
#print axioms RamanujanTau.ZetaCritical.zeta_critical_mean_square_bound
#print axioms RamanujanTau.ZetaCritical.Iz_sqrt
#print axioms RamanujanTau.ZetaCritical.Iz_eps
#print axioms RamanujanTau.ZetaCritical.avg_mv
#print axioms RamanujanTau.ZetaCritical.offdiag_ch_le
