/-
# Cumulative critical-line mean square `∫_0^T |L(Δ,6+it)|² ≪ T log T`

Dyadic summation of `Upper.dyadic_upper` (induction on `n` with `T ≤ 2ⁿ`).
-/
import RamanujanTau.CriticalMeanSquare.Upper

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquare

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL

/-- The integrand `|L(Δ,6+it)|²`. -/
noncomputable def Lsq (t : ℝ) : ℝ := ‖tauL (6 + t * I)‖ ^ 2

lemma continuous_Lsq : Continuous Lsq :=
  (tauLSeries_entire.continuous.comp (by fun_prop)).norm.pow 2

lemma Lsq_nonneg (t : ℝ) : 0 ≤ Lsq t := sq_nonneg _

lemma setIntegral_Icc_eq_interval {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, Lsq t = ∫ t in a..b, Lsq t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- `∫_1^T |L|² ≤ 2C T (1 + log T)` for `1 ≤ T ≤ 2ⁿ`, by induction on `n`. -/
lemma cum_aux {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ T : ℝ, 1 ≤ T → ∫ t in Icc T (2 * T), Lsq t ≤ C * T * (1 + Real.log T)) :
    ∀ n : ℕ, ∀ T : ℝ, 1 ≤ T → T ≤ 2 ^ n →
      ∫ t in (1 : ℝ)..T, Lsq t ≤ 2 * C * T * (1 + Real.log T) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable Lsq volume a b := fun a b =>
    continuous_Lsq.intervalIntegrable a b
  -- base: `T ≤ 2`
  have base : ∀ T : ℝ, 1 ≤ T → T ≤ 2 → ∫ t in (1 : ℝ)..T, Lsq t ≤ 2 * C * T * (1 + Real.log T) := by
    intro T h1 h2
    have hlog := Real.log_nonneg h1
    have hmono : ∫ t in (1 : ℝ)..T, Lsq t ≤ ∫ t in (1 : ℝ)..2, Lsq t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 T) (hii T 2)]
      have := intervalIntegral.integral_nonneg (μ := volume) h2 (fun t _ => Lsq_nonneg t)
      linarith
    have h12 := hC 1 le_rfl
    rw [mul_one, Real.log_one, setIntegral_Icc_eq_interval (by norm_num : (1 : ℝ) ≤ 2)] at h12
    have : C * 1 * (1 + 0) ≤ 2 * C * T * (1 + Real.log T) := by
      have h3 : 1 ≤ 2 * T * (1 + Real.log T) := by nlinarith
      nlinarith
    linarith
  intro n
  induction n with
  | zero => intro T h1 h2; exact base T h1 (by simp at h2; linarith)
  | succ n ih =>
    intro T h1 h2
    rcases le_or_gt T 2 with hT2 | hT2
    · exact base T h1 hT2
    have hT0 : 0 < T := by linarith
    have hh1 : 1 ≤ T / 2 := by linarith
    have hh2 : T / 2 ≤ 2 ^ n := by rw [pow_succ] at h2; linarith
    have hIH := ih (T / 2) hh1 hh2
    have hD := hC (T / 2) hh1
    rw [show 2 * (T / 2) = T by ring, setIntegral_Icc_eq_interval (by linarith)] at hD
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 (T / 2)) (hii (T / 2) T)]
    have hlog : Real.log (T / 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (T / 2) := Real.log_nonneg hh1
    have e1 : 2 * C * (T / 2) * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by
      have : C * T * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by gcongr
      linarith
    have e2 : C * (T / 2) * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) / 2 := by
      have : C * T * (1 + Real.log (T / 2)) ≤ C * T * (1 + Real.log T) := by gcongr
      linarith
    have e3 : 0 ≤ C * T * (1 + Real.log T) := by
      have := Real.log_nonneg h1; positivity
    linarith

/-- **Cumulative upper bound**: `∫_0^T |L(Δ,6+it)|² dt ≤ C T (1 + log T)` for `T ≥ 1`. -/
theorem cumulative_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) := by
  obtain ⟨C, hC0, hC⟩ := dyadic_upper
  set B : ℝ := ∫ t in (0 : ℝ)..1, Lsq t with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (μ := volume) zero_le_one (fun t _ => Lsq_nonneg t)
  refine ⟨B + 2 * C, by positivity, fun T hT => ?_⟩
  have hlog := Real.log_nonneg hT
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
  have h1 := cum_aux hC0 hC n T hT hn.le
  have hii : ∀ a b : ℝ, IntervalIntegrable Lsq volume a b := fun a b =>
    continuous_Lsq.intervalIntegrable a b
  show ∫ t in Icc 0 T, Lsq t ≤ _
  rw [setIntegral_Icc_eq_interval (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 1) (hii 1 T), ← hB]
  have : B ≤ B * T * (1 + Real.log T) := by
    have : 1 ≤ T * (1 + Real.log T) := by nlinarith
    nlinarith
  nlinarith

/-- **`∫_0^T |L(Δ,6+it)|² dt ≪ T log T`** (for `T ≥ e`). -/
theorem critical_mean_square_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := cumulative_upper
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  have h1 : 1 ≤ T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hT
  have hl : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  refine (hC T h1).trans ?_
  have : 0 ≤ C * T := by positivity
  nlinarith

/-- **Dyadic form** `∫_T^{2T} |L(Δ,6+it)|² dt ≪ T log T` (for `T ≥ e`). -/
theorem dyadic_mean_square_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := dyadic_upper
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  have h1 : 1 ≤ T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hT
  have hl : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  refine (hC T h1).trans ?_
  have : 0 ≤ C * T := by positivity
  nlinarith

end RamanujanTau.CriticalMeanSquare
