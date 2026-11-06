/-
# Reducing Selberg's (H1), (H2) to integrals along the line

For continuous `G ≥ 0` and `0 < h ≤ T` (no Fubini: an antiderivative `Φ` and its monotonicity)

    h ∫_{T+h}^{2T} G ≤ ∫_T^{2T} ∫_t^{t+h} G ≤ h ∫_T^{2T+h} G,

and the Cauchy–Schwarz inequality `(∫_t^{t+h} G)² ≤ h ∫_t^{t+h} G²` (via AM–GM).
With `G = |Z| w` these give (H1) from a first moment `∫_{T+h}^{2T} |Z| w ≥ aT` and (H2) from a
second moment `∫_T^{3T} (|Z| w)² ≤ BT`.  Level 1.
-/
import RamanujanTau.HafnerProportion.Abstract

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open MeasureTheory Set Filter

lemma setIcc_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, f t = ∫ t in a..b, f t := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- `∫_T^{2T} ∫_t^{t+h} G = ∫_{2T}^{2T+h} Φ − ∫_T^{T+h} Φ`, `Φ(x) = ∫_0^x G`. -/
lemma double_eq {G : ℝ → ℝ} (hG : Continuous G) {T h : ℝ} (hT : 0 ≤ T) :
    ∫ t in Icc T (2 * T), (∫ u in t..t + h, G u) =
      (∫ x in (2 * T)..(2 * T + h), ∫ u in (0 : ℝ)..x, G u) -
        ∫ x in T..(T + h), ∫ u in (0 : ℝ)..x, G u := by
  set Φ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, G u with hΦ
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 0
  have e : ∀ t, (∫ u in t..t + h, G u) = Φ (t + h) - Φ t := fun t =>
    (intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)).symm
  rw [setIcc_eq_interval (by linarith)]
  simp_rw [e]
  have hc2 : Continuous fun t => Φ (t + h) := hΦc.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hΦc.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_add_right (fun x => Φ x)]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := Φ)
    (a := T + h) (b := 2 * T) (c := 2 * T + h) (hΦc.intervalIntegrable _ _)
    (hΦc.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := Φ)
    (a := T) (b := T + h) (c := 2 * T) (hΦc.intervalIntegrable _ _)
    (hΦc.intervalIntegrable _ _)
  linarith

lemma primitive_mono {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) :
    Monotone fun x => ∫ u in (0 : ℝ)..x, G u := by
  intro x y hxy
  have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := G)
    (a := 0) (b := x) (c := y) (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)
  have h0 : 0 ≤ ∫ u in x..y, G u := intervalIntegral.integral_nonneg hxy fun u _ => hG0 u
  simp only
  linarith

/-- lower Fubini-free bound. -/
theorem double_lower {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) {T h : ℝ}
    (hh : 0 ≤ h) (hhT : h ≤ T) :
    h * ∫ u in (T + h)..(2 * T), G u ≤ ∫ t in Icc T (2 * T), (∫ u in t..t + h, G u) := by
  have hT : 0 ≤ T := le_trans hh hhT
  rw [double_eq hG hT]
  set Φ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, G u with hΦ
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 0
  have hmono := primitive_mono hG hG0
  have hA : h * Φ (2 * T) ≤ ∫ x in (2 * T)..(2 * T + h), Φ x := by
    have := intervalIntegral.integral_mono_on (f := fun _ => Φ (2 * T)) (g := Φ)
      (a := 2 * T) (b := 2 * T + h) (by linarith) (intervalIntegrable_const (μ := volume))
      (hΦc.intervalIntegrable _ _) fun x hx => hmono hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith [show 2 * T + h - 2 * T = h by ring]
  have hB : ∫ x in T..(T + h), Φ x ≤ h * Φ (T + h) := by
    have := intervalIntegral.integral_mono_on (f := Φ) (g := fun _ => Φ (T + h))
      (a := T) (b := T + h) (by linarith) (hΦc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume))
      fun x hx => hmono hx.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith [show T + h - T = h by ring]
  have hdiff : Φ (2 * T) - Φ (T + h) = ∫ u in (T + h)..(2 * T), G u :=
    intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  rw [← hdiff]
  nlinarith

/-- upper Fubini-free bound. -/
theorem double_upper {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) {T h : ℝ}
    (hh : 0 ≤ h) (hT : 0 ≤ T) :
    ∫ t in Icc T (2 * T), (∫ u in t..t + h, G u) ≤ h * ∫ u in T..(2 * T + h), G u := by
  rw [double_eq hG hT]
  set Φ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, G u with hΦ
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 0
  have hmono := primitive_mono hG hG0
  have hA : ∫ x in (2 * T)..(2 * T + h), Φ x ≤ h * Φ (2 * T + h) := by
    have := intervalIntegral.integral_mono_on (f := Φ) (g := fun _ => Φ (2 * T + h))
      (a := 2 * T) (b := 2 * T + h) (by linarith) (hΦc.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) fun x hx => hmono hx.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith [show 2 * T + h - 2 * T = h by ring]
  have hB : h * Φ T ≤ ∫ x in T..(T + h), Φ x := by
    have := intervalIntegral.integral_mono_on (f := fun _ => Φ T) (g := Φ)
      (a := T) (b := T + h) (by linarith) (intervalIntegrable_const (μ := volume))
      (hΦc.intervalIntegrable _ _) fun x hx => hmono hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith [show T + h - T = h by ring]
  have hdiff : Φ (2 * T + h) - Φ T = ∫ u in T..(2 * T + h), G u :=
    intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  rw [← hdiff]
  nlinarith

/-- Cauchy–Schwarz on a short interval, for `G ≥ 0`. -/
theorem sq_integral_le {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ u, 0 ≤ G u) {t h : ℝ}
    (hh : 0 < h) :
    (∫ u in t..t + h, G u) ^ 2 ≤ h * ∫ u in t..t + h, G u ^ 2 := by
  set J := ∫ u in t..t + h, G u with hJ
  set A := ∫ u in t..t + h, G u ^ 2 with hA
  have hth : t ≤ t + h := by linarith
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hth fun u _ => hG0 u
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hth fun u _ => sq_nonneg (G u)
  rcases hJ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  set l := h / J with hl
  have hl0 : 0 < l := by positivity
  have hle : J ≤ ∫ u in t..t + h, (l * G u ^ 2 + 1 / l) / 2 := by
    refine intervalIntegral.integral_mono_on hth (hG.intervalIntegrable _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun u _ => ?_
    have := abs_le_amgm (G u) hl0
    rwa [abs_of_nonneg (hG0 u)] at this
  have e : ∫ u in t..t + h, (l * G u ^ 2 + 1 / l) / 2 = (l * A + h / l) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (((hG.pow 2).intervalIntegrable _ _).const_mul l) (intervalIntegrable_const (μ := volume)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    rw [show t + h - t = h by ring]
    ring
  rw [e] at hle
  have e2 : h / l = J := by rw [hl]; field_simp
  rw [e2] at hle
  have e3 : l * A = h * A / J := by rw [hl]; ring
  rw [e3] at hle
  have : J ≤ h * A / J := by linarith
  rw [le_div_iff₀ hpos] at this
  nlinarith

end RamanujanTau.HafnerProportion
