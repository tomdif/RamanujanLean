/-
# The Laplace transform of `x^{β−1}` at complex `s`

`∫_0^∞ x^{β−1} e^{−sx} dx = Γ(β) s^{−β}` for `β > 0`, `Re s > 0`.
Mathlib has the case of real `s > 0`. Both sides are holomorphic on `Re s > 0` (the left side by
differentiation under the integral), so the identity theorem extends it.
-/
import Mathlib

set_option autoImplicit false

namespace Rademacher
open Complex MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- the integrand. -/
def lapI (β : ℝ) (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ ((β : ℂ) - 1) * cexp (-(s * x))

/-- the Laplace transform. -/
def lap (β : ℝ) (s : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), lapI β s x

lemma norm_lapI {β : ℝ} {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖lapI β s x‖ = x ^ (β - 1) * Real.exp (-(s.re * x)) := by
  rw [lapI, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
  simp

lemma integrableOn_bound {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ (β - 1) * Real.exp (-(a * x))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := β - 1) (p := 1) (b := a) (by linarith) le_rfl ha
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

lemma integrable_lapI {β : ℝ} (hβ : 0 < β) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (lapI β s) (Ioi 0) := by
  refine (integrableOn_bound hβ hs).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    apply ContinuousAt.continuousWithinAt
    unfold lapI
    have hx' : (0 : ℝ) < x := hx
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr hx'.ne')).mul (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    rw [norm_lapI hx]

lemma lap_real {β : ℝ} (hβ : 0 < β) {r : ℝ} (hr : 0 < r) :
    lap β r = (r : ℂ) ^ (-(β : ℂ)) * Gamma β := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi (a := (β : ℂ)) (by simpa using hβ) hr
  rw [lap]
  simp only [lapI]
  rw [h]
  congr 1
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    cpow_neg]

lemma hasDerivAt_lapI (β : ℝ) (x : ℝ) (s : ℂ) :
    HasDerivAt (fun s => lapI β s x) (-(x : ℂ) * lapI β s x) s := by
  have h1 : HasDerivAt (fun s : ℂ => -(s * x)) (-(x : ℂ)) s := by
    simpa using ((hasDerivAt_id s).mul_const (x : ℂ)).neg
  have h2 := h1.cexp.const_mul ((x : ℂ) ^ ((β : ℂ) - 1))
  convert h2 using 1
  unfold lapI; ring

lemma lap_differentiableAt {β : ℝ} (hβ : 0 < β) {s₀ : ℂ} (hs : 0 < s₀.re) : DifferentiableAt ℂ (lap β) s₀ := by
  set a := s₀.re / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hball : ∀ s ∈ Metric.ball s₀ a, a ≤ s.re := by
    intro s hsb
    rw [Metric.mem_ball, dist_eq_norm] at hsb
    have := abs_re_le_norm (s - s₀)
    rw [sub_re] at this
    have := abs_lt.mp (lt_of_le_of_lt this hsb)
    linarith
  have hmeas : ∀ s : ℂ, 0 < s.re → AEStronglyMeasurable (lapI β s) (volume.restrict (Ioi 0)) :=
    fun s hs => (integrable_lapI hβ hs).aestronglyMeasurable
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s x => lapI β s x) (F' := fun s x => -(x : ℂ) * lapI β s x) (x₀ := s₀)
    (bound := fun x => x ^ ((β + 1) - 1) * Real.exp (-(a * x)))
    (Metric.ball_mem_nhds s₀ ha0)
    (by
      filter_upwards [Metric.ball_mem_nhds s₀ ha0] with s hsb
      exact hmeas s (by linarith [hball s hsb]))
    (integrable_lapI hβ hs)
    ((((continuous_ofReal.neg).aestronglyMeasurable).mul (hmeas s₀ hs)))
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx s hsb => ?_)
      have hx' : (0 : ℝ) < x := hx
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hx'.le, norm_lapI hx']
      show x * (x ^ (β - 1) * Real.exp (-(s.re * x))) ≤ x ^ (β + 1 - 1) * Real.exp (-(a * x))
      rw [show β + 1 - 1 = 1 + (β - 1) by ring, Real.rpow_add hx', Real.rpow_one, mul_assoc]
      gcongr
      have := hball s hsb
      nlinarith)
    (integrableOn_bound (by linarith) ha0)
    (Eventually.of_forall fun x s _ => hasDerivAt_lapI β x s)
  exact H.2.differentiableAt

/-- **the Laplace transform at complex `s`**. -/
theorem lap_eq {β : ℝ} (hβ : 0 < β) {s : ℂ} (hs : 0 < s.re) : lap β s = s ^ (-(β : ℂ)) * Gamma β := by
  set U : Set ℂ := {s | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ (lap β) U :=
    DifferentiableOn.analyticOnNhd (f := lap β) (fun s hs => (lap_differentiableAt hβ hs).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fun s => s ^ (-(β : ℂ)) * Gamma β) U := by
    refine (DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo)
    exact ((differentiableAt_id.cpow_const (Or.inl hs)).mul_const _).differentiableWithinAt
  have hU1 : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), lap β z = z ^ (-(β : ℂ)) * Gamma β := by
    set u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
    have hut : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at this
        exact (continuous_ofReal.tendsto 1).comp this |>.congr' (Eventually.of_forall fun n => rfl) |>.trans
          (by simp)
      · refine Eventually.of_forall fun n => ?_
        intro h
        rw [Set.mem_singleton_iff] at h
        have h2 := congrArg Complex.re h
        simp only [hu, ofReal_re, one_re] at h2
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hut.frequently (Frequently.of_forall fun n => ?_)
    have hr : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    exact lap_real hβ hr
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected hU1 hfreq hs

end

end Rademacher
