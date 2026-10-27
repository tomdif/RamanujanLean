/-
# The major arc: Laplace's method

`h_{A,t}(v) = √(1 + iv/√A) · e^{−t(1+iv/√A)/24} · e^{−v²/(1+iv/√A)}`. As `A → ∞`, `t → 0`:
`∫_{−√A}^{√A} h_{A,t}(v) dv → √π`, by dominated convergence with bound `2e^{−v²/2}`.
-/
import RamanujanTau.HardyRamanujan.Minor

set_option autoImplicit false

namespace HardyRamanujan
open Complex Filter MeasureTheory
open scoped Real Topology

/-- the scaled integrand, as a function of `u = v/√A`, `t` and `v`. -/
noncomputable def hfun (u t v : ℝ) : ℂ :=
  cexp (log (1 + u * I) / 2) * cexp (-((t : ℂ) * (1 + u * I)) / 24) * cexp (-((v : ℂ) ^ 2 / (1 + u * I)))

lemma one_add_mem_slit (u : ℝ) : (1 + u * I) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp))

lemma one_add_ne_zero (u : ℝ) : (1 + u * I) ≠ 0 := slitPlane_ne_zero (one_add_mem_slit u)

lemma hfun_continuous (t v : ℝ) : Continuous fun u : ℝ => hfun u t v := by
  unfold hfun
  have hl : Continuous fun u : ℝ => log (1 + u * I) :=
    continuous_iff_continuousAt.mpr fun u =>
      ContinuousAt.clog (f := fun u : ℝ => 1 + (u : ℂ) * I) (by fun_prop) (one_add_mem_slit u)
  have hd : Continuous fun u : ℝ => -((v : ℂ) ^ 2 / (1 + u * I)) :=
    (continuous_const.div (by fun_prop) one_add_ne_zero).neg
  fun_prop

lemma hfun_continuous_v (u t : ℝ) : Continuous fun v : ℝ => hfun u t v := by
  unfold hfun; fun_prop

lemma hfun_lim (v : ℝ) {u t : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => hfun (u n) (t n) v) atTop (𝓝 (cexp (-((v : ℂ) ^ 2)))) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ => hfun p.1 p.2 v) (0, 0) := by
    unfold hfun
    have h1 : ContinuousAt (fun p : ℝ × ℝ => log (1 + p.1 * I)) (0, 0) :=
      ContinuousAt.clog (f := fun p : ℝ × ℝ => 1 + (p.1 : ℂ) * I) (by fun_prop) (one_add_mem_slit 0)
    have h2 : ContinuousAt (fun p : ℝ × ℝ => -((v : ℂ) ^ 2 / (1 + p.1 * I))) (0, 0) :=
      (ContinuousAt.div (f := fun _ : ℝ × ℝ => (v : ℂ) ^ 2) (g := fun p : ℝ × ℝ => 1 + (p.1 : ℂ) * I)
        continuousAt_const (by fun_prop) (one_add_ne_zero 0)).neg
    exact ((h1.div_const 2).cexp.mul (by fun_prop)).mul h2.cexp
  have := hc.tendsto.comp (hu.prodMk_nhds ht)
  simp only [hfun] at this
  convert this using 2
  simp

lemma norm_hfun_le {u t v : ℝ} (hu : |u| ≤ 1) (ht : 0 ≤ t) : ‖hfun u t v‖ ≤ 2 * Real.exp (-(v ^ 2) / 2) := by
  unfold hfun
  rw [norm_mul, norm_mul, norm_exp, norm_exp, norm_exp]
  have e1 : (log (1 + u * I) / 2).re = Real.log ‖1 + u * I‖ / 2 := by
    rw [Complex.div_ofNat_re, log_re]
  have e2 : (-((t : ℂ) * (1 + u * I)) / 24).re = -t / 24 := by simp
  have hw : 0 < 1 + u ^ 2 := by positivity
  have e3 : (-((v : ℂ) ^ 2 / (1 + u * I))).re = -(v ^ 2 / (1 + u ^ 2)) := by
    have hd : (v : ℂ) ^ 2 / (1 + u * I) = ((v ^ 2 / (1 + u ^ 2) : ℝ) : ℂ) + ((-(v ^ 2 * u) / (1 + u ^ 2) : ℝ) : ℂ) * I := by
      rw [div_eq_iff (one_add_ne_zero u)]
      push_cast
      have hw' : (1 : ℂ) + (u : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hw.ne'
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [neg_re, hd, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [e1, e2, e3]
  have hn : ‖1 + u * I‖ ≤ 2 := by
    calc ‖1 + u * I‖ ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * I‖ := norm_add_le _ _
      _ ≤ 2 := by simp [Complex.norm_real]; linarith [abs_nonneg u]
  have hn0 : 0 < ‖1 + u * I‖ := norm_pos_iff.mpr (one_add_ne_zero u)
  have b1 : Real.exp (Real.log ‖1 + u * I‖ / 2) ≤ 2 := by
    calc Real.exp (Real.log ‖1 + u * I‖ / 2) ≤ Real.exp (Real.log ‖1 + u * I‖) := by
          apply Real.exp_le_exp.mpr
          have : Real.log ‖1 + u * I‖ ≥ 0 := Real.log_nonneg (by
            have : 1 ≤ ‖1 + u * I‖ := by
              have := Complex.abs_re_le_norm (1 + u * I); simp at this; linarith
            linarith)
          linarith
      _ = ‖1 + u * I‖ := Real.exp_log hn0
      _ ≤ 2 := hn
  have b2 : Real.exp (-t / 24) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have b3 : Real.exp (-(v ^ 2 / (1 + u ^ 2))) ≤ Real.exp (-(v ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) hw]
    nlinarith [sq_nonneg v]
  calc Real.exp (Real.log ‖1 + u * I‖ / 2) * Real.exp (-t / 24) * Real.exp (-(v ^ 2 / (1 + u ^ 2)))
      ≤ 2 * 1 * Real.exp (-(v ^ 2) / 2) := by gcongr
    _ = _ := by ring

/-- **Laplace's method on the major arc**. -/
theorem J_tendsto {A t : ℕ → ℝ} (hA : Tendsto A atTop atTop) (hA0 : ∀ n, 0 < A n)
    (ht : Tendsto t atTop (𝓝 0)) (ht0 : ∀ n, 0 ≤ t n) :
    Tendsto (fun n => ∫ v in (-√(A n))..√(A n), hfun (v / √(A n)) (t n) v) atTop
      (𝓝 ((√π : ℝ) : ℂ)) := by
  have hsq : ∀ n, 0 < √(A n) := fun n => Real.sqrt_pos.mpr (hA0 n)
  have heq : ∀ n, (∫ v in (-√(A n))..√(A n), hfun (v / √(A n)) (t n) v) =
      ∫ v, Set.indicator (Set.Ioc (-√(A n)) (√(A n))) (fun v => hfun (v / √(A n)) (t n) v) v := by
    intro n
    rw [intervalIntegral.integral_of_le (by linarith [hsq n]), integral_indicator measurableSet_Ioc]
  simp only [heq]
  have hG : ∫ v : ℝ, cexp (-((v : ℂ) ^ 2)) = ((√π : ℝ) : ℂ) := by
    have h := integral_gaussian 1
    rw [div_one] at h
    calc ∫ v : ℝ, cexp (-((v : ℂ) ^ 2)) = ∫ v : ℝ, ((Real.exp (-1 * v ^ 2) : ℝ) : ℂ) := by
          congr 1; funext v; rw [ofReal_exp]; push_cast; ring_nf
      _ = ((∫ v : ℝ, Real.exp (-1 * v ^ 2) : ℝ) : ℂ) := integral_ofReal
      _ = _ := by rw [h]
  rw [← hG]
  refine tendsto_integral_of_dominated_convergence (fun v => 2 * Real.exp (-(v ^ 2) / 2)) (fun n => ?_)
    ?_ (fun n => ?_) ?_
  · refine (Continuous.aestronglyMeasurable ?_).indicator measurableSet_Ioc
    have := (hfun_continuous (t n) 0)
    unfold hfun
    have hl : Continuous fun v : ℝ => log (1 + ((v / √(A n) : ℝ) : ℂ) * I) :=
      continuous_iff_continuousAt.mpr fun v =>
        ContinuousAt.clog (f := fun v : ℝ => 1 + ((v / √(A n) : ℝ) : ℂ) * I) (by fun_prop) (one_add_mem_slit _)
    have hd : Continuous fun v : ℝ => -((v : ℂ) ^ 2 / (1 + ((v / √(A n) : ℝ) : ℂ) * I)) :=
      ((by fun_prop : Continuous fun v : ℝ => (v : ℂ) ^ 2).div (by fun_prop) fun v => one_add_ne_zero _).neg
    fun_prop
  · have := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul 2
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only; congr 2; ring
  · refine Eventually.of_forall fun v => ?_
    by_cases hv : v ∈ Set.Ioc (-√(A n)) (√(A n))
    · rw [Set.indicator_of_mem hv]
      refine norm_hfun_le ?_ (ht0 n)
      rw [abs_div, abs_of_pos (hsq n), div_le_one (hsq n), abs_le]
      exact ⟨hv.1.le, hv.2⟩
    · rw [Set.indicator_of_notMem hv, norm_zero]; positivity
  · refine Eventually.of_forall fun v => ?_
    have hsA : Tendsto (fun n => √(A n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hA
    have hmem : ∀ᶠ n in atTop, v ∈ Set.Ioc (-√(A n)) (√(A n)) := by
      filter_upwards [hsA.eventually_gt_atTop |v|] with n hn
      constructor <;> [linarith [neg_abs_le v]; linarith [le_abs_self v]]
    have hlim := hfun_lim v (u := fun n => v / √(A n)) (tendsto_const_nhds.div_atTop hsA) ht
    refine hlim.congr' ?_
    filter_upwards [hmem] with n hn
    rw [Set.indicator_of_mem hn]

end HardyRamanujan
