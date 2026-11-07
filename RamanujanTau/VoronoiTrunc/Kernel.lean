/-
# The Schläfli kernel on the steepest-descent path, and its asymptotic with phase

For `ν : ℕ` and `L > 0` let `f(v) = v^{−(ν+1)} exp(L(v − 1/v))` and let `v(s) = (1−s) + s i`,
`s ≥ 0` (the ray from `1` through the saddle point `i`, direction `e^{3πi/4}`).  Put

    A_ν(L) = ∫₀^∞ (−1+i) f(v(s)) ds,      I_ν(L) = Im A_ν(L) / π.

(`I_ν(L) = J_ν(2L)`; this identification is not needed.)  Main results:

* `Ik_asymp_twelve`: `|I₁₂(L) − cos(2L − π/4)/√(πL)| ≤ C/L` for `L ≥ 1`;
* `Ik_bound`: `|I_ν(L)| ≤ C_ν L^{−1/2}` for `L ≥ 1`.

Everything is elementary: on the path `Re(v − 1/v) = −2s(1−s)²/((1−s)²+s²) ≤ 0`, and near the
saddle `v = i + u(1−i)` one has the exact identity `v − 1/v = 2i + w²/(i+w)`, `w = u(1−i)`,
`w² = −2iu²`, so the integrand is a Gaussian `e^{2iL} e^{−2Lu²}` up to `O(|u|³L)` in the exponent.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

/-- The path `v(s) = (1 − s) + s i`. -/
noncomputable def pv (s : ℝ) : ℂ := ((1 - s : ℝ) : ℂ) + (s : ℂ) * I

lemma pv_re (s : ℝ) : (pv s).re = 1 - s := by simp [pv]
lemma pv_im (s : ℝ) : (pv s).im = s := by simp [pv]

lemma normSq_pv (s : ℝ) : Complex.normSq (pv s) = (1 - s) ^ 2 + s ^ 2 := by
  rw [Complex.normSq_apply, pv_re, pv_im]; ring

lemma nsq_pos (s : ℝ) : 0 < (1 - s) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (s - 1 / 2)]

lemma pv_ne_zero (s : ℝ) : pv s ≠ 0 := by
  intro h
  have := congrArg Complex.normSq h
  rw [normSq_pv, map_zero] at this
  linarith [nsq_pos s]

lemma sq_norm_pv (s : ℝ) : ‖pv s‖ ^ 2 = (1 - s) ^ 2 + s ^ 2 := by
  rw [Complex.sq_norm, normSq_pv]

lemma continuous_pv : Continuous pv := by
  unfold pv; fun_prop

/-- `Re(v − 1/v)` on the path. -/
lemma re_h_pv (s : ℝ) :
    (pv s - (pv s)⁻¹).re = -(2 * s * (1 - s) ^ 2) / ((1 - s) ^ 2 + s ^ 2) := by
  rw [sub_re, inv_re, normSq_pv, pv_re]
  have := nsq_pos s
  field_simp
  ring

lemma re_h_nonpos {s : ℝ} (hs : 0 ≤ s) : (pv s - (pv s)⁻¹).re ≤ 0 := by
  rw [re_h_pv]
  have := nsq_pos s
  apply div_nonpos_of_nonpos_of_nonneg _ this.le
  have : 0 ≤ 2 * s * (1 - s) ^ 2 := by positivity
  linarith

/-- The integrand `f(v) = v^{−(ν+1)} exp(L(v − 1/v))`. -/
noncomputable def fk (ν : ℕ) (L : ℝ) (v : ℂ) : ℂ := (v ^ (ν + 1))⁻¹ * cexp (L * (v - v⁻¹))

lemma norm_fk (ν : ℕ) (L : ℝ) (v : ℂ) :
    ‖fk ν L v‖ = (‖v‖ ^ (ν + 1))⁻¹ * Real.exp (L * (v - v⁻¹).re) := by
  rw [fk, norm_mul, norm_inv, norm_pow, Complex.norm_exp]
  congr 2
  simp [mul_re]

/-- `‖v(s)‖^{−(ν+1)} ≤ 2^{ν+2}/(1+s²)`. -/
lemma inv_norm_pv_pow_le {ν : ℕ} (hν : 1 ≤ ν) (s : ℝ) :
    (‖pv s‖ ^ (ν + 1))⁻¹ ≤ 2 ^ (ν + 2) / (1 + s ^ 2) := by
  have hsq := sq_norm_pv s
  have hn0 : 0 < ‖pv s‖ := norm_pos_iff.2 (pv_ne_zero s)
  have h1s : 0 < 1 + s ^ 2 := by positivity
  rcases le_or_gt 1 ‖pv s‖ with h | h
  · -- ‖v‖ ≥ 1: ‖v‖^(ν+1) ≥ ‖v‖² ≥ (1+s²)/3
    have hp : ‖pv s‖ ^ 2 ≤ ‖pv s‖ ^ (ν + 1) := by
      exact pow_le_pow_right₀ h (by omega)
    have h3 : (1 + s ^ 2) / 3 ≤ ‖pv s‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (s - 3 / 5)]
    have hpos : 0 < ‖pv s‖ ^ (ν + 1) := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ hpos h1s]
    have : (3 : ℝ) ≤ 2 ^ (ν + 2) := by
      calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (ν + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  · -- ‖v‖ < 1: then 0 < s < 1 and ‖v‖ ≥ 1/2
    have hs1 : s ^ 2 ≤ 1 := by
      have : ‖pv s‖ ^ 2 < 1 := by nlinarith
      rw [hsq] at this; nlinarith
    have hhalf : 1 / 2 ≤ ‖pv s‖ := by
      have : (1 / 2 : ℝ) ^ 2 ≤ ‖pv s‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (s - 1 / 2)]
      exact (pow_le_pow_iff_left₀ (by norm_num) hn0.le (by norm_num)).1 this
    have hp : (1 / 2 : ℝ) ^ (ν + 1) ≤ ‖pv s‖ ^ (ν + 1) := pow_le_pow_left₀ (by norm_num) hhalf _
    have hpos : 0 < (1 / 2 : ℝ) ^ (ν + 1) := by positivity
    calc (‖pv s‖ ^ (ν + 1))⁻¹ ≤ ((1 / 2 : ℝ) ^ (ν + 1))⁻¹ := inv_anti₀ hpos hp
      _ = 2 ^ (ν + 1) := by rw [one_div, inv_pow, inv_inv]
      _ ≤ 2 ^ (ν + 2) / (1 + s ^ 2) := by
        rw [le_div_iff₀ h1s, pow_succ 2 (ν + 1)]
        have : (0 : ℝ) < 2 ^ (ν + 1) := by positivity
        nlinarith

lemma norm_neg_one_add_I : ‖(-1 + I : ℂ)‖ ≤ 2 := by
  have : ‖(-1 + I : ℂ)‖ ≤ ‖(-1 : ℂ)‖ + ‖I‖ := norm_add_le _ _
  simp at this; linarith

/-- The integrand on the path. -/
noncomputable def Gk (ν : ℕ) (L : ℝ) (s : ℝ) : ℂ := (-1 + I) * fk ν L (pv s)

lemma continuous_Gk (ν : ℕ) (L : ℝ) : Continuous (Gk ν L) := by
  unfold Gk fk
  have hc := continuous_pv
  have hne : ∀ s, pv s ≠ 0 := pv_ne_zero
  refine continuous_const.mul ((((hc.pow _).inv₀ fun s => pow_ne_zero _ (hne s))).mul ?_)
  exact Complex.continuous_exp.comp (continuous_const.mul (hc.sub (hc.inv₀ hne)))

lemma norm_Gk_le {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {s : ℝ} (hs : 0 ≤ s) :
    ‖Gk ν L s‖ ≤ 2 * (2 ^ (ν + 2) / (1 + s ^ 2)) := by
  rw [Gk, norm_mul, norm_fk]
  have he : Real.exp (L * (pv s - (pv s)⁻¹).re) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hL (re_h_nonpos hs))
  have h1 := inv_norm_pv_pow_le hν s
  have h0 : 0 ≤ (‖pv s‖ ^ (ν + 1))⁻¹ := by positivity
  calc ‖(-1 + I : ℂ)‖ * ((‖pv s‖ ^ (ν + 1))⁻¹ * Real.exp (L * (pv s - (pv s)⁻¹).re))
      ≤ 2 * ((‖pv s‖ ^ (ν + 1))⁻¹ * 1) := by
        gcongr
        · exact norm_neg_one_add_I
    _ ≤ 2 * (2 ^ (ν + 2) / (1 + s ^ 2)) := by rw [mul_one]; gcongr

lemma integrableOn_Gk {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) : IntegrableOn (Gk ν L) (Ioi 0) := by
  have hmaj : Integrable fun s : ℝ => 2 * (2 ^ (ν + 2) * (1 + s ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.const_mul _).const_mul _
  refine Integrable.mono' hmaj.integrableOn (continuous_Gk ν L).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  have := norm_Gk_le hν hL (le_of_lt hs)
  simpa [div_eq_mul_inv] using this

/-- `A_ν(L) = ∫₀^∞ (−1+i) f(v(s)) ds`. -/
noncomputable def Ak (ν : ℕ) (L : ℝ) : ℂ := ∫ s in Ioi (0 : ℝ), Gk ν L s

/-- `I_ν(L) = Im A_ν(L)/π`. -/
noncomputable def Ik (ν : ℕ) (L : ℝ) : ℝ := (Ak ν L).im / π


/-! ### Elementary integrals -/

lemma integral_exp_neg_le {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    ∫ s in a..b, Real.exp (-c * s) ≤ Real.exp (-c * a) / c := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun s => -Real.exp (-c * s) / c) (Real.exp (-c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s => -c * s) (-c) x := by
      simpa using (hasDerivAt_id x).const_mul (-c)
    have h2 := (h1.exp.neg).div_const c
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  have : 0 < Real.exp (-c * b) / c := by positivity
  linarith [show -Real.exp (-c * b) / c - -Real.exp (-c * a) / c =
    Real.exp (-c * a) / c - Real.exp (-c * b) / c by ring]

lemma integral_Ioi_exp_neg {c a : ℝ} (hc : 0 < c) :
    ∫ s in Ioi a, Real.exp (-c * s) = Real.exp (-c * a) / c := by
  have hd : ∀ x ∈ Ici a, HasDerivAt (fun s => -Real.exp (-c * s) / c) (Real.exp (-c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s => -c * s) (-c) x := by
      simpa using (hasDerivAt_id x).const_mul (-c)
    have h2 := (h1.exp.neg).div_const c
    convert h2 using 1
    field_simp
  have hint : IntegrableOn (fun s => Real.exp (-c * s)) (Ioi a) := exp_neg_integrableOn_Ioi a hc
  have hlim : Tendsto (fun s => -Real.exp (-c * s) / c) atTop (𝓝 0) := by
    have : Tendsto (fun s => Real.exp (-c * s)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (this.neg).div_const c
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  ring

lemma integral_mul_exp_neg_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ u in (0 : ℝ)..b, u * Real.exp (-a * u ^ 2) ≤ 1 / (2 * a) := by
  have hd : ∀ x ∈ uIcc 0 b, HasDerivAt (fun u => -Real.exp (-a * u ^ 2) / (2 * a))
      (x * Real.exp (-a * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun u => -a * u ^ 2) (-a * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-a))
    have h2 := (h1.exp.neg).div_const (2 * a)
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have : 0 < Real.exp (-a * b ^ 2) / (2 * a) := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
  have e : -Real.exp (-a * b ^ 2) / (2 * a) - -1 / (2 * a) =
      1 / (2 * a) - Real.exp (-a * b ^ 2) / (2 * a) := by ring
  rw [e]; linarith

lemma integral_cube_mul_exp_neg_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ u in (0 : ℝ)..b, u ^ 3 * Real.exp (-a * u ^ 2) ≤ 1 / (2 * a ^ 2) := by
  have hd : ∀ x ∈ uIcc 0 b, HasDerivAt (fun u => -(a * u ^ 2 + 1) * Real.exp (-a * u ^ 2) / (2 * a ^ 2))
      (x ^ 3 * Real.exp (-a * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun u => -a * u ^ 2) (-a * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-a))
    have h0 : HasDerivAt (fun u => -(a * u ^ 2 + 1)) (-(a * (2 * x))) x := by
      have h := ((hasDerivAt_pow 2 x).const_mul a).add_const 1
      have h' := h.neg
      convert h' using 1
      push_cast; ring
    have h2 := (h0.mul h1.exp).div_const (2 * a ^ 2)
    convert h2 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have : 0 ≤ (a * b ^ 2 + 1) * Real.exp (-a * b ^ 2) / (2 * a ^ 2) := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
    Real.exp_zero, mul_one]
  have e : -(a * b ^ 2 + 1) * Real.exp (-a * b ^ 2) / (2 * a ^ 2) - -1 / (2 * a ^ 2) =
      1 / (2 * a ^ 2) - (a * b ^ 2 + 1) * Real.exp (-a * b ^ 2) / (2 * a ^ 2) := by ring
  rw [e]; linarith

lemma integral_symm_abs' {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in -a..a, g |t| = 2 * ∫ t in (0 : ℝ)..a, g t := by
  have hc : Continuous fun t => g |t| := hg.comp continuous_abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..a, g |t| = ∫ t in (0 : ℝ)..a, g t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le ha] at ht
    simp [abs_of_nonneg ht.1]
  have h2 : ∫ t in -a..(0 : ℝ), g |t| = ∫ t in (0 : ℝ)..a, g t := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun t => g |t|)
    simp only [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le ha] at ht
    simp [abs_of_nonneg ht.1]
  rw [h1, h2]; ring

/-- `‖e^a − e^b‖ ≤ ‖a − b‖ e^m` whenever `Re a, Re b ≤ m`. -/
lemma norm_cexp_sub_cexp_le {a b : ℂ} {m : ℝ} (ha : a.re ≤ m) (hb : b.re ≤ m) :
    ‖cexp a - cexp b‖ ≤ ‖a - b‖ * Real.exp m := by
  set g : ℝ → ℂ := fun t => cexp (b + t * (a - b)) with hg
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g ((a - b) * cexp (b + t * (a - b))) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => b + (t : ℂ) * (a - b)) (a - b) t := by
      have := ((hasDerivAt_id t).ofReal_comp).mul_const (a - b)
      simpa using this.const_add b
    have h2 := h1.cexp
    rw [mul_comm]
    exact h2.hasDerivWithinAt
  have hb' : ∀ t ∈ Ico (0 : ℝ) 1, ‖(a - b) * cexp (b + t * (a - b))‖ ≤ ‖a - b‖ * Real.exp m := by
    intro t ht
    rw [norm_mul, Complex.norm_exp]
    gcongr
    have : (b + t * (a - b)).re = (1 - t) * b.re + t * a.re := by simp; ring
    rw [this]
    nlinarith [ht.1, ht.2]
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb' 1 ⟨zero_le_one, le_rfl⟩
  simpa [hg] using this


/-! ### The two outer pieces -/

lemma re_h_le_left {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : (pv s - (pv s)⁻¹).re ≤ -s / 2 := by
  rw [re_h_pv]
  have hp := nsq_pos s
  rw [div_le_iff₀ hp]
  nlinarith [mul_nonneg h0 (sq_nonneg (1 - s)), mul_nonneg h0 (by nlinarith : (0 : ℝ) ≤ 3 * (1 - s) ^ 2 - s ^ 2)]

lemma re_h_le_right {s : ℝ} (h : 3 / 2 ≤ s) : (pv s - (pv s)⁻¹).re ≤ -1 / 6 := by
  rw [re_h_pv]
  have hp := nsq_pos s
  rw [div_le_iff₀ hp]
  have ht : 1 / 2 ≤ s - 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ s - 1 - 1 / 2) (by linarith : (0 : ℝ) ≤ s - 1))
    (by linarith : (0 : ℝ) ≤ s - 1), sq_nonneg (s - 1)]

lemma norm_Gk_left {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    ‖Gk ν L s‖ ≤ 2 ^ (ν + 3) * Real.exp (-(L / 2) * s) := by
  rw [Gk, norm_mul, norm_fk]
  have he : Real.exp (L * (pv s - (pv s)⁻¹).re) ≤ Real.exp (-(L / 2) * s) := by
    apply Real.exp_le_exp.2
    have := re_h_le_left h0 h1
    nlinarith
  have h2 : (‖pv s‖ ^ (ν + 1))⁻¹ ≤ 2 ^ (ν + 2) := by
    refine (inv_norm_pv_pow_le hν s).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) < 2 ^ (ν + 2) := by positivity
    nlinarith [sq_nonneg s]
  calc ‖(-1 + I : ℂ)‖ * ((‖pv s‖ ^ (ν + 1))⁻¹ * Real.exp (L * (pv s - (pv s)⁻¹).re))
      ≤ 2 * (2 ^ (ν + 2) * Real.exp (-(L / 2) * s)) := by
        gcongr
        · exact norm_neg_one_add_I
    _ = 2 ^ (ν + 3) * Real.exp (-(L / 2) * s) := by ring

lemma norm_Gk_right {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {s : ℝ} (h : 3 / 2 ≤ s) :
    ‖Gk ν L s‖ ≤ 2 ^ (ν + 3) * Real.exp (-L / 6) * (1 + s ^ 2)⁻¹ := by
  rw [Gk, norm_mul, norm_fk]
  have he : Real.exp (L * (pv s - (pv s)⁻¹).re) ≤ Real.exp (-L / 6) := by
    apply Real.exp_le_exp.2
    have := re_h_le_right h
    nlinarith
  have h2 := inv_norm_pv_pow_le hν s
  calc ‖(-1 + I : ℂ)‖ * ((‖pv s‖ ^ (ν + 1))⁻¹ * Real.exp (L * (pv s - (pv s)⁻¹).re))
      ≤ 2 * (2 ^ (ν + 2) / (1 + s ^ 2) * Real.exp (-L / 6)) := by
        gcongr
        · exact norm_neg_one_add_I
    _ = 2 ^ (ν + 3) * Real.exp (-L / 6) * (1 + s ^ 2)⁻¹ := by ring

lemma piece_left {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 < L) :
    ‖∫ s in (0 : ℝ)..1 / 2, Gk ν L s‖ ≤ 2 ^ (ν + 4) / L := by
  have hb : ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖Gk ν L s‖ ≤ 2 ^ (ν + 3) * Real.exp (-(L / 2) * s) := by
    intro s hs
    exact norm_Gk_left hν hL.le hs.1.le hs.2
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num)
    (Eventually.of_forall hb) (by apply Continuous.intervalIntegrable; fun_prop)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 := integral_exp_neg_le (c := L / 2) (a := 0) (b := 1 / 2) (by positivity) (by norm_num)
  simp only [mul_zero, Real.exp_zero] at h2
  calc 2 ^ (ν + 3) * ∫ s in (0 : ℝ)..1 / 2, Real.exp (-(L / 2) * s)
      ≤ 2 ^ (ν + 3) * (1 / (L / 2)) := by gcongr
    _ = 2 ^ (ν + 4) / L := by field_simp; ring

lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le hx
  linarith [Real.add_one_le_exp x]

lemma piece_right {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 < L) :
    ‖∫ s in Ioi (3 / 2 : ℝ), Gk ν L s‖ ≤ 6 * π * 2 ^ (ν + 3) / L := by
  have hb : ∀ᵐ s ∂(volume.restrict (Ioi (3 / 2 : ℝ))),
      ‖Gk ν L s‖ ≤ 2 ^ (ν + 3) * Real.exp (-L / 6) * (1 + s ^ 2)⁻¹ := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    exact norm_Gk_right hν hL.le (le_of_lt hs)
  have h1 := norm_integral_le_of_norm_le
    ((integrable_inv_one_add_sq.const_mul (2 ^ (ν + 3) * Real.exp (-L / 6))).integrableOn) hb
  refine h1.trans ?_
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
  have ha : 0 ≤ π / 2 - Real.arctan (3 / 2) := by
    linarith [Real.arctan_lt_pi_div_two (3 / 2)]
  have ha' : π / 2 - Real.arctan (3 / 2) ≤ π := by
    have : 0 ≤ Real.arctan (3 / 2) := Real.arctan_nonneg.2 (by norm_num)
    linarith [Real.pi_pos]
  have he : Real.exp (-L / 6) ≤ 6 / L := by
    have := exp_neg_le_inv (x := L / 6) (by positivity)
    rw [neg_div]; convert this using 1; field_simp
  have hpos : (0 : ℝ) < 2 ^ (ν + 3) := by positivity
  calc 2 ^ (ν + 3) * Real.exp (-L / 6) * (π / 2 - Real.arctan (3 / 2))
      ≤ 2 ^ (ν + 3) * (6 / L) * π := by gcongr
    _ = 6 * π * 2 ^ (ν + 3) / L := by ring

/-! ### The saddle piece -/

/-- `z(u) = i + u(1 − i)`, i.e. `v(1 − u)`. -/
noncomputable def zu (u : ℝ) : ℂ := I + (u : ℂ) * (1 - I)

lemma pv_one_sub (u : ℝ) : pv (1 - u) = zu u := by
  apply Complex.ext <;> simp [pv, zu]; ring

lemma normSq_zu (u : ℝ) : Complex.normSq (zu u) = u ^ 2 + (1 - u) ^ 2 := by
  rw [← pv_one_sub, normSq_pv]; ring

lemma zu_ne_zero (u : ℝ) : zu u ≠ 0 := by rw [← pv_one_sub]; exact pv_ne_zero _

lemma zu_sub_I (u : ℝ) : zu u - I = (u : ℂ) * (1 - I) := by unfold zu; ring

lemma sq_zu_sub_I (u : ℝ) : (zu u - I) ^ 2 = -2 * I * (u : ℂ) ^ 2 := by
  rw [zu_sub_I]; ring_nf; rw [I_sq]; ring

/-- The exact saddle identity `z − 1/z = 2i + (z − i)²/z`. -/
lemma sub_inv_eq (z : ℂ) (hz : z ≠ 0) : z - z⁻¹ = 2 * I + (z - I) ^ 2 / z := by
  field_simp
  ring_nf
  rw [I_sq]; ring

lemma re_phi_le {u : ℝ} (hu : |u| ≤ 1 / 2) {L : ℝ} (hL : 0 ≤ L) :
    (L * ((zu u - I) ^ 2 / zu u)).re ≤ -(2 * L / 5) * u ^ 2 := by
  have h := re_h_pv (1 - u)
  rw [pv_one_sub, sub_inv_eq _ (zu_ne_zero u)] at h
  simp only [add_re, mul_re, re_ofNat, I_re, im_ofNat, I_im, mul_zero, sub_zero, mul_one,
    zero_add] at h
  have hu1 : -(1 / 2) ≤ u ∧ u ≤ 1 / 2 := abs_le.1 hu
  have hre : (L * ((zu u - I) ^ 2 / zu u)).re = L * ((zu u - I) ^ 2 / zu u).re := by
    simp [mul_re]
  rw [hre]
  have hn : 0 < (1 - (1 - u)) ^ 2 + (1 - u) ^ 2 := nsq_pos _
  have key : ((zu u - I) ^ 2 / zu u).re ≤ -(2 / 5) * u ^ 2 := by
    rw [h, div_le_iff₀ hn]
    have : (1 - (1 - u)) = u := by ring
    rw [this]
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (by nlinarith : (0 : ℝ) ≤ 5 * (1 - u) - (u ^ 2 + (1 - u) ^ 2))]
  nlinarith

lemma norm_phi_add_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ‖(zu u - I) ^ 2 / zu u + 2 * (u : ℂ) ^ 2‖ ≤ 4 * |u| ^ 3 := by
  have hz := zu_ne_zero u
  have hzn : 0 < ‖zu u‖ := norm_pos_iff.2 hz
  have e : (zu u - I) ^ 2 / zu u + 2 * (u : ℂ) ^ 2 = 2 * (u : ℂ) ^ 2 * (zu u - I) / zu u := by
    rw [sq_zu_sub_I]
    field_simp
    unfold zu; ring
  rw [e, norm_div, norm_mul, norm_mul, zu_sub_I, norm_mul]
  have h1 : ‖(1 - I : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
  have h2 : 1 / 2 ≤ ‖zu u‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_zu]; nlinarith [sq_nonneg (u - 1 / 2)]
  rw [div_le_iff₀ hzn]
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
  have hu0 : 0 ≤ |u| := abs_nonneg u
  -- square both sides
  have hA : 0 ≤ 2 * |u| ^ 2 * (|u| * ‖(1 - I : ℂ)‖) := by positivity
  have hB : 0 ≤ 4 * |u| ^ 3 * ‖zu u‖ := by positivity
  refine (pow_le_pow_iff_left₀ hA hB (two_ne_zero)).1 ?_
  have : (2 * |u| ^ 2 * (|u| * ‖(1 - I : ℂ)‖)) ^ 2 = 8 * |u| ^ 6 := by
    rw [show (2 * |u| ^ 2 * (|u| * ‖(1 - I : ℂ)‖)) ^ 2 = 4 * |u| ^ 6 * ‖(1 - I : ℂ)‖ ^ 2 by ring, h1]; ring
  rw [this, show (4 * |u| ^ 3 * ‖zu u‖) ^ 2 = 16 * |u| ^ 6 * ‖zu u‖ ^ 2 by ring]
  have : 0 ≤ |u| ^ 6 := by positivity
  nlinarith

lemma norm_zu_le {u : ℝ} (hu : |u| ≤ 1 / 2) : 1 / 2 ≤ ‖zu u‖ ∧ ‖zu u‖ ≤ 2 := by
  have hu1 := abs_le.1 hu
  have hsq : ‖zu u‖ ^ 2 = u ^ 2 + (1 - u) ^ 2 := by rw [Complex.sq_norm, normSq_zu]
  have h0 := norm_nonneg (zu u)
  constructor
  · have : (1 / 2 : ℝ) ^ 2 ≤ ‖zu u‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (u - 1 / 2)]
    exact (pow_le_pow_iff_left₀ (by norm_num) h0 (by norm_num)).1 this
  · have : ‖zu u‖ ^ 2 ≤ 2 ^ 2 := by rw [hsq]; nlinarith
    exact (pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num)).1 this

lemma norm_inv_pow_sub_le (m : ℕ) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ‖(zu u ^ m)⁻¹ - (I ^ m)⁻¹‖ ≤ m * 2 ^ (2 * m + 1) * |u| := by
  obtain ⟨hz1, hz2⟩ := norm_zu_le hu
  have hz := zu_ne_zero u
  have e : (zu u ^ m)⁻¹ - (I ^ m)⁻¹ = (I ^ m - zu u ^ m) / (zu u ^ m * I ^ m) := by
    field_simp
  rw [e, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow, mul_one]
  have hg := geom_sum₂_mul I (zu u) m
  rw [← hg, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range m, I ^ i * zu u ^ (m - 1 - i)‖ ≤ m * 2 ^ m := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ Finset.range m, ‖I ^ i * zu u ^ (m - 1 - i)‖ ≤ 2 ^ m := by
      intro i _
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow, one_mul]
      calc ‖zu u‖ ^ (m - 1 - i) ≤ 2 ^ (m - 1 - i) := pow_le_pow_left₀ (norm_nonneg _) hz2 _
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hIz : ‖I - zu u‖ ≤ 2 * |u| := by
    rw [show I - zu u = -((u : ℂ) * (1 - I)) by unfold zu; ring, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 - I : ℂ)‖ ≤ 2 := by
      have := norm_sub_le (1 : ℂ) I; simp at this; linarith
    nlinarith [abs_nonneg u]
  have hden : (1 / 2 : ℝ) ^ m ≤ ‖zu u‖ ^ m := pow_le_pow_left₀ (by norm_num) hz1 _
  have hden0 : (0 : ℝ) < (1 / 2) ^ m := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hden0 hden)]
  calc ‖∑ i ∈ Finset.range m, I ^ i * zu u ^ (m - 1 - i)‖ * ‖I - zu u‖
      ≤ (m * 2 ^ m) * (2 * |u|) := by gcongr
    _ = m * 2 ^ (2 * m + 1) * |u| * (1 / 2) ^ m := by
        rw [show 2 * m + 1 = m + m + 1 by ring, pow_add, pow_add, one_div, inv_pow]
        field_simp
    _ ≤ m * 2 ^ (2 * m + 1) * |u| * ‖zu u‖ ^ m := by gcongr


/-- The Gaussian model of the integrand near the saddle (in the variable `u = 1 − s`). -/
noncomputable def Mk (ν : ℕ) (L u : ℝ) : ℂ :=
  (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (Real.exp (-2 * L * u ^ 2) : ℂ)

lemma Gk_one_sub (ν : ℕ) (L u : ℝ) : Gk ν L (1 - u) =
    (-1 + I) * (zu u ^ (ν + 1))⁻¹ * (cexp (2 * I * L) * cexp (L * ((zu u - I) ^ 2 / zu u))) := by
  rw [Gk, fk, pv_one_sub, sub_inv_eq _ (zu_ne_zero u), ← Complex.exp_add]
  ring_nf

lemma norm_cexp_two_I_mul (L : ℝ) : ‖cexp (2 * I * L)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Pointwise comparison with the Gaussian model, `|u| ≤ 1/2`. -/
lemma norm_Gk_sub_Mk (ν : ℕ) {L : ℝ} (hL : 0 ≤ L) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ‖Gk ν L (1 - u) - Mk ν L u‖ ≤
      2 * ((ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1) * |u| + 4 * L * |u| ^ 3) *
        Real.exp (-(2 * L / 5) * |u| ^ 2) := by
  set P := (zu u ^ (ν + 1))⁻¹
  set P0 := (I ^ (ν + 1))⁻¹
  set E1 := cexp (L * ((zu u - I) ^ 2 / zu u))
  set E0 : ℂ := (Real.exp (-2 * L * u ^ 2) : ℂ)
  have e : Gk ν L (1 - u) - Mk ν L u = (-1 + I) * cexp (2 * I * L) * ((P - P0) * E1 + P0 * (E1 - E0)) := by
    rw [Gk_one_sub]; unfold Mk; ring
  rw [e, norm_mul, norm_mul, norm_cexp_two_I_mul, mul_one]
  have hm : -(2 * L / 5) * |u| ^ 2 = -(2 * L / 5) * u ^ 2 := by rw [sq_abs]
  have hE1 : ‖E1‖ ≤ Real.exp (-(2 * L / 5) * |u| ^ 2) := by
    rw [Complex.norm_exp, hm]
    exact Real.exp_le_exp.2 (by have := re_phi_le hu hL; linarith)
  have hP0 : ‖P0‖ = 1 := by simp [P0]
  have hE : ‖E1 - E0‖ ≤ L * (4 * |u| ^ 3) * Real.exp (-(2 * L / 5) * |u| ^ 2) := by
    have hE0 : E0 = cexp ((-2 * L * u ^ 2 : ℝ) : ℂ) := by simp [E0, Complex.ofReal_exp]
    rw [hE0]
    refine (norm_cexp_sub_cexp_le (m := -(2 * L / 5) * |u| ^ 2) ?_ ?_).trans ?_
    · rw [hm]; have := re_phi_le hu hL; linarith
    · simp only [Complex.ofReal_re, hm]
      nlinarith [sq_nonneg u]
    · gcongr
      have : L * ((zu u - I) ^ 2 / zu u) - ((-2 * L * u ^ 2 : ℝ) : ℂ) =
          (L : ℂ) * ((zu u - I) ^ 2 / zu u + 2 * (u : ℂ) ^ 2) := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL]
      gcongr
      exact norm_phi_add_le hu
  have hPP := norm_inv_pow_sub_le (ν + 1) hu
  calc ‖(-1 + I : ℂ)‖ * ‖(P - P0) * E1 + P0 * (E1 - E0)‖
      ≤ 2 * (‖P - P0‖ * ‖E1‖ + ‖P0‖ * ‖E1 - E0‖) := by
        gcongr
        · exact norm_neg_one_add_I
        · refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
    _ ≤ 2 * (((ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1) * |u|) * Real.exp (-(2 * L / 5) * |u| ^ 2) +
          1 * (L * (4 * |u| ^ 3) * Real.exp (-(2 * L / 5) * |u| ^ 2))) := by
        rw [hP0]; gcongr
    _ = _ := by ring

/-- Splitting an integral over `Ioi a`. -/
lemma integral_Ioi_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioi a)) :
    ∫ x in Ioi a, f x = (∫ x in a..b, f x) + ∫ x in Ioi b, f x := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hab, setIntegral_union _ measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hab)),
    intervalIntegral.integral_of_le hab]
  rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx'.out (not_lt.2 hx.2)

/-- The Gaussian window: `|∫_{−1/2}^{1/2} e^{−2Lu²} du − √(π/(2L))| ≤ 2/L`. -/
lemma gauss_window {L : ℝ} (hL : 0 < L) :
    |(∫ u in -(1 / 2 : ℝ)..1 / 2, Real.exp (-2 * L * u ^ 2)) - √(π / (2 * L))| ≤ 2 / L := by
  have hsym := integral_symm_abs' (g := fun t => Real.exp (-2 * L * t ^ 2)) (by fun_prop)
    (a := 1 / 2) (by norm_num)
  simp only [sq_abs] at hsym
  rw [hsym]
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-2 * L * u ^ 2)) (Ioi 0) := by
    have := (integrable_exp_neg_mul_sq (b := 2 * L) (by positivity)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi
  have hsplit := integral_Ioi_split (f := fun u : ℝ => Real.exp (-2 * L * u ^ 2)) (a := 0)
    (b := 1 / 2) (by norm_num) hint
  have hg := integral_gaussian_Ioi (2 * L)
  have hg' : ∫ x in Ioi (0 : ℝ), Real.exp (-2 * L * x ^ 2) = √(π / (2 * L)) / 2 := by
    rw [← hg]; congr 1; funext x; ring_nf
  rw [hg'] at hsplit
  simp only at hsplit
  set T := ∫ x in Ioi (1 / 2 : ℝ), Real.exp (-2 * L * x ^ 2)
  have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Ioi (fun x _ => (Real.exp_pos _).le)
  have hT1 : T ≤ 1 / L := by
    have h1 : T ≤ ∫ x in Ioi (1 / 2 : ℝ), Real.exp (-L * x) := by
      refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi (by norm_num)))
        (exp_neg_integrableOn_Ioi _ hL) measurableSet_Ioi (fun x hx => ?_)
      apply Real.exp_le_exp.2
      have hx' : (1 / 2 : ℝ) < x := hx
      nlinarith [mul_pos (mul_pos hL (by linarith : (0:ℝ) < x)) (by linarith : (0:ℝ) < 2 * x - 1)]
    rw [integral_Ioi_exp_neg hL] at h1
    refine h1.trans ?_
    have := exp_neg_le_inv (x := L * (1 / 2)) (by positivity)
    have h2 : Real.exp (-L * (1 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact div_le_div_of_nonneg_right h2 hL.le
  have h2L : 2 / L = 2 * (1 / L) := by ring
  rw [abs_le]
  constructor <;> linarith

/-- The saddle piece. -/
lemma piece_mid {ν : ℕ} {L : ℝ} (hL : 0 < L) :
    ‖(∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s) -
        (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)‖ ≤
      (5 * ((ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1)) + 54) / L := by
  set K : ℝ := (ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsub : ∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s = ∫ u in -(1 / 2 : ℝ)..1 / 2, Gk ν L (1 - u) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s => Gk ν L s) 1]; norm_num
  have hGc : Continuous fun u : ℝ => Gk ν L (1 - u) :=
    (continuous_Gk ν L).comp (continuous_const.sub continuous_id)
  have hMc : Continuous fun u : ℝ => Mk ν L u := by unfold Mk; fun_prop
  have hMint : ∫ u in -(1 / 2 : ℝ)..1 / 2, Mk ν L u =
      (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) *
        ((∫ u in -(1 / 2 : ℝ)..1 / 2, Real.exp (-2 * L * u ^ 2) : ℝ) : ℂ) := by
    unfold Mk
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  set c : ℂ := (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L)
  have hc : ‖c‖ ≤ 2 := by
    simp only [c, norm_mul, norm_inv, norm_pow, Complex.norm_I, one_pow, inv_one, mul_one,
      norm_cexp_two_I_mul]
    exact norm_neg_one_add_I
  have e : (∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s) - c * (√(π / (2 * L)) : ℂ) =
      (∫ u in -(1 / 2 : ℝ)..1 / 2, (Gk ν L (1 - u) - Mk ν L u)) +
        c * ((((∫ u in -(1 / 2 : ℝ)..1 / 2, Real.exp (-2 * L * u ^ 2)) - √(π / (2 * L)) : ℝ)) : ℂ) := by
    rw [hsub, intervalIntegral.integral_sub (hGc.intervalIntegrable _ _) (hMc.intervalIntegrable _ _),
      hMint]
    push_cast; ring
  rw [e]
  -- the Gaussian-model error
  set a : ℝ := 2 * L / 5 with ha
  have ha0 : 0 < a := by positivity
  set B : ℝ → ℝ := fun t => 2 * (K * t + 4 * L * t ^ 3) * Real.exp (-a * t ^ 2) with hB
  have hBc : Continuous B := by rw [hB]; fun_prop
  have h1 : ‖∫ u in -(1 / 2 : ℝ)..1 / 2, (Gk ν L (1 - u) - Mk ν L u)‖ ≤
      ∫ u in -(1 / 2 : ℝ)..1 / 2, B |u| := by
    refine intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num)
      (Eventually.of_forall fun u hu => ?_) ((hBc.comp continuous_abs).intervalIntegrable _ _)
    have hu' : |u| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
    have := norm_Gk_sub_Mk ν hL.le hu'
    simpa [hB, ha, hK] using this
  have h2 : ∫ u in -(1 / 2 : ℝ)..1 / 2, B |u| = 2 * ∫ u in (0 : ℝ)..1 / 2, B u :=
    integral_symm_abs' hBc (by norm_num)
  have h3 : ∫ u in (0 : ℝ)..1 / 2, B u ≤ K / a + 4 * L / a ^ 2 := by
    have eB : ∀ t, B t = (2 * K) * (t * Real.exp (-a * t ^ 2)) + (8 * L) * (t ^ 3 * Real.exp (-a * t ^ 2)) := by
      intro t; simp only [hB]; ring
    simp_rw [eB]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have i1 := integral_mul_exp_neg_sq_le ha0 (b := 1 / 2) (by norm_num)
    have i2 := integral_cube_mul_exp_neg_sq_le ha0 (b := 1 / 2) (by norm_num)
    have : 2 * K * (1 / (2 * a)) + 8 * L * (1 / (2 * a ^ 2)) = K / a + 4 * L / a ^ 2 := by
      field_simp; ring
    rw [← this]
    gcongr
  have h4 : ‖c * ((((∫ u in -(1 / 2 : ℝ)..1 / 2, Real.exp (-2 * L * u ^ 2)) - √(π / (2 * L)) : ℝ)) : ℂ)‖
      ≤ 2 * (2 / L) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact gauss_window hL
  have h5 : 2 * (K / a + 4 * L / a ^ 2) + 2 * (2 / L) = (5 * K + 54) / L := by
    rw [ha]; field_simp; ring
  have h1' : ‖∫ u in -(1 / 2 : ℝ)..1 / 2, (Gk ν L (1 - u) - Mk ν L u)‖ ≤
      2 * (K / a + 4 * L / a ^ 2) := h1.trans (by rw [h2]; linarith [h3])
  rw [← h5]
  exact (norm_add_le _ _).trans (add_le_add h1' h4)


/-! ### Assembly -/

/-- The constant in the kernel asymptotic. -/
noncomputable def Ck (ν : ℕ) : ℝ :=
  2 ^ (ν + 4) + 6 * π * 2 ^ (ν + 3) + (5 * ((ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1)) + 54)

lemma Ck_nonneg (ν : ℕ) : 0 ≤ Ck ν := by unfold Ck; positivity

/-- **Saddle-point asymptotic of `A_ν`**: `A_ν(L) = (−1+i) i^{−(ν+1)} e^{2iL} √(π/(2L)) + O(1/L)`. -/
theorem Ak_asymp {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 < L) :
    ‖Ak ν L - (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)‖ ≤ Ck ν / L := by
  have hint := integrableOn_Gk hν hL.le
  have hsplit := integral_Ioi_split (f := Gk ν L) (a := 0) (b := 3 / 2) (by norm_num) hint
  have hadj : ∫ s in (0 : ℝ)..3 / 2, Gk ν L s =
      (∫ s in (0 : ℝ)..1 / 2, Gk ν L s) + ∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s :=
    (intervalIntegral.integral_add_adjacent_intervals ((continuous_Gk ν L).intervalIntegrable _ _)
      ((continuous_Gk ν L).intervalIntegrable _ _)).symm
  unfold Ak
  rw [hsplit, hadj]
  set M := (-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)
  have e : (∫ s in (0 : ℝ)..1 / 2, Gk ν L s) + (∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s) +
      (∫ s in Ioi (3 / 2 : ℝ), Gk ν L s) - M =
      (∫ s in (0 : ℝ)..1 / 2, Gk ν L s) + ((∫ s in (1 / 2 : ℝ)..3 / 2, Gk ν L s) - M) +
      (∫ s in Ioi (3 / 2 : ℝ), Gk ν L s) := by ring
  rw [e]
  have h1 := piece_left hν hL
  have h2 := piece_mid (ν := ν) hL
  have h3 := piece_right hν hL
  have : Ck ν / L = 2 ^ (ν + 4) / L + (5 * ((ν + 1 : ℕ) * 2 ^ (2 * (ν + 1) + 1)) + 54) / L +
      6 * π * 2 ^ (ν + 3) / L := by unfold Ck; ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)

lemma norm_lead_le (ν : ℕ) (L : ℝ) :
    ‖(-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)‖ ≤ 2 * √(π / (2 * L)) := by
  rw [norm_mul, norm_mul, norm_mul, norm_cexp_two_I_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [norm_inv, norm_pow, Complex.norm_I, one_pow, inv_one, mul_one]
  gcongr
  exact norm_neg_one_add_I

/-- **Kernel bound**: `|I_ν(L)| ≤ (2√π + C_ν) L^{−1/2}` for `L ≥ 1`. -/
theorem Ik_bound {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 1 ≤ L) :
    |Ik ν L| ≤ (2 * √π + Ck ν) / √L := by
  have hL0 : 0 < L := by linarith
  have hsL : 0 < √L := Real.sqrt_pos.2 hL0
  have h := Ak_asymp hν hL0
  have hA : ‖Ak ν L‖ ≤ 2 * √(π / (2 * L)) + Ck ν / L := by
    have := norm_sub_norm_le (Ak ν L)
      ((-1 + I) * (I ^ (ν + 1))⁻¹ * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ))
    linarith [norm_lead_le ν L]
  have hs1 : √(π / (2 * L)) ≤ √π / √L := by
    rw [← Real.sqrt_div Real.pi_pos.le]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left Real.pi_pos.le hL0 (by linarith)
  have hs2 : Ck ν / L ≤ Ck ν / √L := by
    apply div_le_div_of_nonneg_left (Ck_nonneg ν) hsL
    have : √L ≤ L := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    exact this
  have hIm : |Ik ν L| ≤ ‖Ak ν L‖ := by
    unfold Ik
    rw [abs_div, abs_of_pos Real.pi_pos]
    calc |(Ak ν L).im| / π ≤ |(Ak ν L).im| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos (by linarith [Real.two_le_pi])
      _ ≤ ‖Ak ν L‖ := by rw [div_one]; exact abs_im_le_norm _
  calc |Ik ν L| ≤ 2 * √(π / (2 * L)) + Ck ν / L := hIm.trans hA
    _ ≤ 2 * (√π / √L) + Ck ν / √L := by gcongr
    _ = (2 * √π + Ck ν) / √L := by ring

lemma lead_twelve (L : ℝ) :
    (-1 + I) * (I ^ (12 + 1))⁻¹ * cexp (2 * I * L) = (1 + I) * cexp (2 * I * L) := by
  have : I ^ (12 + 1) = I := by
    rw [show 12 + 1 = 4 * 3 + 1 by rfl, pow_succ, pow_mul, I_pow_four]; simp
  rw [this, inv_I]
  ring_nf; rw [I_sq]; ring

lemma sqrt_identity {L : ℝ} (hL : 0 < L) : √(π / (2 * L)) / π = (√2 / 2) / √(π * L) := by
  have hp := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hpL : 0 < √(π * L) := Real.sqrt_pos.2 (by positivity)
  have hsp : 0 < √π := Real.sqrt_pos.2 hp
  rw [Real.sqrt_div hp.le, Real.sqrt_mul (by norm_num), Real.sqrt_mul hp.le]
  have hsL : 0 < √L := Real.sqrt_pos.2 hL
  have e1 : √π * √π = π := Real.mul_self_sqrt hp.le
  have e2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [e1, e2]

/-- **Phase asymptotic for `ν = 12`**: `|I₁₂(L) − cos(2L − π/4)/√(πL)| ≤ C₁₂/(πL)`. -/
theorem Ik_asymp_twelve {L : ℝ} (hL : 0 < L) :
    |Ik 12 L - Real.cos (2 * L - π / 4) / √(π * L)| ≤ Ck 12 / (π * L) := by
  have h := Ak_asymp (ν := 12) (by norm_num) hL
  rw [lead_twelve] at h
  set M : ℂ := (1 + I) * cexp (2 * I * L) * (√(π / (2 * L)) : ℂ)
  have hMim : M.im / π = Real.cos (2 * L - π / 4) / √(π * L) := by
    have hM : M.im = (Real.cos (2 * L) + Real.sin (2 * L)) * √(π / (2 * L)) := by
      simp only [M]
      rw [show (2 * I * (L : ℂ)) = ((2 * L : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      simp only [mul_im, mul_re, add_re, add_im, one_re, one_im, I_re, I_im, ofReal_re, ofReal_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    rw [hM, mul_div_assoc, sqrt_identity hL, Real.cos_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    ring
  have hIk : Ik 12 L - Real.cos (2 * L - π / 4) / √(π * L) = (Ak 12 L - M).im / π := by
    unfold Ik; rw [← hMim, sub_im, sub_div]
  rw [hIk, abs_div, abs_of_pos Real.pi_pos, div_le_div_iff₀ Real.pi_pos (by positivity)]
  have := (abs_im_le_norm (Ak 12 L - M)).trans h
  have hp := Real.pi_pos
  calc |(Ak 12 L - M).im| * (π * L) ≤ Ck 12 / L * (π * L) := by gcongr
    _ = Ck 12 * π := by field_simp

end RamanujanTau.VoronoiTrunc
