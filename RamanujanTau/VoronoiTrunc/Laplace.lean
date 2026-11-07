/-
# Inverse Laplace transform of `z^{−(r+1)}` on the line `Re z = 1`

`laplace_inv`: for `r ≥ 1` and real `w`,

    (1/2π) ∫_ℝ e^{w(1+it)} (1+it)^{−(r+1)} dt = (max w 0)^r / r!.

Proof: Fourier inversion (`Continuous.fourierInv_fourier_eq`) for `φ(y) = y_+^r e^{−y_+}/r!`,
whose Fourier transform is `(1 + 2πiξ)^{−(r+1)}` (`integral_pow_mul_cexp_neg`, by induction with
integration by parts on `(0,∞)`).
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

lemma integrableOn_pow_mul_exp_neg (r : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun v : ℝ => v ^ r * Real.exp (-b * v)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1) (b := b)
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith) le_rfl hb
  refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast]

lemma integrableOn_cpow_mul_cexp_neg (r : ℕ) {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ r * cexp (-a * v)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_pow_mul_exp_neg r ha) (by
    apply Continuous.aestronglyMeasurable; fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv, Complex.norm_exp]
  simp [mul_re]

/-- `∫₀^∞ v^r e^{−av} dv = r!/a^{r+1}` for `Re a > 0`. -/
theorem integral_pow_mul_cexp_neg (r : ℕ) {a : ℂ} (ha : 0 < a.re) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ r * cexp (-a * v) = (Nat.factorial r : ℂ) / a ^ (r + 1) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  induction r with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have := integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
    simpa using this
  | succ r ih =>
    -- integrate by parts: u = v^{r+1}, dv = e^{−av}
    have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun v : ℝ => (v : ℂ) ^ (r + 1))
        (((r + 1 : ℕ) : ℂ) * (x : ℂ) ^ r) x := by
      intro x _
      have := (hasDerivAt_id x).ofReal_comp.pow (r + 1)
      simpa using this
    have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun v : ℝ => -cexp (-a * v) / a) (cexp (-a * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun v : ℝ => -a * (v : ℂ)) (-a) x := by
        simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-a)
      have := (h1.cexp.neg).div_const a
      convert this using 1
      field_simp
    have hint1 : IntegrableOn ((fun v : ℝ => (v : ℂ) ^ (r + 1)) * fun v : ℝ => cexp (-a * (v : ℂ))) (Ioi 0) :=
      integrableOn_cpow_mul_cexp_neg (r + 1) ha
    have hint2 : IntegrableOn ((fun v : ℝ => ((r + 1 : ℕ) : ℂ) * (v : ℂ) ^ r) *
        fun v : ℝ => -cexp (-a * (v : ℂ)) / a) (Ioi 0) := by
      have : IntegrableOn (fun v : ℝ => (-((r + 1 : ℕ) : ℂ) / a) * ((v : ℂ) ^ r * cexp (-a * v)))
          (Ioi 0) := (integrableOn_cpow_mul_cexp_neg r ha).const_mul _
      refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; field_simp
    have hzero : Tendsto ((fun v : ℝ => (v : ℂ) ^ (r + 1)) * fun v : ℝ => -cexp (-a * (v : ℂ)) / a)
        (𝓝[>] 0) (𝓝 0) := by
      have : Continuous ((fun v : ℝ => (v : ℂ) ^ (r + 1)) * fun v : ℝ => -cexp (-a * (v : ℂ)) / a) := by
        fun_prop
      have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    have hinf : Tendsto ((fun v : ℝ => (v : ℂ) ^ (r + 1)) * fun v : ℝ => -cexp (-a * (v : ℂ)) / a)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero (r + 1)
      have h2 : Tendsto (fun v : ℝ => (a.re * v) ^ (r + 1) * Real.exp (-(a.re * v))) atTop (𝓝 0) :=
        h.comp (tendsto_id.const_mul_atTop ha)
      have h3 : Tendsto (fun v : ℝ => ((a.re ^ (r + 1))⁻¹ * ‖a‖⁻¹) *
          ((a.re * v) ^ (r + 1) * Real.exp (-(a.re * v)))) atTop (𝓝 0) := by
        simpa using h2.const_mul ((a.re ^ (r + 1))⁻¹ * ‖a‖⁻¹)
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with v hv
      simp only [Pi.mul_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hv, norm_div, norm_neg, Complex.norm_exp]
      have : (-a * (v : ℂ)).re = -(a.re * v) := by simp
      rw [this, mul_pow]
      have hre : 0 < a.re ^ (r + 1) := by positivity
      have hn : 0 < ‖a‖ := norm_pos_iff.2 ha0
      field_simp
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hzero hinf
    simp only at hibp
    rw [hibp]
    have e : ∫ x in Ioi (0 : ℝ), ((r + 1 : ℕ) : ℂ) * (x : ℂ) ^ r * (-cexp (-a * x) / a) =
        (-((r + 1 : ℕ) : ℂ) / a) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ r * cexp (-a * x) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      field_simp
    rw [e, ih]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring


/-- `φ_r(y) = y_+^r e^{−y_+}/r!`. -/
noncomputable def phiL (r : ℕ) (y : ℝ) : ℂ :=
  (((max y 0) ^ r * Real.exp (-(max y 0)) / (Nat.factorial r : ℝ) : ℝ) : ℂ)

lemma continuous_phiL (r : ℕ) : Continuous (phiL r) := by unfold phiL; fun_prop

lemma phiL_of_nonpos {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : y ≤ 0) : phiL r y = 0 := by
  unfold phiL; rw [max_eq_right hy, zero_pow (by omega)]; simp

lemma phiL_of_pos (r : ℕ) {y : ℝ} (hy : 0 < y) :
    phiL r y = (y : ℂ) ^ r * cexp (-(y : ℂ)) / (Nat.factorial r : ℂ) := by
  unfold phiL; rw [max_eq_left hy.le]; push_cast; rfl

lemma integrable_phiL {r : ℕ} (hr : 1 ≤ r) : Integrable (phiL r) := by
  have hon : IntegrableOn (phiL r) (Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => (v : ℂ) ^ r * cexp (-1 * v) / (Nat.factorial r : ℂ)) (Ioi 0) :=
      (integrableOn_cpow_mul_cexp_neg r (a := 1) (by simp)).div_const (Nat.factorial r : ℂ)
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    rw [phiL_of_pos r hy]; simp
  exact hon.integrable_of_forall_notMem_eq_zero (fun y hy => phiL_of_nonpos hr (not_lt.1 hy))

lemma fourier_phiL {r : ℕ} (hr : 1 ≤ r) (ξ : ℝ) :
    𝓕 (phiL r) ξ = ((1 + 2 * π * ξ * I) ^ (r + 1))⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hz : ∀ v, v ∉ Ioi (0 : ℝ) → cexp (↑(-2 * π * v * ξ) * I) • phiL r v = 0 := by
    intro v hv; rw [phiL_of_nonpos hr (not_lt.1 hv), smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  set a : ℂ := 1 + 2 * π * ξ * I
  have ha : 0 < a.re := by simp [a]
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have e : ∀ v ∈ Ioi (0 : ℝ), cexp (↑(-2 * π * v * ξ) * I) • phiL r v =
      (1 / (Nat.factorial r : ℂ)) * ((v : ℂ) ^ r * cexp (-a * v)) := by
    intro v hv
    rw [phiL_of_pos r hv, smul_eq_mul]
    have : cexp (↑(-2 * π * v * ξ) * I) * cexp (-(v : ℂ)) = cexp (-a * v) := by
      rw [← Complex.exp_add]; congr 1; simp only [a]; push_cast; ring
    rw [← this]
    have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, integral_pow_mul_cexp_neg r ha]
  have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  field_simp

lemma norm_fourier_phiL_le {r : ℕ} (hr : 1 ≤ r) (ξ : ℝ) :
    ‖((1 + 2 * π * ξ * I) ^ (r + 1))⁻¹‖ ≤ (1 + ξ ^ 2)⁻¹ := by
  set a : ℂ := 1 + 2 * π * ξ * I
  have hsq : ‖a‖ ^ 2 = 1 + (2 * π * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [a]; ring
  have h1 : 1 ≤ ‖a‖ := by
    have : (1 : ℝ) ^ 2 ≤ ‖a‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (2 * π * ξ)]
    exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) (by norm_num)).1 this
  have h2 : 1 + ξ ^ 2 ≤ ‖a‖ ^ (r + 1) := by
    calc 1 + ξ ^ 2 ≤ ‖a‖ ^ 2 := by
          rw [hsq]; have := Real.two_le_pi
          have h4 : 1 ≤ (2 * π) ^ 2 := by nlinarith
          nlinarith [sq_nonneg ξ, mul_le_mul_of_nonneg_right h4 (sq_nonneg ξ)]
      _ ≤ ‖a‖ ^ (r + 1) := pow_le_pow_right₀ h1 (by omega)
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (by positivity) h2

lemma integrable_fourier_phiL {r : ℕ} (hr : 1 ≤ r) : Integrable (𝓕 (phiL r)) := by
  have hc : Continuous fun ξ : ℝ => ((1 + 2 * π * ξ * I) ^ (r + 1))⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) (fun ξ => pow_ne_zero _ ?_)
    intro h; have := congrArg Complex.re h; simp at this
  have : Integrable fun ξ : ℝ => ((1 + 2 * π * ξ * I) ^ (r + 1))⁻¹ :=
    Integrable.mono' integrable_inv_one_add_sq hc.aestronglyMeasurable
      (Eventually.of_forall (norm_fourier_phiL_le hr))
  refine this.congr (Eventually.of_forall fun ξ => ?_)
  rw [fourier_phiL hr]

/-- **Inverse Laplace transform on `Re z = 1`**. -/
theorem laplace_inv {r : ℕ} (hr : 1 ≤ r) (w : ℝ) :
    ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, cexp (w * (1 + t * I)) * ((1 + t * I) ^ (r + 1))⁻¹ =
      (((max w 0) ^ r / (Nat.factorial r : ℝ) : ℝ) : ℂ) := by
  have hinv := (continuous_phiL r).fourierInv_fourier_eq (integrable_phiL hr) (integrable_fourier_phiL hr)
  have hw := congrFun hinv w
  rw [Real.fourierInv_eq'] at hw
  set F : ℝ → ℂ := fun t => cexp (w * (1 + t * I)) * ((1 + t * I) ^ (r + 1))⁻¹ with hF
  have hsub : ∫ t : ℝ, F t = |2 * π| * ∫ ξ : ℝ, F (2 * π * ξ) := by
    have := Measure.integral_comp_mul_left F (2 * π)
    rw [this, Complex.real_smul, abs_inv]
    have hp : 0 < |2 * π| := by positivity
    push_cast
    field_simp
  have hpt : ∀ ξ : ℝ, F (2 * π * ξ) = cexp w * (cexp (↑(2 * π * (ξ * w)) * I) • 𝓕 (phiL r) ξ) := by
    intro ξ
    rw [fourier_phiL hr, smul_eq_mul, hF]
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [hsub]
  simp_rw [hpt]
  rw [integral_const_mul]
  have hinner : ∀ ξ : ℝ, (inner ℝ ξ w : ℝ) = ξ * w := by
    intro ξ; simp [mul_comm]
  simp_rw [hinner] at hw
  rw [hw]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hp : (2 * π : ℝ) ≠ 0 := by positivity
  rcases le_or_gt w 0 with h | h
  · rw [phiL_of_nonpos hr h, max_eq_right h, zero_pow (by omega)]; simp
  · rw [phiL_of_pos r h, max_eq_left h.le]
    have e1 : cexp (w : ℂ) * cexp (-(w : ℂ)) = 1 := by rw [← Complex.exp_add]; simp
    have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
    push_cast
    field_simp
    linear_combination ((w : ℂ) ^ r) * e1

end RamanujanTau.VoronoiTrunc
