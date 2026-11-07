/-
# The `t`-derivative of the AFE weight `V_t(ξ) = V(6+it, ξ)`

On a line `Re u = x` (`x ≥ −1`, `x ≠ 0`) put
`Φ_x(t) = ∫_ℝ Γ(6+it+u) ξ^{−u} e^{u²}/u dy` (`u = x+iy`).  Then

* `hasDerivAt_Phi`: differentiation under the integral sign, `Φ_x'(t) = ∫ i Γ'(6+it+u) ξ^{−u}e^{u²}/u`;
* `hasDerivAt_Vline`: `d/dt [Φ_x(t)/(2π Γ(6+it))] = (2π)⁻¹ ∫ i(ψ(s+u)−ψ(s)) Γ(s+u) ξ^{−u}e^{u²}/u dy / Γ(s)`;
* `norm_Dline_le`: this is `≤ K (T(t)/ξ)^x / (1+|t|)` (from `norm_digamma_diff_le` + Stirling);
* **`V_deriv_bound`**: `t ↦ V(6+it, ξ)` is differentiable and
  `|∂_t V(6+it, ξ)| ≤ C_A (1+|t|)^{−1} (1 + ξ/(1+|t|))^{−A}`, uniformly in `t ∈ ℝ`, `ξ > 0`.
-/
import RamanujanTau.HeckeAFE2.Psi

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE2

open Complex MeasureTheory Set Filter Topology Metric RamanujanTau.HeckeAFE RamanujanTau.HeckeL
open scoped Real

/-- the integrand of `Φ_x(t)` -/
noncomputable def Fi (x ξ t y : ℝ) : ℂ :=
  Gamma ((6 + t * I) + ((x : ℂ) + y * I)) * (ξ : ℂ) ^ (-((x : ℂ) + y * I)) *
    cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)

/-- its `t`-derivative -/
noncomputable def Fi' (x ξ t y : ℝ) : ℂ :=
  I * deriv Gamma ((6 + t * I) + ((x : ℂ) + y * I)) * (ξ : ℂ) ^ (-((x : ℂ) + y * I)) *
    cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)

/-- the derivative of the normalized line integral -/
noncomputable def Dline (x ξ t : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (∫ y : ℝ, I * (digamma ((6 + t * I) + ((x : ℂ) + y * I)) -
    digamma (6 + t * I)) * Fi x ξ t y) / Gamma (6 + t * I)

lemma re_shift (t x y : ℝ) : ((6 + t * I) + ((x : ℂ) + y * I)).re = 6 + x := by simp

lemma shift_re_pos {x : ℝ} (hx : -1 ≤ x) (t y : ℝ) : 0 < ((6 + t * I) + ((x : ℂ) + y * I)).re := by
  rw [re_shift]; linarith

lemma Gamma_shift_ne {x : ℝ} (hx : -1 ≤ x) (t y : ℝ) :
    Gamma ((6 + t * I) + ((x : ℂ) + y * I)) ≠ 0 := Gamma_ne_zero_of_re_pos (shift_re_pos hx t y)

lemma deriv_Gamma_eq {z : ℂ} (hz : 0 < z.re) : deriv Gamma z = digamma z * Gamma z := by
  rw [digamma_def, logDeriv_apply, div_mul_cancel₀ _ (Gamma_ne_zero_of_re_pos hz)]

lemma continuousAt_deriv_Gamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt (deriv Gamma) z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (differentiableAt_Gamma w (ne_neg_nat_of_re_pos hw)).differentiableWithinAt
  exact (hd.analyticAt (hopen.mem_nhds hz)).deriv.continuousAt

lemma hasDerivAt_Gamma_line {x : ℝ} (hx : -1 ≤ x) (y t : ℝ) :
    HasDerivAt (fun w : ℝ => Gamma ((6 + w * I) + ((x : ℂ) + y * I)))
      (I * deriv Gamma ((6 + t * I) + ((x : ℂ) + y * I))) t := by
  have hin : HasDerivAt (fun w : ℝ => (6 + (w : ℂ) * I) + ((x : ℂ) + y * I)) (1 * I) t :=
    (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add 6 |>.add_const _
  have hG := (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (shift_re_pos hx t y))).hasDerivAt
  have := hG.comp t hin
  rw [one_mul] at this
  exact this.congr_deriv (mul_comm _ _)

/-! ## Pointwise bounds -/

lemma norm_K_le {x ξ : ℝ} (hx0 : x ≠ 0) (hξ : 0 < ξ) (y : ℝ) :
    ‖(ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖ ≤
      ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * Real.exp (-1 * y ^ 2) := by
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
  have hr : (-((x : ℂ) + y * I)).re = -x := by simp
  rw [hr]
  have hi : ‖((x : ℂ) + y * I)⁻¹‖ ≤ |x|⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ (abs_pos.2 hx0) (norm_line_ge y)
  have he : Real.exp (x ^ 2 - y ^ 2) = Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  calc ξ ^ (-x) * (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((x : ℂ) + y * I)⁻¹‖
      ≤ ξ ^ (-x) * (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * |x|⁻¹ := by gcongr
    _ = _ := by ring

lemma Fi_eq (x ξ t y : ℝ) : Fi x ξ t y = Gamma ((6 + t * I) + ((x : ℂ) + y * I)) *
    ((ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)) := by
  unfold Fi; ring

lemma Fi'_eq (x ξ t y : ℝ) : Fi' x ξ t y = I * deriv Gamma ((6 + t * I) + ((x : ℂ) + y * I)) *
    ((ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)) := by
  unfold Fi'; ring

lemma continuous_K {x ξ : ℝ} (hx0 : x ≠ 0) (hξ : 0 < ξ) :
    Continuous (fun y : ℝ => (ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) /
      ((x : ℂ) + y * I)) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  refine Continuous.div ?_ (continuous_line x) (line_ne_zero hx0)
  refine Continuous.mul ?_ (by fun_prop)
  exact continuous_iff_continuousAt.2 fun y =>
    ((continuousAt_const_cpow hξ0).comp (by fun_prop : Continuous fun y : ℝ =>
      -((x : ℂ) + y * I)).continuousAt)

lemma continuous_Fi {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    Continuous (Fi x ξ t) := by
  rw [show Fi x ξ t = _ from funext (Fi_eq x ξ t)]
  exact (continuous_Gamma_line (s := 6 + t * I) (c := x) (by simp; linarith)).mul
    (continuous_K hx0 hξ)

lemma continuous_Fi' {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    Continuous (Fi' x ξ t) := by
  rw [show Fi' x ξ t = _ from funext (Fi'_eq x ξ t)]
  refine Continuous.mul ?_ (continuous_K hx0 hξ)
  refine continuous_const.mul ?_
  rw [continuous_iff_continuousAt]
  intro y
  exact ContinuousAt.comp (g := deriv Gamma)
    (f := fun y : ℝ => (6 + t * I) + ((x : ℂ) + y * I))
    (continuousAt_deriv_Gamma (shift_re_pos hx t y)) (Continuous.continuousAt (by fun_prop))

lemma gamma_re_bound {x : ℝ} (hx : -1 ≤ x) (t y : ℝ) :
    ‖Gamma ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤ Real.Gamma (6 + x) := by
  have := RamanujanTau.RankinError.norm_Gamma_le_Gamma_re (shift_re_pos hx t y)
  rwa [re_shift] at this

lemma norm_log_le_self_add {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖log z‖ ≤ ‖z‖ + π := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [log_re, log_im]
  have h0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  rw [abs_of_nonneg h0]
  have h1 : Real.log ‖z‖ ≤ ‖z‖ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2 : |arg z| ≤ π := abs_arg_le_pi z
  linarith

lemma norm_digamma_shift_le {x : ℝ} (hx : -1 ≤ x) (t y : ℝ) :
    ‖digamma ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤ 6 + |x| + |t| + |y| + π + 10 := by
  set z : ℂ := (6 + t * I) + ((x : ℂ) + y * I)
  have hre : z.re = 6 + x := re_shift t x y
  have h1 := norm_digamma_sub_log_le (z := z) (by rw [hre]; linarith)
  have h40 : 40 / (z.re - 1 + |z.im|) ≤ 10 := by
    rw [div_le_iff₀ (by rw [hre]; linarith [abs_nonneg z.im])]
    rw [hre]; nlinarith [abs_nonneg z.im]
  have hz1 : 1 ≤ ‖z‖ := by
    have := Complex.re_le_norm z; rw [hre] at this; linarith
  have hzn : ‖z‖ ≤ 6 + |x| + |t| + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    have him : z.im = t + y := by simp [z]
    rw [hre, him]
    have := abs_add_le t y
    have : |6 + x| ≤ 6 + |x| := by
      calc |6 + x| ≤ |(6:ℝ)| + |x| := abs_add_le _ _
        _ = 6 + |x| := by norm_num
    linarith
  have hl := norm_log_le_self_add hz1
  have : ‖digamma z‖ ≤ ‖log z‖ + ‖digamma z - log z‖ := by
    have := norm_add_le (log z) (digamma z - log z); simpa using this
  linarith

/-- Gaussian domination of `Fi'` locally uniformly in `t`. -/
lemma norm_Fi'_le {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t₀ : ℝ) :
    ∃ M : ℝ, ∀ t ∈ ball t₀ 1, ∀ y : ℝ, ‖Fi' x ξ t y‖ ≤ M * Real.exp (-(1 / 2) * y ^ 2) := by
  set A : ℝ := 6 + |x| + (|t₀| + 1) + π + 10
  set Q : ℝ := ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹
  set E : ℝ := Real.exp ((1 + π / 2) ^ 2 / 2)
  have hQ : 0 ≤ Q := by positivity
  have hG : 0 ≤ Real.Gamma (6 + x) := (Real.Gamma_pos_of_pos (by linarith)).le
  refine ⟨(A + 1) * Real.Gamma (6 + x) * Q * E, fun t ht y => ?_⟩
  have htt : |t| ≤ |t₀| + 1 := by
    rw [mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀; linarith
  rw [Fi'_eq, norm_mul, norm_mul, norm_I, one_mul,
    deriv_Gamma_eq (shift_re_pos hx t y), norm_mul]
  have h1 := norm_digamma_shift_le hx t y
  have h2 := gamma_re_bound hx t y
  have h3 := norm_K_le hx0 hξ y
  have hpe := poly_exp_bound (q := 1) (by norm_num) y
  rw [Real.rpow_one] at hpe
  have hpi : 1 ≤ Real.exp (π * |y| / 2) := Real.one_le_exp (by positivity)
  have hy0 := abs_nonneg y
  have hψ : ‖digamma ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤ (A + 1) * (1 + |y|) := by
    have : 6 + |x| + |t| + |y| + π + 10 ≤ (A + 1) * (1 + |y|) := by
      have : 0 ≤ A := by positivity
      nlinarith
    linarith
  have hey : (1 + |y|) * Real.exp (-1 * y ^ 2) ≤ E * Real.exp (-(1 / 2) * y ^ 2) := by
    have h0 : 0 ≤ (1 + |y|) * Real.exp (-1 * y ^ 2) := by positivity
    have hq : Real.exp (-1 * y ^ 2) ≤ Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hpi
    calc (1 + |y|) * Real.exp (-1 * y ^ 2)
        ≤ (1 + |y|) * (Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (1 + |y|) * Real.exp (π * |y| / 2) * Real.exp (-1 * y ^ 2) := by ring
      _ ≤ _ := hpe
  calc ‖digamma ((6 + t * I) + ((x : ℂ) + y * I))‖ * ‖Gamma ((6 + t * I) + ((x : ℂ) + y * I))‖ *
        ‖(ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖
      ≤ ((A + 1) * (1 + |y|)) * Real.Gamma (6 + x) * (Q * Real.exp (-1 * y ^ 2)) := by
        gcongr
    _ = (A + 1) * Real.Gamma (6 + x) * Q * ((1 + |y|) * Real.exp (-1 * y ^ 2)) := by ring
    _ ≤ (A + 1) * Real.Gamma (6 + x) * Q * (E * Real.exp (-(1 / 2) * y ^ 2)) := by gcongr
    _ = _ := by ring

/-! ## Differentiation under the integral -/

theorem hasDerivAt_Phi {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ y : ℝ, Fi x ξ t y) (∫ y : ℝ, Fi' x ξ t₀ y) t₀ := by
  obtain ⟨M, hM⟩ := norm_Fi'_le hx hx0 hξ t₀
  have hint0 : Integrable (Fi x ξ t₀) := by
    refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
      (Real.Gamma (6 + x) * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)))
      (continuous_Fi hx hx0 hξ t₀).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Fi_eq, norm_mul]
    calc _ ≤ Real.Gamma (6 + x) * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * Real.exp (-1 * y ^ 2)) :=
          mul_le_mul (gamma_re_bound hx t₀ y) (norm_K_le hx0 hξ y) (norm_nonneg _)
            (Real.Gamma_pos_of_pos (by linarith)).le
      _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t y => Fi x ξ t y) (F' := fun t y => Fi' x ξ t y)
    (bound := fun y => M * Real.exp (-(1 / 2) * y ^ 2)) (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (continuous_Fi hx hx0 hξ t).aestronglyMeasurable) hint0
    (continuous_Fi' hx hx0 hξ t₀).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => hM t ht y)
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    (Eventually.of_forall fun y t _ => by
      have hG := hasDerivAt_Gamma_line hx y t
      have := ((hG.mul_const ((ξ : ℂ) ^ (-((x : ℂ) + y * I)))).mul_const
        (cexp (((x : ℂ) + y * I) ^ 2))).div_const ((x : ℂ) + y * I)
      exact this)
  exact h.2

lemma integrable_Fi {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    Integrable (Fi x ξ t) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).const_mul
    (Real.Gamma (6 + x) * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹)))
    (continuous_Fi hx hx0 hξ t).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Fi_eq, norm_mul]
  calc _ ≤ Real.Gamma (6 + x) * (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * Real.exp (-1 * y ^ 2)) :=
        mul_le_mul (gamma_re_bound hx t y) (norm_K_le hx0 hξ y) (norm_nonneg _)
          (Real.Gamma_pos_of_pos (by linarith)).le
    _ = _ := by ring

lemma integrable_Fi' {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    Integrable (Fi' x ξ t) := by
  obtain ⟨M, hM⟩ := norm_Fi'_le hx hx0 hξ t
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul M)
    (continuous_Fi' hx hx0 hξ t).aestronglyMeasurable
    (Eventually.of_forall fun y => hM t (mem_ball_self one_pos) y)

/-- the normalized line integral `V_x(t) = (2π)⁻¹ Φ_x(t) / Γ(6+it)` -/
noncomputable def Vline (x ξ t : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (∫ y : ℝ, Fi x ξ t y) / Gamma (6 + t * I)

lemma Vline_eq_WGam (x ξ t : ℝ) : Vline x ξ t = WGam (6 + t * I) ξ x / Gamma (6 + t * I) := by
  unfold Vline WGam vline Fi; rfl

theorem hasDerivAt_Vline {x ξ : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    HasDerivAt (Vline x ξ) (Dline x ξ t) t := by
  have hΦ := hasDerivAt_Phi hx hx0 hξ t
  have hΓ : HasDerivAt (fun w : ℝ => Gamma (6 + w * I)) (I * deriv Gamma (6 + t * I)) t := by
    have := hasDerivAt_Gamma_line (x := 0) (by norm_num) 0 t
    simpa using this
  have hne : Gamma (6 + t * I) ≠ 0 := Gamma_line_ne_zero t
  have h := (hΦ.const_mul ((2 * π : ℂ)⁻¹)).div hΓ hne
  have e : Vline x ξ = fun w => (2 * π : ℂ)⁻¹ * (∫ y : ℝ, Fi x ξ w y) / Gamma (6 + w * I) := rfl
  rw [e]
  convert h using 1
  -- identify the derivative
  unfold Dline
  have hs : 0 < (6 + t * I).re := by simp
  rw [deriv_Gamma_eq hs]
  have hsplit : (∫ y : ℝ, I * (digamma ((6 + t * I) + ((x : ℂ) + y * I)) -
      digamma (6 + t * I)) * Fi x ξ t y) =
      (∫ y : ℝ, Fi' x ξ t y) - I * digamma (6 + t * I) * ∫ y : ℝ, Fi x ξ t y := by
    rw [← integral_const_mul, ← integral_sub (integrable_Fi' hx hx0 hξ t)
      ((integrable_Fi hx hx0 hξ t).const_mul _)]
    congr 1; ext y
    rw [Fi'_eq, Fi_eq, deriv_Gamma_eq (shift_re_pos hx t y)]
    ring
  rw [hsplit]
  field_simp

/-! ## The bound for the derivative on a line -/

theorem norm_Dline_le {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ξ : ℝ, 0 < ξ →
      ‖Dline x ξ t‖ ≤ K * (Tq t / ξ) ^ x / (1 + |t|) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line (x := x) (by linarith)
  obtain ⟨Cψ, hCψ0, hCψ⟩ := norm_digamma_diff_le hx
  have hp0 : 0 ≤ 11 / 2 + x + 2 := by linarith
  set E : ℝ := Real.exp ((11 / 2 + x + 2 + π / 2) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  have hx' : 0 < |x| := abs_pos.2 hx0
  set K : ℝ := (2 * π)⁻¹ * (Cψ * C * E * Real.exp (x ^ 2) * |x|⁻¹ * J)
  refine ⟨K, by positivity, fun t ξ hξ => ?_⟩
  have h1t : 0 < 1 + |t| := by positivity
  set G : ℝ := ‖Gamma (6 + t * I)‖
  have hGp : 0 < G := norm_pos_iff.2 (Gamma_line_ne_zero t)
  set B : ℝ := Cψ / (1 + |t|) * C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * E
  have hB : ∀ y : ℝ, ‖I * (digamma ((6 + t * I) + ((x : ℂ) + y * I)) - digamma (6 + t * I)) *
      Fi x ξ t y‖ ≤ B * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    rw [norm_mul, norm_mul, norm_I, one_mul, Fi_eq, norm_mul]
    have hψ := hCψ t y
    have hΓ := hC t y
    have hK := norm_K_le hx0 hξ y
    have hpe := poly_exp_bound hp0 y
    have hy1 : 0 < 1 + |y| := by positivity
    have hpow : (1 + |y|) ^ 2 * (1 + |y|) ^ (11 / 2 + x) = (1 + |y|) ^ (11 / 2 + x + 2) := by
      rw [show (11 / 2 + x + 2 : ℝ) = 2 + (11 / 2 + x) by ring, Real.rpow_add hy1 2 (11 / 2 + x),
        Real.rpow_two]
    have hTx : 0 ≤ Tq t ^ x := (Real.rpow_pos_of_pos (Tq_pos t) _).le
    calc ‖digamma ((6 + t * I) + ((x : ℂ) + y * I)) - digamma (6 + t * I)‖ *
          (‖Gamma ((6 + t * I) + ((x : ℂ) + y * I))‖ *
          ‖(ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖)
        ≤ (Cψ * (1 + |y|) ^ 2 / (1 + |t|)) *
          ((C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) * G) *
          (ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * Real.exp (-1 * y ^ 2))) := by
          gcongr
      _ = Cψ / (1 + |t|) * C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          (((1 + |y|) ^ 2 * (1 + |y|) ^ (11 / 2 + x)) * Real.exp (π * |y| / 2) *
            Real.exp (-1 * y ^ 2)) := by ring
      _ ≤ Cψ / (1 + |t|) * C * Tq t ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by rw [hpow]; gcongr
      _ = _ := by ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul B
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hB)
  rw [integral_const_mul] at hI
  unfold Dline
  rw [norm_div, norm_mul, div_le_iff₀ hGp]
  have h2pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h2pi]
  have hdiv : (Tq t / ξ) ^ x = Tq t ^ x * ξ ^ (-x) := by
    rw [Real.div_rpow (Tq_pos t).le hξ.le, Real.rpow_neg hξ.le, div_eq_mul_inv]
  rw [hdiv]
  calc (2 * π)⁻¹ * ‖∫ y : ℝ, I * (digamma ((6 + t * I) + ((x : ℂ) + y * I)) -
        digamma (6 + t * I)) * Fi x ξ t y‖
      ≤ (2 * π)⁻¹ * (B * J) := by gcongr
    _ = _ := by simp only [B, K]; field_simp

/-! ## The headline: `∂_t V_t(ξ) ≪ (1+|t|)^{−1} (1+ξ/(1+|t|))^{−A}` -/

lemma V_eq_Vline_pos {x ξ : ℝ} (hx : 0 < x) (hξ : 0 < ξ) :
    (fun t : ℝ => V (6 + t * I) ξ) = Vline x ξ := by
  funext t
  rw [Vline_eq_WGam]
  unfold V
  have hsre : (6 + t * I).re = 6 := by simp
  rcases le_total x 2 with h | h
  · rw [WGam_shift hξ hx h (by rw [hsre]; linarith)]
  · rw [WGam_shift hξ (by norm_num) h (by rw [hsre]; norm_num)]

lemma V_eq_one_add_Vline {ξ : ℝ} (hξ : 0 < ξ) :
    (fun t : ℝ => V (6 + t * I) ξ) = fun t => 1 + Vline (-1) ξ t := by
  funext t
  rw [Vline_eq_WGam]
  unfold V
  have hsre : (6 + t * I).re = 6 := by simp
  have hres := WGam_residue (s := 6 + t * I) hξ (by norm_num : (0:ℝ) < 2) one_pos
    (by rw [hsre]; norm_num)
  have hG := Gamma_line_ne_zero t
  rw [div_eq_iff hG, add_mul, div_mul_cancel₀ _ hG, one_mul]
  linear_combination hres

lemma combine_bound {A a b w T ξ f : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 < w)
    (hξ : 0 < ξ) (hT1 : w / 2 ≤ T) (hT2 : T ≤ 3 / 2 * w)
    (h1 : f ≤ a * (T / ξ) ^ (A + 1)) (h2 : f ≤ b * (T / ξ) ^ (-1 : ℝ)) :
    f ≤ max (2 * b * 2 ^ A) (a * (3 / 2) ^ (A + 1) * 2 ^ A) * (1 + ξ / w) ^ (-A) := by
  set r : ℝ := ξ / w with hr
  have hr0 : 0 < r := by positivity
  have hT0 : 0 < T := by linarith
  have h2A : (2:ℝ) ^ A * (2:ℝ) ^ (-A) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
  have hM1 : 0 ≤ 2 * b * 2 ^ A := by positivity
  rcases le_total r 1 with hr1 | hr1
  · have hx : (T / ξ) ^ (-1 : ℝ) ≤ 2 := by
      rw [Real.rpow_neg_one, inv_div, div_le_iff₀ hT0]
      have : ξ ≤ w := by rw [hr] at hr1; rwa [div_le_one hw] at hr1
      linarith
    have hlow : (2:ℝ) ^ (-A) ≤ (1 + r) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    calc f ≤ b * 2 := h2.trans (by gcongr)
      _ = 2 * b * ((2:ℝ) ^ A * (2:ℝ) ^ (-A)) := by rw [h2A]; ring
      _ ≤ 2 * b * 2 ^ A * (1 + r) ^ (-A) := by rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hTξ : T / ξ ≤ 3 / 2 * r⁻¹ := by
      rw [hr, inv_div, div_le_iff₀ hξ]; field_simp; linarith
    have hri : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    have hri0 : 0 < r⁻¹ := inv_pos.2 hr0
    have h3 : (T / ξ) ^ (A + 1) ≤ (3 / 2) ^ (A + 1) * r⁻¹ ^ (A + 1) := by
      rw [← Real.mul_rpow (by norm_num) hri0.le]
      exact Real.rpow_le_rpow (by positivity) hTξ (by linarith)
    have h4 : r⁻¹ ^ (A + 1) ≤ r⁻¹ ^ A := Real.rpow_le_rpow_of_exponent_ge hri0 hri (by linarith)
    have h5 : r⁻¹ ^ A ≤ 2 ^ A * (1 + r) ^ (-A) := by
      rw [Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
      have : r ^ (-A) ≤ ((1 + r) / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      refine this.trans (le_of_eq ?_)
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    calc f ≤ a * (T / ξ) ^ (A + 1) := h1
      _ ≤ a * ((3 / 2) ^ (A + 1) * (2 ^ A * (1 + r) ^ (-A))) := by
          gcongr; exact h3.trans (by gcongr; exact h4.trans h5)
      _ = a * (3 / 2) ^ (A + 1) * 2 ^ A * (1 + r) ^ (-A) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- **Derivative bound for the AFE weight** (`j = 1`): for every `A ≥ 0` there is `C` with
`t ↦ V(6+it, ξ)` differentiable and
`‖∂_t V(6+it, ξ)‖ ≤ C (1+|t|)^{−1} (1 + ξ/(1+|t|))^{−A}`, uniformly in `t ∈ ℝ`, `ξ > 0`. -/
theorem V_deriv_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ →
      HasDerivAt (fun w : ℝ => V (6 + w * I) ξ) (deriv (fun w : ℝ => V (6 + w * I) ξ) t) t ∧
      ‖deriv (fun w : ℝ => V (6 + w * I) ξ) t‖ ≤ C / (1 + |t|) * (1 + ξ / (1 + |t|)) ^ (-A) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_Dline_le (x := A + 1) (by linarith) (ne_of_gt (by linarith))
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_Dline_le (x := -1) le_rfl (by norm_num)
  refine ⟨max (2 * K₂ * 2 ^ A) (K₁ * (3 / 2) ^ (A + 1) * 2 ^ A), by positivity,
    fun t ξ hξ => ?_⟩
  have hd1 : HasDerivAt (fun w : ℝ => V (6 + w * I) ξ) (Dline (A + 1) ξ t) t := by
    rw [V_eq_Vline_pos (x := A + 1) (by linarith) hξ]
    exact hasDerivAt_Vline (by linarith) (ne_of_gt (by linarith)) hξ t
  have hd2 : HasDerivAt (fun w : ℝ => V (6 + w * I) ξ) (Dline (-1) ξ t) t := by
    rw [V_eq_one_add_Vline hξ]
    exact (hasDerivAt_Vline le_rfl (by norm_num) hξ t).const_add 1
  refine ⟨hd1.differentiableAt.hasDerivAt, ?_⟩
  have h1t : 0 < 1 + |t| := by positivity
  have e1 := hd1.deriv
  have e2 := hd2.deriv
  set f : ℝ := ‖deriv (fun w : ℝ => V (6 + w * I) ξ) t‖ * (1 + |t|)
  have hf1 : f ≤ K₁ * (Tq t / ξ) ^ (A + 1) := by
    simp only [f]; rw [e1, ← le_div_iff₀ h1t]; exact hK₁ t ξ hξ
  have hf2 : f ≤ K₂ * (Tq t / ξ) ^ (-1 : ℝ) := by
    simp only [f]; rw [e2, ← le_div_iff₀ h1t]; exact hK₂ t ξ hξ
  have hc := combine_bound (w := 1 + |t|) hA hK₁0 hK₂0 h1t hξ (Tq_ge t) (Tq_le t) hf1 hf2
  rw [div_mul_eq_mul_div, le_div_iff₀ h1t]
  linarith

end RamanujanTau.HeckeAFE2
