import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The Hermite–Gaussian integral behind the Shimura lift

For `c > 0` and every `n`,

  `∫₀^∞ x^(n-2) H_n(x) exp(-x²/2 - c²/(2x²)) dx = √(π/2) c^(n-1) exp(-c)`,

where `H_n` is the probabilists' Hermite polynomial. The proof is an induction on `n`, using
integration by parts and differentiation in `c`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open MeasureTheory Set Filter Topology Polynomial

/-- The weight `exp(-x²/2 - c²/(2x²))`. -/
noncomputable def wgt (c x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2) - c ^ 2 / (2 * x ^ 2))

lemma wgt_pos (c x : ℝ) : 0 < wgt c x := Real.exp_pos _

/-- A uniform bound for powers against the weight. -/
lemma zpow_bound (p : ℤ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c x : ℝ}, c₀ ≤ c → 0 < x →
      x ^ p * Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2)) ≤ C := by
  let m := p.natAbs
  refine ⟨(4 : ℝ) ^ m * m.factorial + (2 / c₀ ^ 2) ^ m * m.factorial, by positivity, ?_⟩
  intro c x hc hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hmono : c₀ ^ 2 / (2 * x ^ 2) ≤ c ^ 2 / (2 * x ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hc₀.le hc 2
  have hp1 : (x ^ 2 / 4) ^ m / m.factorial ≤ Real.exp (x ^ 2 / 4) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hp2 : (c₀ ^ 2 / (2 * x ^ 2)) ^ m / m.factorial ≤ Real.exp (c₀ ^ 2 / (2 * x ^ 2)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have he1 : Real.exp (-(x ^ 2 / 4)) * (x ^ 2 / 4) ^ m ≤ m.factorial := by
    rw [div_le_iff₀ hf] at hp1
    rw [Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  have he2 : Real.exp (-(c₀ ^ 2 / (2 * x ^ 2))) * (c₀ ^ 2 / (2 * x ^ 2)) ^ m ≤ m.factorial := by
    rw [div_le_iff₀ hf] at hp2
    rw [Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  rcases le_total 1 x with h1 | h1
  · have hpow : x ^ p ≤ (x ^ 2) ^ m := by
      rw [← pow_mul, ← zpow_natCast]
      apply zpow_le_zpow_right₀ h1
      push_cast
      omega
    have hE : Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2)) ≤ Real.exp (-(x ^ 2 / 4)) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ c ^ 2 / (2 * x ^ 2) := by positivity
      linarith
    calc x ^ p * Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2))
        ≤ (x ^ 2) ^ m * Real.exp (-(x ^ 2 / 4)) :=
          mul_le_mul hpow hE (Real.exp_pos _).le (by positivity)
      _ = 4 ^ m * (Real.exp (-(x ^ 2 / 4)) * (x ^ 2 / 4) ^ m) := by
          rw [div_pow]
          field_simp
      _ ≤ 4 ^ m * m.factorial := by gcongr
      _ ≤ _ := by
          have : 0 ≤ (2 / c₀ ^ 2) ^ m * (m.factorial : ℝ) := by positivity
          linarith
  · have hpow : x ^ p ≤ (x ^ 2)⁻¹ ^ m := by
      rw [inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]
      apply zpow_le_zpow_right_of_le_one₀ hx h1
      push_cast
      omega
    have hE : Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2)) ≤
        Real.exp (-(c₀ ^ 2 / (2 * x ^ 2))) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ x ^ 2 / 4 := by positivity
      linarith
    calc x ^ p * Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2))
        ≤ (x ^ 2)⁻¹ ^ m * Real.exp (-(c₀ ^ 2 / (2 * x ^ 2))) :=
          mul_le_mul hpow hE (Real.exp_pos _).le (by positivity)
      _ = (2 / c₀ ^ 2) ^ m * (Real.exp (-(c₀ ^ 2 / (2 * x ^ 2))) * (c₀ ^ 2 / (2 * x ^ 2)) ^ m) := by
          rw [div_pow, div_pow, inv_pow]
          have hc0 : c₀ ≠ 0 := hc₀.ne'
          field_simp
          ring
      _ ≤ (2 / c₀ ^ 2) ^ m * m.factorial := by gcongr
      _ ≤ _ := by
          have : 0 ≤ (4 : ℝ) ^ m * (m.factorial : ℝ) := by positivity
          linarith

lemma gauss_integrable : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) (Ioi 0) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).integrableOn (s := Ioi 0)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  congr 1
  ring

/-- The basic integrand is dominated by a Gaussian, uniformly for `c ≥ c₀`. -/
lemma zpow_wgt_le (p : ℤ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c x : ℝ}, c₀ ≤ c → 0 < x →
      x ^ p * wgt c x ≤ C * Real.exp (-(x ^ 2 / 4)) := by
  obtain ⟨C, hC, h⟩ := zpow_bound p hc₀
  refine ⟨C, hC, fun {c x} hc hx => ?_⟩
  have := h hc hx
  have hsplit : wgt c x = Real.exp (-(x ^ 2 / 4) - c ^ 2 / (2 * x ^ 2)) * Real.exp (-(x ^ 2 / 4)) := by
    rw [wgt, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- Continuity of the integrand on the positive reals. -/
lemma continuousOn_wgt (c : ℝ) : ContinuousOn (wgt c) (Ioi 0) := by
  unfold wgt
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.sub (by fun_prop)
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have : 0 < x := hx
  positivity

lemma integrableOn_zpow_wgt (p : ℤ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ p * wgt c x) (Ioi 0) := by
  obtain ⟨C, -, h⟩ := zpow_wgt_le p hc
  refine Integrable.mono' (gauss_integrable.const_mul C) ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul _ (continuousOn_wgt c)
    exact continuousOn_id.zpow₀ p (fun x hx => Or.inl (ne_of_gt hx))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : 0 < x := hx
    rw [Real.norm_of_nonneg (mul_nonneg (zpow_nonneg hx'.le _) (wgt_pos c x).le)]
    exact h le_rfl hx'

/-- `K(p,c) = ∫₀^∞ x^p exp(-x²/2 - c²/(2x²)) dx`. -/
noncomputable def K (p : ℤ) (c : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), x ^ p * wgt c x

lemma hasDerivAt_wgt_c (c x : ℝ) :
    HasDerivAt (fun c => wgt c x) (-c * ((x ^ 2)⁻¹ * wgt c x)) c := by
  unfold wgt
  have h : HasDerivAt (fun c : ℝ => -(x ^ 2 / 2) - c ^ 2 / (2 * x ^ 2))
      (-(2 * c / (2 * x ^ 2))) c := by
    have := ((hasDerivAt_pow 2 c).div_const (2 * x ^ 2)).const_sub (-(x ^ 2 / 2))
    simpa using this
  convert h.exp using 1
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

/-- Differentiating in `c` lowers the power of `x` by two. -/
theorem hasDerivAt_K (p : ℤ) {c : ℝ} (hc : 0 < c) : HasDerivAt (K p) (-c * K (p - 2) c) c := by
  obtain ⟨C, hC, hb⟩ := zpow_wgt_le (p - 2) (half_pos hc)
  have hs : Ioo (c / 2) (2 * c) ∈ 𝓝 c := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ d in 𝓝 c, AEStronglyMeasurable (fun x : ℝ => x ^ p * wgt d x)
      (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioo_mem_nhds (a := 0) (b := 2 * c) hc (by linarith)] with d hd
    exact (integrableOn_zpow_wgt p hd.1).aestronglyMeasurable
  have hbound : Integrable (fun x : ℝ => 2 * c * (C * Real.exp (-(x ^ 2 / 4))))
      (volume.restrict (Ioi 0)) := (gauss_integrable.const_mul C).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := fun d x => x ^ p * wgt d x)
    (F' := fun d x => -d * (x ^ (p - 2) * wgt d x))
    (bound := fun x : ℝ => 2 * c * (C * Real.exp (-(x ^ 2 / 4)))) (x₀ := c) hs hmeas
    (integrableOn_zpow_wgt p hc) ((integrableOn_zpow_wgt (p - 2) hc).const_mul (-c)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx d hd => ?_)) hbound
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx d _ => ?_))
  · have := key.2
    rw [integral_const_mul] at this
    exact this
  · have hx' : 0 < x := hx
    have hd0 : 0 < d := by linarith [hd.1, half_pos hc]
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hd0.le,
      Real.norm_of_nonneg (mul_nonneg (zpow_nonneg hx'.le _) (wgt_pos d x).le)]
    exact mul_le_mul hd.2.le (hb hd.1.le hx') (mul_nonneg (zpow_nonneg hx'.le _) (wgt_pos d x).le)
      (by linarith)
  · have hx' : 0 < x := hx
    have := (hasDerivAt_wgt_c d x).const_mul (x ^ p)
    convert this using 1
    change -d * (x ^ (p - 2) * wgt d x) = _
    rw [zpow_sub₀ hx'.ne']
    simp only [zpow_ofNat]
    field_simp

/-- The substitution `x ↦ c/x`. -/
theorem K_neg_two (c : ℝ) (hc : 0 < c) : K (-2) c = K 0 c / c := by
  let h : ℝ → ℝ := wgt c
  have hsym : ∀ {u : ℝ}, 0 < u → h (c / u) = h u := by
    intro u hu
    simp only [h, wgt]
    congr 1
    field_simp
    ring
  have h1 := integral_comp_rpow_Ioi (fun u => h (c * u)) (p := -1) (by norm_num)
  have h2 := integral_comp_mul_left_Ioi h 0 hc
  simp only [mul_zero] at h2
  have hl : ∫ x in Ioi (0 : ℝ), x ^ (-2 : ℤ) * wgt c x =
      ∫ x in Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • h (c * x ^ (-1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : 0 < x := hx
    have e1 : c * x ^ (-1 : ℝ) = c / x := by rw [Real.rpow_neg_one]; rfl
    have e2 : x ^ ((-1 : ℝ) - 1) = x ^ (-2 : ℤ) := by
      rw [← Real.rpow_intCast]
      norm_num
    simp only [e1, e2, hsym hx', abs_neg, abs_one, one_mul, smul_eq_mul]
    rfl
  rw [K, hl, h1, h2, K]
  simp only [zpow_zero, one_mul, smul_eq_mul]
  rw [inv_mul_eq_div]

/-- Limit as `c → 0⁺` of the basic integral. -/
lemma tendsto_K_zero :
    Tendsto (K 0) (𝓝[>] 0) (𝓝 (√(Real.pi / (1 / 2)) / 2)) := by
  have hg : ∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 2) * x ^ 2) = √(Real.pi / (1 / 2)) / 2 :=
    integral_gaussian_Ioi (1 / 2)
  rw [← hg]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => Real.exp (-(1 / 2) * x ^ 2)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact (integrableOn_zpow_wgt 0 hc).aestronglyMeasurable
  · filter_upwards with c
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : 0 < x := hx
    rw [zpow_zero, one_mul, Real.norm_of_nonneg (wgt_pos c x).le]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ c ^ 2 / (2 * x ^ 2) := by positivity
    nlinarith
  · exact (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : 0 < x := hx
    have hc : Tendsto (fun c : ℝ => (0 : ℝ) + (1 : ℝ) * (x ^ (0 : ℤ) * wgt c x)) (𝓝 0)
        (𝓝 (0 + 1 * (x ^ (0 : ℤ) * wgt 0 x))) := by
      apply Continuous.tendsto
      unfold wgt
      fun_prop
    have he : x ^ (0 : ℤ) * wgt 0 x = Real.exp (-(1 / 2) * x ^ 2) := by
      simp only [zpow_zero, one_mul, wgt]
      congr 1
      ring
    rw [he] at hc
    simpa using hc.mono_left nhdsWithin_le_nhds

/-- **The base case**: `∫₀^∞ exp(-x²/2 - c²/(2x²)) dx = √(π/2) exp(-c)`. -/
theorem K_zero {c : ℝ} (hc : 0 < c) : K 0 c = √(Real.pi / (1 / 2)) / 2 * Real.exp (-c) := by
  let g : ℝ → ℝ := fun d => K 0 d * Real.exp d
  have hder : ∀ {d : ℝ}, 0 < d → HasDerivAt g 0 d := by
    intro d hd
    have h1 := hasDerivAt_K 0 hd
    have h2 := h1.mul (Real.hasDerivAt_exp d)
    convert h2 using 1
    rw [show (0 : ℤ) - 2 = -2 by norm_num, K_neg_two d hd]
    field_simp
    ring
  have hconst : ∀ {a b : ℝ}, 0 < a → 0 < b → g a = g b := by
    intro a b ha hb
    apply IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi
      (fun d hd => (hder hd).differentiableAt.differentiableWithinAt)
      (fun d hd => (hder hd).deriv) ha hb
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 (√(Real.pi / (1 / 2)) / 2 * Real.exp 0)) :=
    tendsto_K_zero.mul ((Real.continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hev : g =ᶠ[𝓝[>] 0] fun _ => g c := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact hconst hd hc
  have hval := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  rw [Real.exp_zero, mul_one] at hval
  have : K 0 c * Real.exp c = _ := hval.symm
  rw [Real.exp_neg, eq_mul_inv_iff_mul_eq₀ (Real.exp_pos c).ne']
  exact this

/-- A polynomial with integer coefficients, evaluated at a real. -/
noncomputable def ev (P : ℤ[X]) (x : ℝ) : ℝ := aeval x P

lemma ev_add (P Q : ℤ[X]) (x : ℝ) : ev (P + Q) x = ev P x + ev Q x := by simp [ev]

lemma ev_monomial (i : ℕ) (a : ℤ) (x : ℝ) : ev (monomial i a) x = a * x ^ i := by
  simp [ev, aeval_monomial]

lemma hasDerivAt_ev (P : ℤ[X]) (x : ℝ) : HasDerivAt (ev P) (ev (derivative P) x) x := by
  have h := (P.map (Int.castRingHom ℝ)).hasDerivAt x
  have he : ∀ (Q : ℤ[X]) y, ev Q y = (Q.map (Int.castRingHom ℝ)).eval y := fun Q y => by
    simp [ev, aeval_def, eval₂_eq_eval_map]
  have hf : ev P = fun y => (P.map (Int.castRingHom ℝ)).eval y := funext (he P)
  rw [hf]
  convert h using 1
  rw [he, derivative_map]

/-- `F(P,p,c) = ∫₀^∞ x^p P(x) exp(-x²/2 - c²/(2x²)) dx`. -/
noncomputable def FP (P : ℤ[X]) (p : ℤ) (c : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ p * ev P x * wgt c x

lemma integrableOn_FP (P : ℤ[X]) (p : ℤ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ p * ev P x * wgt c x) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hs : IntegrableOn (fun x : ℝ => x ^ p * ev P x * wgt c x + x ^ p * ev Q x * wgt c x) (Ioi 0) :=
      hP.add hQ
    refine hs.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [ev_add]
    ring
  | monomial i a =>
    have hs : IntegrableOn (fun x : ℝ => (a : ℝ) * (x ^ (p + (i : ℤ)) * wgt c x)) (Ioi 0) :=
      (integrableOn_zpow_wgt (p + i) hc).const_mul (a : ℝ)
    refine hs.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : 0 < x := hx
    simp only [ev_monomial, zpow_add₀ hx'.ne', zpow_natCast]
    ring

lemma FP_add (P Q : ℤ[X]) (p : ℤ) {c : ℝ} (hc : 0 < c) :
    FP (P + Q) p c = FP P p c + FP Q p c := by
  unfold FP
  rw [← integral_add (integrableOn_FP P p hc) (integrableOn_FP Q p hc)]
  congr 1
  funext x
  rw [ev_add]
  ring

lemma FP_monomial (i : ℕ) (a : ℤ) (p : ℤ) (c : ℝ) :
    FP (monomial i a) p c = a * K (p + i) c := by
  unfold FP K
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  simp only [ev_monomial, zpow_add₀ hx'.ne', zpow_natCast]
  ring

/-- Differentiating `F` in `c`. -/
theorem hasDerivAt_FP (P : ℤ[X]) (p : ℤ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (FP P p) (-c * FP P (p - 2) c) c := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : FP (P + Q) p =ᶠ[𝓝 c] fun d => FP P p d + FP Q p d := by
      filter_upwards [Ioi_mem_nhds hc] with d hd
      exact FP_add P Q p hd
    refine ((hP.add hQ).congr_of_eventuallyEq he).congr_deriv ?_
    rw [FP_add P Q (p - 2) hc]
    ring
  | monomial i a =>
    have hf : FP (monomial i a) p = fun d => (a : ℝ) * K (p + i) d :=
      funext fun d => FP_monomial i a p d
    rw [hf, FP_monomial]
    refine ((hasDerivAt_K (p + i) hc).const_mul (a : ℝ)).congr_deriv ?_
    rw [show p + (i : ℤ) - 2 = p - 2 + i by ring]
    ring

/-- The integrand vanishes at both ends. -/
lemma tendsto_zpow_wgt (q : ℤ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ q * wgt c x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => x ^ q * wgt c x) atTop (𝓝 0) := by
  have hgauss : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  constructor
  · obtain ⟨C, hC, h⟩ := zpow_wgt_le (q - 1) hc
    have hup : Tendsto (fun x : ℝ => x * (C * Real.exp (-(x ^ 2 / 4)))) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun x : ℝ => x * (C * Real.exp (-(x ^ 2 / 4))) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      exact mul_nonneg (zpow_nonneg hx'.le _) (wgt_pos c x).le
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      have := mul_le_mul_of_nonneg_left (h le_rfl hx') hx'.le
      refine le_trans (le_of_eq ?_) this
      rw [zpow_sub₀ hx'.ne']
      simp only [zpow_one]
      field_simp
  · obtain ⟨C, hC, h⟩ := zpow_wgt_le q hc
    have hup : Tendsto (fun x : ℝ => C * Real.exp (-(x ^ 2 / 4))) atTop (𝓝 0) := by
      simpa using hgauss.const_mul C
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg (zpow_nonneg hx.le _) (wgt_pos c x).le
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact h le_rfl hx

lemma tendsto_FP_integrand (P : ℤ[X]) (q : ℤ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ q * ev P x * wgt c x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => x ^ q * ev P x * wgt c x) atTop (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    constructor
    · have := hP.1.add hQ.1
      rw [add_zero] at this
      refine this.congr fun x => ?_
      rw [ev_add]
      ring
    · have := hP.2.add hQ.2
      rw [add_zero] at this
      refine this.congr fun x => ?_
      rw [ev_add]
      ring
  | monomial i a =>
    obtain ⟨h0, h1⟩ := tendsto_zpow_wgt (q + i) hc
    constructor
    · have := h0.const_mul (a : ℝ)
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      simp only [ev_monomial, zpow_add₀ hx'.ne', zpow_natCast]
      ring
    · have := h1.const_mul (a : ℝ)
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [ev_monomial, zpow_add₀ hx.ne', zpow_natCast]
      ring

lemma hasDerivAt_wgt_x (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wgt c) ((-x + c ^ 2 * (x ^ 3)⁻¹) * wgt c x) x := by
  unfold wgt
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).neg
    convert this using 1
    simp
  have h2 : HasDerivAt (fun y : ℝ => c ^ 2 / (2 * y ^ 2)) (-(c ^ 2 * (x ^ 3)⁻¹)) x := by
    have hd : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul 2
    have := (hasDerivAt_const x (c ^ 2)).div hd (by positivity)
    convert this using 1
    field_simp
    ring
  have := (h1.sub h2).exp
  convert this using 1
  rw [mul_comm]
  congr 1
  ring

/-- **Integration by parts.** -/
theorem FP_ibp (P : ℤ[X]) (p : ℤ) {c : ℝ} (hc : 0 < c) :
    FP (X * P - derivative P) p c = p * FP P (p - 1) c + c ^ 2 * FP P (p - 3) c := by
  classical
  let A : ℝ → ℝ := fun x => x ^ p * ev P x * wgt c x
  let f : ℝ → ℝ := fun x => if 0 < x then A x else 0
  let f' : ℝ → ℝ := fun x => p * (x ^ (p - 1) * ev P x * wgt c x) +
    c ^ 2 * (x ^ (p - 3) * ev P x * wgt c x) - x ^ p * ev (X * P - derivative P) x * wgt c x
  have hA : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hfA : f =ᶠ[𝓝 x] A := by
      filter_upwards [Ioi_mem_nhds hx'] with y hy
      exact if_pos hy
    refine HasDerivAt.congr_of_eventuallyEq ?_ hfA
    have h1 : HasDerivAt (fun y : ℝ => y ^ p) ((p : ℝ) * x ^ (p - 1)) x :=
      hasDerivAt_zpow p x (Or.inl hx'.ne')
    have h := (h1.mul (hasDerivAt_ev P x)).mul (hasDerivAt_wgt_x c hx')
    convert h using 1
    have hev : ev (X * P - derivative P) x = x * ev P x - ev (derivative P) x := by
      simp [ev]
    simp only [f', hev, zpow_sub₀ hx'.ne', zpow_one, zpow_ofNat, Pi.mul_apply]
    field_simp
    ring
  have hi1 : IntegrableOn (fun x : ℝ => (p : ℝ) * (x ^ (p - 1) * ev P x * wgt c x)) (Ioi 0) :=
    (integrableOn_FP P (p - 1) hc).const_mul _
  have hi2 : IntegrableOn (fun x : ℝ => c ^ 2 * (x ^ (p - 3) * ev P x * wgt c x)) (Ioi 0) :=
    (integrableOn_FP P (p - 3) hc).const_mul _
  have hi3 := integrableOn_FP (X * P - derivative P) p hc
  have hint : IntegrableOn f' (Ioi 0) := (hi1.add hi2).sub hi3
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hlim := (tendsto_FP_integrand P p hc).1
    have hf0 : f 0 = 0 := if_neg (lt_irrefl _)
    rw [ContinuousWithinAt, hf0, ← Ioi_insert, nhdsWithin_insert, tendsto_sup]
    refine ⟨?_, ?_⟩
    · rw [tendsto_pure_left]
      intro s hs
      rw [hf0]
      exact mem_of_mem_nhds hs
    · refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (if_pos hx).symm
  have htop : Tendsto f atTop (𝓝 0) := by
    refine (tendsto_FP_integrand P p hc).2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (if_pos hx).symm
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hA hint htop
  have hf0 : f 0 = 0 := if_neg (lt_irrefl _)
  rw [hf0, sub_zero] at hmain
  have hsplit : ∫ x in Ioi (0 : ℝ), f' x =
      p * FP P (p - 1) c + c ^ 2 * FP P (p - 3) c - FP (X * P - derivative P) p c := by
    have e1 : ∫ x in Ioi (0 : ℝ), f' x =
        (∫ x in Ioi (0 : ℝ), ((p : ℝ) * (x ^ (p - 1) * ev P x * wgt c x) +
          c ^ 2 * (x ^ (p - 3) * ev P x * wgt c x))) -
        ∫ x in Ioi (0 : ℝ), x ^ p * ev (X * P - derivative P) x * wgt c x :=
      integral_sub (hi1.add hi2) hi3
    have e2 : ∫ x in Ioi (0 : ℝ), ((p : ℝ) * (x ^ (p - 1) * ev P x * wgt c x) +
          c ^ 2 * (x ^ (p - 3) * ev P x * wgt c x)) =
        (∫ x in Ioi (0 : ℝ), (p : ℝ) * (x ^ (p - 1) * ev P x * wgt c x)) +
        ∫ x in Ioi (0 : ℝ), c ^ 2 * (x ^ (p - 3) * ev P x * wgt c x) := integral_add hi1 hi2
    rw [e1, e2, integral_const_mul, integral_const_mul]
    rfl
  linarith

/-- **The Hermite–Gaussian integral.** -/
theorem hermite_integral (n : ℕ) {c : ℝ} (hc : 0 < c) :
    FP (hermite n) ((n : ℤ) - 2) c = √(Real.pi / (1 / 2)) / 2 * c ^ ((n : ℤ) - 1) * Real.exp (-c) := by
  induction n generalizing c with
  | zero =>
    have h0 : FP (hermite 0) (((0 : ℕ) : ℤ) - 2) c = K (-2) c := by
      rw [hermite_zero, ← monomial_zero_left]
      rw [FP_monomial]
      simp
    rw [h0, K_neg_two c hc, K_zero hc]
    simp only [Nat.cast_zero, zero_sub, zpow_neg_one]
    field_simp
  | succ n ih =>
    have hd := hasDerivAt_FP (hermite n) ((n : ℤ) - 2) hc
    have hf : FP (hermite n) ((n : ℤ) - 2) =ᶠ[𝓝 c] fun d =>
        √(Real.pi / (1 / 2)) / 2 * d ^ ((n : ℤ) - 1) * Real.exp (-d) := by
      filter_upwards [Ioi_mem_nhds hc] with d hd'
      exact ih hd'
    have hrhs : HasDerivAt (fun d : ℝ => √(Real.pi / (1 / 2)) / 2 * d ^ ((n : ℤ) - 1) * Real.exp (-d))
        (√(Real.pi / (1 / 2)) / 2 * (((n : ℤ) - 1 : ℤ) * c ^ ((n : ℤ) - 1 - 1)) * Real.exp (-c) +
          √(Real.pi / (1 / 2)) / 2 * c ^ ((n : ℤ) - 1) * (Real.exp (-c) * -1)) c := by
      exact ((hasDerivAt_zpow _ c (Or.inl hc.ne')).const_mul _).mul
        ((Real.hasDerivAt_exp (-c)).comp c (hasDerivAt_neg c))
    have huniq := (hd.congr_of_eventuallyEq hf.symm).unique hrhs
    rw [hermite_succ, show (((n + 1 : ℕ) : ℤ) - 2) = (n : ℤ) - 1 by push_cast; ring, FP_ibp _ _ hc,
      show (n : ℤ) - 1 - 1 = (n : ℤ) - 2 by ring, ih hc, show (n : ℤ) - 1 - 3 = (n : ℤ) - 2 - 2 by ring]
    have hsolve : c ^ 2 * FP (hermite n) ((n : ℤ) - 2 - 2) c = c * (-c * FP (hermite n) ((n : ℤ) - 2 - 2) c) * -1 := by
      ring
    rw [hsolve, huniq]
    simp only [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, zpow_sub₀ hc.ne', zpow_one,
      zpow_natCast]
    push_cast
    field_simp
    ring

/-- The parity of Hermite polynomials. -/
lemma hermite_comp_neg (n : ℕ) : (hermite n).comp (-X) = (-1) ^ n * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    have hd : (derivative (hermite n)).comp (-X) = -((-1) ^ n * derivative (hermite n)) := by
      have hC : ((-1 : ℤ[X]) ^ n) = C ((-1) ^ n) := by simp
      have h := congrArg derivative ih
      rw [derivative_comp, derivative_neg, derivative_X, hC, derivative_C_mul, ← hC] at h
      linear_combination -h
    rw [hermite_succ, sub_comp, mul_comp, X_comp, ih, hd, pow_succ]
    ring

lemma ev_hermite_neg (n : ℕ) (x : ℝ) : ev (hermite n) (-x) = (-1) ^ n * ev (hermite n) x := by
  have h := congrArg (fun P : ℤ[X] => aeval x P) (hermite_comp_neg n)
  simp only [aeval_comp, map_neg, aeval_X, map_mul, map_pow, map_one] at h
  exact h

/-- Passing to the variable `v = x²/α`. -/
theorem hermite_v_integral (n : ℕ) {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    ∫ v in Ioi (0 : ℝ), v ^ (((n : ℝ) - 3) / 2) *
        (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) * ev (hermite n) (√(α * v))) =
      α ^ (-(((n : ℝ) - 3) / 2)) * (2 / α) * FP (hermite n) ((n : ℤ) - 2) c := by
  let G : ℝ → ℝ := fun v => v ^ (((n : ℝ) - 3) / 2) *
    (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) * ev (hermite n) (√(α * v)))
  have h1 := integral_comp_mul_left_Ioi G 0 (inv_pos.mpr hα)
  rw [mul_zero] at h1
  have h2 := integral_comp_rpow_Ioi (fun y => G (α⁻¹ * y)) (p := 2) (by norm_num)
  have h3 : ∫ v in Ioi (0 : ℝ), G v = α⁻¹ * ∫ y in Ioi (0 : ℝ), G (α⁻¹ * y) := by
    rw [h1, smul_eq_mul, inv_inv, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  change ∫ v in Ioi (0 : ℝ), G v = _
  rw [h3, ← h2]
  unfold FP
  rw [show α ^ (-(((n : ℝ) - 3) / 2)) * (2 / α) * ∫ x in Ioi (0 : ℝ), x ^ ((n : ℤ) - 2) *
      ev (hermite n) x * wgt c x = α⁻¹ * ((2 * α ^ (-(((n : ℝ) - 3) / 2))) *
      ∫ x in Ioi (0 : ℝ), x ^ ((n : ℤ) - 2) * ev (hermite n) x * wgt c x) by
    field_simp]
  congr 1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  simp only [smul_eq_mul, G]
  have e1 : α⁻¹ * x ^ (2 : ℝ) = x ^ 2 / α := by
    rw [Real.rpow_two]
    field_simp
  have e2 : α * (x ^ 2 / α) = x ^ 2 := by field_simp
  have e3 : (x ^ 2 / α) ^ (((n : ℝ) - 3) / 2) =
      x ^ ((n : ℤ) - 3) * α ^ (-(((n : ℝ) - 3) / 2)) := by
    rw [Real.div_rpow (by positivity) hα.le, Real.rpow_neg hα.le, div_eq_mul_inv]
    congr 1
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx'.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have e4 : x ^ ((2 : ℝ) - 1) = x := by norm_num
  have e5 : x ^ ((n : ℤ) - 2) = x ^ ((n : ℤ) - 3) * x := by
    rw [show (n : ℤ) - 2 = (n : ℤ) - 3 + 1 by ring, zpow_add₀ hx'.ne', zpow_one]
  rw [e1, e2, e3, e4, e5, Real.sqrt_sq hx'.le, wgt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

/-- The same integral with a sign in the Hermite argument. -/
theorem hermite_v_integral_sign (n : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {α c : ℝ} (hα : 0 < α)
    (hc : 0 < c) :
    ∫ v in Ioi (0 : ℝ), v ^ (((n : ℝ) - 3) / 2) *
        (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) * ev (hermite n) (ε * √(α * v))) =
      ε ^ n * (α ^ (-(((n : ℝ) - 3) / 2)) * (2 / α) * (√(Real.pi / (1 / 2)) / 2 *
        c ^ ((n : ℤ) - 1) * Real.exp (-c))) := by
  rw [← hermite_integral n hc, ← hermite_v_integral n hα hc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rcases hε with rfl | rfl
  · simp
  · simp only [neg_mul, one_mul, ev_hermite_neg]
    ring

/-- **The binomial collapse.** The Hermite sum in the Fourier expansion of the lift is `(1+ε)^λ`
times a single exponential. It vanishes when `ε = -1`, which is why the lift is holomorphic. -/
theorem kernel_sum (lam : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {g m y : ℝ} (hg : 0 < g) (hm : 0 < m)
    (hy : 0 < y) :
    ∑ n ∈ Finset.range (lam + 1), (lam.choose n : ℝ) * (6 * g) ^ (lam - n) *
        (√(3 / Real.pi) / y) ^ n *
        ∫ v in Ioi (0 : ℝ), v ^ (((n : ℝ) - 3) / 2) *
          (Real.exp (-((2 * Real.pi * y * g * m) ^ 2 / (2 * (Real.pi * m ^ 2 / 3 * v))) -
            Real.pi * m ^ 2 / 3 * v / 2) * ev (hermite n) (ε * √(Real.pi * m ^ 2 / 3 * v))) =
      (1 + ε) ^ lam * (6 * g) ^ lam * ((Real.pi * m ^ 2 / 3) ^ ((3 : ℝ) / 2) *
        (2 / (Real.pi * m ^ 2 / 3)) * (√(Real.pi / (1 / 2)) / 2) *
        (2 * Real.pi * y * g * m)⁻¹ * Real.exp (-(2 * Real.pi * y * g * m))) := by
  have hpi := Real.pi_pos
  set α := Real.pi * m ^ 2 / 3 with hα
  have hαpos : 0 < α := by positivity
  set c := 2 * Real.pi * y * g * m with hc
  have hcpos : 0 < c := by positivity
  have hterm : ∀ n : ℕ, (√(3 / Real.pi) / y) ^ n * (α ^ (-(((n : ℝ) - 3) / 2)) * c ^ n) =
      (6 * g) ^ n * α ^ ((3 : ℝ) / 2) := by
    intro n
    have hsplit : α ^ (-(((n : ℝ) - 3) / 2)) = α ^ ((3 : ℝ) / 2) * (√α)⁻¹ ^ n := by
      rw [show -(((n : ℝ) - 3) / 2) = (3 : ℝ) / 2 + -((n : ℝ) / 2) by ring,
        Real.rpow_add hαpos, inv_pow, Real.rpow_neg hαpos.le, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast (α ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hαpos.le]
      congr 3
      ring
    have hbase : (√(3 / Real.pi) / y) * ((√α)⁻¹ * c) = 6 * g := by
      have hsq : √(3 / Real.pi) * (√α)⁻¹ = 3 / (Real.pi * m) := by
        rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
        rw [show 3 / Real.pi * α⁻¹ = (3 / (Real.pi * m)) ^ 2 by
          rw [hα]
          field_simp]
        exact Real.sqrt_sq (by positivity)
      calc (√(3 / Real.pi) / y) * ((√α)⁻¹ * c) = (√(3 / Real.pi) * (√α)⁻¹) * (c / y) := by ring
        _ = _ := by
          rw [hsq, hc]
          field_simp
          ring
    calc (√(3 / Real.pi) / y) ^ n * (α ^ (-(((n : ℝ) - 3) / 2)) * c ^ n)
        = ((√(3 / Real.pi) / y) * ((√α)⁻¹ * c)) ^ n * α ^ ((3 : ℝ) / 2) := by
          rw [hsplit, mul_pow, mul_pow]
          ring
      _ = _ := by rw [hbase]
  have hsum : ∀ n ∈ Finset.range (lam + 1), (lam.choose n : ℝ) * (6 * g) ^ (lam - n) *
        (√(3 / Real.pi) / y) ^ n *
        ∫ v in Ioi (0 : ℝ), v ^ (((n : ℝ) - 3) / 2) *
          (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) * ev (hermite n) (ε * √(α * v))) =
      (ε ^ n * 1 ^ (lam - n) * (lam.choose n : ℝ)) * ((6 * g) ^ lam * (α ^ ((3 : ℝ) / 2) * (2 / α) *
        (√(Real.pi / (1 / 2)) / 2) * c⁻¹ * Real.exp (-c))) := by
    intro n hn
    have hle : n ≤ lam := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [hermite_v_integral_sign n ε hε hαpos hcpos]
    have hcz : c ^ ((n : ℤ) - 1) = c ^ n * c⁻¹ := by
      rw [zpow_sub₀ hcpos.ne', zpow_natCast, zpow_one, div_eq_mul_inv]
    have hsplit6 : (6 * g) ^ lam = (6 * g) ^ (lam - n) * (6 * g) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hcz, hsplit6, one_pow]
    have ht := hterm n
    calc (lam.choose n : ℝ) * (6 * g) ^ (lam - n) * (√(3 / Real.pi) / y) ^ n *
          (ε ^ n * (α ^ (-(((n : ℝ) - 3) / 2)) * (2 / α) * (√(Real.pi / (1 / 2)) / 2 *
            (c ^ n * c⁻¹) * Real.exp (-c))))
        = (ε ^ n * 1 * (lam.choose n : ℝ)) * ((6 * g) ^ (lam - n) *
          ((√(3 / Real.pi) / y) ^ n * (α ^ (-(((n : ℝ) - 3) / 2)) * c ^ n)) * ((2 / α) *
            (√(Real.pi / (1 / 2)) / 2) * c⁻¹ * Real.exp (-c))) := by ring
      _ = _ := by rw [ht]; ring
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_mul, ← add_pow]
  ring

end RamanujanTau.ThetaLift
