/-
# `Λ(f, σ+it) e^{βt}` as a Fourier integral, for `k/2 ≤ σ ≤ k/2 + 1`

The σ-general version of `HardyZerosGeneral.Fourier` (which is the case `σ = k/2`), for a
level-one cusp form `f` of weight `k ≥ 12`; the Δ case is `HardyCountHafner.Fourier`.

* `|L(f,σ+it)| ≤ C (1+|t|)` for each `σ ∈ [k/2, k/2+1]` (convexity on `[k/2,(k+1)/2]`,
  absolute convergence beyond);
* `Phis f σ w = ∫ Λ(f,σ+it) e^{−itw} dt` is holomorphic on the strip `|Im w| < π/2`;
* Mellin inversion on `Re s = σ`: `Phis f σ u = 2π e^{σu} f(i e^u)`, and (identity theorem)
  `Phis f σ w = 2π Gs f σ w`, `Gs f σ w = e^{σw} f(i e^w)`, on the strip;
* Fourier inversion: `Λ(f,σ+it) e^{βt} = ∫ Phis f σ (−2πξ + iβ) e^{−2πiξt} dξ`.
-/
import RamanujanTau.HardyZerosGeneral.Cusp
import RamanujanTau.HardyCountHafner.Schur

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter Topology ModularForm
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
  RamanujanTau.HardyCountLinear
open scoped Real FourierTransform MatrixGroups

variable {k : ℕ}

/-- Growth of `L(f,σ+it)` at most linear in `|t|`, for `k/2 ≤ σ ≤ k/2 + 1`. -/
lemma fL_linear_growth (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) := by
  rcases le_or_gt σ (((k : ℝ) + 1) / 2) with h2 | h2
  · obtain ⟨C, hC0, hC⟩ := fL_convexity_strip f (ε := 1 / 2) (by norm_num)
    refine ⟨C, hC0, fun t => ?_⟩
    refine (hC σ t (by linarith) h2).trans ?_
    gcongr
    calc (1 + |t|) ^ (((k : ℝ) + 1) / 2 - σ + 1 / 2) ≤ (1 + |t|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
      _ = 1 + |t| := Real.rpow_one _
  · obtain ⟨D, hD0, hD⟩ := fL_bounded_of_gt f hk h2
    refine ⟨D, hD0, fun t => ?_⟩
    refine (hD _ (by simp)).trans ?_
    nlinarith [abs_nonneg t]

/-- `Λ(f, σ+it)`. -/
noncomputable def Zs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ t : ℝ) : ℂ := heckeLambda f ((σ : ℂ) + t * I)

lemma continuous_Zs (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (σ : ℝ) : Continuous (Zs f σ) :=
  (heckeLambda_entire f hk).continuous.comp (by fun_prop)

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -n := by
  intro h
  have := congrArg Complex.re h
  simp only [neg_re, natCast_re] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `‖Λ(f,σ+it)‖ ≤ K (1+|t|)^{k+2} e^{−π|t|/2}` for `k/2 ≤ σ ≤ k/2 + 1`. -/
lemma norm_Zs_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ} (h1 : (k : ℝ) / 2 ≤ σ)
    (h2 : σ ≤ (k : ℝ) / 2 + 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖Zs f σ t‖ ≤ K * (1 + |t|) ^ (k + 2) * Real.exp (-(π * |t|) / 2) := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := fL_linear_growth f (by omega) h1
  set G : ℝ := ((k + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π)
  have hG0 : 0 ≤ G := by positivity
  refine ⟨G * 2 ^ (k + 1) * C, by positivity, fun t => ?_⟩
  have hs : ∀ n : ℕ, ((σ : ℂ) + t * I : ℂ) ≠ -n :=
    ne_neg_nat_of_re_pos (by simp; linarith)
  rw [Zs, heckeLambda_eq_fL f hs, norm_mul, norm_mul]
  have h2π : ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ 1 := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [neg_re, add_re, mul_re, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im,
      mul_zero, sub_zero, add_zero, mul_one]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    linarith
  have hΓ := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := σ) (by linarith) k
    (by linarith) t
  set Tn := ‖(3 / 2 : ℂ) + t * I‖ with hTn
  have hT1 : 1 ≤ Tn := RamanujanTau.Stirling.one_le_norm_of_re (by simp; norm_num)
  have hTle : Tn ≤ 2 * (1 + |t|) := by
    refine (norm_add_le _ _).trans ?_
    have : ‖(t : ℂ) * I‖ = |t| := by simp
    rw [this]
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]
      norm_num
    rw [this]; linarith [abs_nonneg t]
  have hTpow : Tn ^ (σ - 1 / 2) ≤ (2 * (1 + |t|)) ^ (k + 1) := by
    calc Tn ^ (σ - 1 / 2) ≤ Tn ^ (((k + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
      _ = Tn ^ (k + 1) := Real.rpow_natCast _ _
      _ ≤ (2 * (1 + |t|)) ^ (k + 1) := pow_le_pow_left₀ (by positivity) hTle _
  have hΓ' : ‖Complex.Gamma ((σ : ℂ) + t * I)‖ ≤ G * (2 * (1 + |t|)) ^ (k + 1) *
      Real.exp (-(π * |t|) / 2) := by
    refine hΓ.trans ?_
    have := mul_le_mul_of_nonneg_left hTpow hG0
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  calc ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ‖Complex.Gamma ((σ : ℂ) + t * I)‖ *
        ‖fL f ((σ : ℂ) + t * I)‖
      ≤ 1 * (G * (2 * (1 + |t|)) ^ (k + 1) * Real.exp (-(π * |t|) / 2)) * (C * (1 + |t|)) := by
        gcongr; exact hC t
    _ = G * 2 ^ (k + 1) * C * (1 + |t|) ^ (k + 2) * Real.exp (-(π * |t|) / 2) := by
        rw [mul_pow, pow_succ (1 + |t|) (k + 1)]; ring

/-- Decay: for `b < π/2`, `‖Λ(f,σ+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹`. -/
theorem Zs_decay (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ} (h1 : (k : ℝ) / 2 ≤ σ)
    (h2 : σ ≤ (k : ℝ) / 2 + 1) {b : ℝ} (hb : b < π / 2) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Zs f σ t‖ * (1 + |t|) * Real.exp (b * |t|) ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := norm_Zs_le f hk h1 h2
  obtain ⟨K₁, hK₁0, hK₁⟩ := RamanujanTau.HardyZeros.one_add_pow_le_exp
    (c := π / 2 - b) (by linarith) (k + 5)
  refine ⟨K * K₁, fun t => ?_⟩
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h1 := hK t
  have h2 := hK₁ |t| ht0
  have hexp : Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
      Real.exp ((π / 2 - b) * |t|) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  calc ‖Zs f σ t‖ * (1 + |t|) * Real.exp (b * |t|) * (1 + t ^ 2)
      ≤ (K * (1 + |t|) ^ (k + 2) * Real.exp (-(π * |t|) / 2)) * (1 + |t|) *
          Real.exp (b * |t|) * (1 + |t|) ^ 2 := by gcongr
    _ = K * (1 + |t|) ^ (k + 5) * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by ring
    _ ≤ K * (K₁ * Real.exp ((π / 2 - b) * |t|)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by gcongr
    _ = K * K₁ * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
          Real.exp ((π / 2 - b) * |t|)) := by ring
    _ = K * K₁ := by rw [hexp, mul_one]

theorem integrable_Zs (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ} (h1 : (k : ℝ) / 2 ≤ σ)
    (h2 : σ ≤ (k : ℝ) / 2 + 1) {b : ℝ} (hb : b < π / 2) :
    Integrable fun t : ℝ => ‖Zs f σ t‖ * (1 + |t|) * Real.exp (b * |t|) := by
  obtain ⟨C, hC⟩ := Zs_decay f hk h1 h2 hb
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (((continuous_Zs f (by omega) σ).norm.mul (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hC t

/-- `Φ_σ(w) = ∫ Λ(f,σ+it) e^{−itw} dt`. -/
noncomputable def Phis (f : CuspForm 𝒮ℒ (k : ℤ)) (σ : ℝ) (w : ℂ) : ℂ :=
  ∫ t : ℝ, Zs f σ t * cexp (-(t * I * w))

/-- `G_σ(w) = e^{σw} f(i e^w)`. -/
noncomputable def Gs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ : ℝ) (w : ℂ) : ℂ :=
  cexp (σ * w) * Fc f (cexp w * I)

lemma integrable_Zs_mul (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) {w : ℂ} (hw : w ∈ strip) :
    Integrable fun t : ℝ => Zs f σ t * cexp (-(t * I * w)) := by
  have hb : |w.im| < π / 2 := hw
  refine (integrable_Zs f hk h1 h2 hb).mono'
    (((continuous_Zs f (by omega) σ).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_term]
  have h1 : ‖Zs f σ t‖ ≤ ‖Zs f σ t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  exact mul_le_mul h1 (exp_mul_im_le le_rfl) (Real.exp_pos _).le (by positivity)

/-- `Φ_σ` is holomorphic on the strip. -/
theorem differentiableOn_Phis (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) :
    DifferentiableOn ℂ (Phis f σ) strip := by
  intro w₀ hw₀
  have hcZ := continuous_Zs f (by omega) σ
  have ha : |w₀.im| < π / 2 := hw₀
  set ε : ℝ := (π / 2 - |w₀.im|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set b : ℝ := |w₀.im| + ε with hb
  have hbπ : b < π / 2 := by rw [hb, hε]; linarith
  have hball : ∀ w ∈ Metric.ball w₀ ε, |w.im| ≤ b := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 := abs_sub_abs_le_abs_sub w.im w₀.im
    rw [hb]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w (t : ℝ) => Zs f σ t * cexp (-(t * I * w)))
    (F' := fun w (t : ℝ) => Zs f σ t * (cexp (-(t * I * w)) * (-(t * I))))
    (x₀ := w₀) (bound := fun t => ‖Zs f σ t‖ * (1 + |t|) * Real.exp (b * |t|))
    (Metric.ball_mem_nhds w₀ hεpos)
    (Eventually.of_forall fun w => (hcZ.mul (by fun_prop)).aestronglyMeasurable)
    (integrable_Zs_mul f hk h1 h2 hw₀)
    ((hcZ.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => ?_)
    (integrable_Zs f hk h1 h2 hbπ)
    (Eventually.of_forall fun t w _ => ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [norm_mul, norm_mul, norm_cexp_term, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h1 := exp_mul_im_le (t := t) (hball w hw)
    have h2 : |t| ≤ 1 + |t| := by linarith
    calc ‖Zs f σ t‖ * (Real.exp (t * w.im) * |t|)
        ≤ ‖Zs f σ t‖ * (Real.exp (b * |t|) * (1 + |t|)) := by gcongr
      _ = ‖Zs f σ t‖ * (1 + |t|) * Real.exp (b * |t|) := by ring
  · have h := (((hasDerivAt_id w).const_mul ((t : ℂ) * I)).neg.cexp).const_mul (Zs f σ t)
    convert h using 1; simp [id]

theorem differentiableOn_Gs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ : ℝ) :
    DifferentiableOn ℂ (Gs f σ) strip := by
  have h1 : DifferentiableOn ℂ (fun w => Fc f (cexp w * I)) strip :=
    (Fc_differentiableOn f).comp
      (by fun_prop : Differentiable ℂ fun w => cexp w * I).differentiableOn
      fun w hw => im_exp_mul_I_pos hw
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => cexp (σ * w)).differentiableOn.mul h1

/-- Mellin inversion on the line `Re s = σ`: `Φ_σ(u) = 2π G_σ(u)`. -/
theorem Phis_eq_real (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) (u : ℝ) :
    Phis f σ u = 2 * π * Gs f σ u := by
  have hk1 : 1 ≤ k := by omega
  have hx : 0 < Real.exp u := Real.exp_pos u
  have hconv : MellinConvergent (heckeF f) ((σ : ℝ) : ℂ) := ((heckePair f hk1).hasMellin _).1
  have hvert : Complex.VerticalIntegrable (mellin (heckeF f)) σ := by
    unfold Complex.VerticalIntegrable
    have h := integrable_Zs f hk h1 h2 (b := 0) (by positivity)
    refine h.mono' (continuous_Zs f hk1 σ).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg t])
  have hcont : ContinuousAt (heckeF f) (Real.exp u) :=
    (continuousOn_heckeF f).continuousAt (Ioi_mem_nhds hx)
  have hinv := mellinInv_mellin_eq σ (heckeF f) hx hconv hvert hcont
  unfold mellinInv at hinv
  have hcp : ∀ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) =
      cexp (-(σ : ℂ) * u) * cexp (-(y * I * u)) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
      ← Complex.ofReal_log hx.le, Real.log_exp, ← Complex.exp_add]
    congr 1; ring
  have hint : (∫ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) •
      mellin (heckeF f) ((σ : ℂ) + y * I)) = cexp (-(σ : ℂ) * u) * Phis f σ u := by
    rw [Phis, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, hcp, Zs, heckeLambda]
    ring
  rw [hint] at hinv
  have hF : heckeF f (Real.exp u) = Fc f (cexp u * I) := by
    rw [heckeF, Fc, Complex.ofReal_exp]
  rw [hF] at hinv
  rw [Gs, ← hinv, Complex.real_smul]
  have hE : cexp ((σ : ℂ) * (u : ℂ)) * cexp (-(σ : ℂ) * u) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have h1 : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by push_cast; field_simp
  calc Phis f σ u = (((1 / (2 * π) : ℝ) : ℂ) * (2 * π)) * (cexp ((σ : ℂ) * (u : ℂ)) *
        cexp (-(σ : ℂ) * u)) * Phis f σ u := by rw [h1, hE]; ring
    _ = _ := by ring

/-- The identity theorem: `Φ_σ = 2π G_σ` on the strip. -/
theorem Phis_eq_strip (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) {w : ℂ} (hw : w ∈ strip) :
    Phis f σ w = 2 * π * Gs f σ w := by
  have hU := isOpen_strip
  have hf := (differentiableOn_Phis f hk h1 h2).analyticOnNhd hU
  have hg := ((differentiableOn_Gs f σ).const_mul (2 * π : ℂ)).analyticOnNhd hU
  have h0 : (0 : ℂ) ∈ strip := by simp [strip]; positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Phis f σ z = 2 * π * Gs f σ z := by
    have ht : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have e : (1 : ℂ) / ((n : ℂ) + 1) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [e]; exact Phis_eq_real f hk h1 h2 _
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_strip h0 hfreq hw

/-! ### Fourier inversion -/

/-- `F(t) = Λ(f,σ+it) e^{βt}`. -/
noncomputable def Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ β t : ℝ) : ℂ := Zs f σ t * cexp (β * t)

/-- Its Fourier-side density `ξ ↦ Φ_σ(−2πξ + iβ)`. -/
noncomputable def gS (f : CuspForm 𝒮ℒ (k : ℤ)) (σ β ξ : ℝ) : ℂ :=
  Phis f σ (((-2 * π * ξ : ℝ) : ℂ) + β * I)

lemma continuous_Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (σ β : ℝ) :
    Continuous (Fs f σ β) :=
  (continuous_Zs f hk σ).mul (by fun_prop)

lemma integrable_Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < π / 2) : Integrable (Fs f σ β) := by
  refine (integrable_Zs f hk h1 h2 hβ).mono' (continuous_Fs f (by omega) σ β).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Fs, norm_mul, Complex.norm_exp]
  have e : (((β : ℂ) * (t : ℂ))).re = β * t := by simp
  rw [e]
  have h1 : ‖Zs f σ t‖ ≤ ‖Zs f σ t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  have h2 : Real.exp (β * t) ≤ Real.exp (β * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hβ0)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

lemma fourier_Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ β ξ : ℝ) :
    𝓕 (Fs f σ β) ξ = Phis f σ (((2 * π * ξ : ℝ) : ℂ) + β * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Phis]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Fs, smul_eq_mul]
  rw [mul_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- **Fourier inversion**: `Λ(f,σ+it) e^{βt} = ∫ Φ_σ(−2πξ+iβ) e^{−2πiξt} dξ`, provided the
right-hand density is integrable. -/
theorem Fs_eq_fI (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {σ : ℝ}
    (h1 : (k : ℝ) / 2 ≤ σ) (h2 : σ ≤ (k : ℝ) / 2 + 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2)
    (hgi : Integrable (gS f σ β)) (t : ℝ) : Fs f σ β t = fI (gS f σ β) t := by
  have hFi : Integrable (𝓕 (Fs f σ β)) := by
    have : 𝓕 (Fs f σ β) = fun ξ => gS f σ β (-ξ) := by
      funext ξ; rw [fourier_Fs, gS]; congr 3; ring
    rw [this]; exact hgi.comp_neg
  have hinv := congrFun ((continuous_Fs f (by omega) σ β).fourierInv_fourier_eq
    (integrable_Fs f hk h1 h2 hβ0 hβ) hFi) t
  rw [← hinv, Real.fourierInv_eq', fI, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, gS, ph, fourier_Fs]
  rw [mul_comm]
  congr 1
  · congr 3; ring
  · congr 1; simp; ring

end RamanujanTau.HafnerGeneral
