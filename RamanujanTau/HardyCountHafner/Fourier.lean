/-
# `Λ(Δ, σ+it) e^{βt}` as a Fourier integral, for `6 ≤ σ ≤ 7`

The σ-general version of `HardyZeros.Fourier` (which is the case `σ = 6`).

* `Phis σ w = ∫ Λ(σ+it) e^{−itw} dt` is holomorphic on the strip `|Im w| < π/2`;
* Mellin inversion on the line `Re s = σ` gives `Phis σ u = 2π e^{σu} Δ(i e^u)` for real `u`, hence
  (identity theorem) `Phis σ w = 2π Gs σ w`, `Gs σ w = e^{σw} Δ(i e^w)`, on the whole strip;
* Fourier inversion (`Continuous.fourierInv_fourier_eq`): for `0 ≤ β < π/2`,
  `Λ(σ+it) e^{βt} = ∫ Phis σ (−2πξ + iβ) e^{−2πiξt} dξ`.
-/
import RamanujanTau.HardyZeros.Cusp
import RamanujanTau.HardyCount.Contour
import RamanujanTau.HardyCountHafner.Schur

set_option autoImplicit false

namespace RamanujanTau.HardyCountHafner

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
  RamanujanTau.HardyCountLinear
open scoped Real FourierTransform

/-- `Λ(σ+it)`. -/
noncomputable def Zs (σ t : ℝ) : ℂ := heckeLambda ((σ : ℂ) + t * I)

lemma continuous_Zs (σ : ℝ) : Continuous (Zs σ) :=
  heckeLambda_entire.continuous.comp (by fun_prop)

/-- `‖Λ(σ+it)‖ ≤ K (1+|t|)^8 e^{−π|t|/2}` for `6 ≤ σ ≤ 7`. -/
lemma norm_Zs_le {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖Zs σ t‖ ≤ K * (1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2) := by
  obtain ⟨C, hC0, hC⟩ := tauL_right_half_bound (ε := 1 / 2) (by norm_num) le_rfl
  set G : ℝ := ((5 + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π)
  have hG0 : 0 ≤ G := by positivity
  refine ⟨G * 2 ^ 7 * C, by positivity, fun t => ?_⟩
  have hs : ∀ n : ℕ, ((σ : ℂ) + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp; linarith)
  rw [Zs, heckeLambda_eq_tauL hs, norm_mul, norm_mul]
  have h2π : ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ 1 := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [neg_re, add_re, mul_re, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, add_zero, mul_one]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    linarith
  have hΓ := RamanujanTau.Stirling.norm_Gamma_le_stirling (σ := σ) (by linarith) 5
    (by push_cast; linarith) t
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
  have hTpow : Tn ^ (σ - 1 / 2) ≤ (2 * (1 + |t|)) ^ 7 := by
    calc Tn ^ (σ - 1 / 2) ≤ Tn ^ ((7 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
      _ = Tn ^ 7 := Real.rpow_natCast _ _
      _ ≤ (2 * (1 + |t|)) ^ 7 := pow_le_pow_left₀ (by positivity) hTle 7
  have hΓ' : ‖Complex.Gamma ((σ : ℂ) + t * I)‖ ≤ G * (2 * (1 + |t|)) ^ 7 *
      Real.exp (-(π * |t|) / 2) := by
    refine hΓ.trans ?_
    have := mul_le_mul_of_nonneg_left hTpow hG0
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hL := hC σ t h6
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at hL
  calc ‖(2 * π : ℂ) ^ (-((σ : ℂ) + t * I))‖ * ‖Complex.Gamma ((σ : ℂ) + t * I)‖ *
        ‖tauL ((σ : ℂ) + t * I)‖
      ≤ 1 * (G * (2 * (1 + |t|)) ^ 7 * Real.exp (-(π * |t|) / 2)) * (C * (1 + |t|)) := by
        gcongr
    _ = G * 2 ^ 7 * C * (1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2) := by ring

/-- Decay: for `b < π/2`, `‖Λ(σ+it)‖ (1+|t|) e^{b|t|} ≤ C (1+t²)⁻¹`. -/
theorem Zs_decay {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {b : ℝ} (hb : b < π / 2) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Zs σ t‖ * (1 + |t|) * Real.exp (b * |t|) ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := norm_Zs_le h6 h7
  obtain ⟨K₁, hK₁0, hK₁⟩ := RamanujanTau.HardyZeros.one_add_pow_le_exp
    (c := π / 2 - b) (by linarith) 11
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
  calc ‖Zs σ t‖ * (1 + |t|) * Real.exp (b * |t|) * (1 + t ^ 2)
      ≤ (K * (1 + |t|) ^ 8 * Real.exp (-(π * |t|) / 2)) * (1 + |t|) * Real.exp (b * |t|) *
          (1 + |t|) ^ 2 := by gcongr
    _ = K * (1 + |t|) ^ 11 * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by ring
    _ ≤ K * (K₁ * Real.exp ((π / 2 - b) * |t|)) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|)) := by gcongr
    _ = K * K₁ * (Real.exp (-(π * |t|) / 2) * Real.exp (b * |t|) *
          Real.exp ((π / 2 - b) * |t|)) := by ring
    _ = K * K₁ := by rw [hexp, mul_one]

theorem integrable_Zs {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {b : ℝ} (hb : b < π / 2) :
    Integrable fun t : ℝ => ‖Zs σ t‖ * (1 + |t|) * Real.exp (b * |t|) := by
  obtain ⟨C, hC⟩ := Zs_decay h6 h7 hb
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (((continuous_Zs σ).norm.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hC t

/-- `Φ_σ(w) = ∫ Λ(σ+it) e^{−itw} dt`. -/
noncomputable def Phis (σ : ℝ) (w : ℂ) : ℂ := ∫ t : ℝ, Zs σ t * cexp (-(t * I * w))

/-- `G_σ(w) = e^{σw} Δ(i e^w)`. -/
noncomputable def Gs (σ : ℝ) (w : ℂ) : ℂ := cexp (σ * w) * Dc (cexp w * I)

lemma integrable_Zs_mul {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {w : ℂ} (hw : w ∈ strip) :
    Integrable fun t : ℝ => Zs σ t * cexp (-(t * I * w)) := by
  have hb : |w.im| < π / 2 := hw
  refine (integrable_Zs h6 h7 hb).mono'
    (((continuous_Zs σ).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_term]
  have h1 : ‖Zs σ t‖ ≤ ‖Zs σ t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  exact mul_le_mul h1 (exp_mul_im_le le_rfl) (Real.exp_pos _).le (by positivity)

/-- `Φ_σ` is holomorphic on the strip. -/
theorem differentiableOn_Phis {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) :
    DifferentiableOn ℂ (Phis σ) strip := by
  intro w₀ hw₀
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
    (F := fun w (t : ℝ) => Zs σ t * cexp (-(t * I * w)))
    (F' := fun w (t : ℝ) => Zs σ t * (cexp (-(t * I * w)) * (-(t * I))))
    (x₀ := w₀) (bound := fun t => ‖Zs σ t‖ * (1 + |t|) * Real.exp (b * |t|))
    (Metric.ball_mem_nhds w₀ hεpos)
    (Eventually.of_forall fun w => ((continuous_Zs σ).mul (by fun_prop)).aestronglyMeasurable)
    (integrable_Zs_mul h6 h7 hw₀)
    (((continuous_Zs σ).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => ?_)
    (integrable_Zs h6 h7 hbπ)
    (Eventually.of_forall fun t w _ => ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [norm_mul, norm_mul, norm_cexp_term, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h1 := exp_mul_im_le (t := t) (hball w hw)
    have h2 : |t| ≤ 1 + |t| := by linarith
    calc ‖Zs σ t‖ * (Real.exp (t * w.im) * |t|)
        ≤ ‖Zs σ t‖ * (Real.exp (b * |t|) * (1 + |t|)) := by gcongr
      _ = ‖Zs σ t‖ * (1 + |t|) * Real.exp (b * |t|) := by ring
  · have h := (((hasDerivAt_id w).const_mul ((t : ℂ) * I)).neg.cexp).const_mul (Zs σ t)
    convert h using 1; simp [id]

theorem differentiableOn_Gs (σ : ℝ) : DifferentiableOn ℂ (Gs σ) strip := by
  have h1 : DifferentiableOn ℂ (fun w => Dc (cexp w * I)) strip :=
    Dc_differentiableOn.comp (by fun_prop : Differentiable ℂ fun w => cexp w * I).differentiableOn
      fun w hw => im_exp_mul_I_pos hw
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => cexp (σ * w)).differentiableOn.mul h1

/-- Mellin inversion on the line `Re s = σ`: `Φ_σ(u) = 2π G_σ(u)`. -/
theorem Phis_eq_real {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) (u : ℝ) :
    Phis σ u = 2 * π * Gs σ u := by
  have hx : 0 < Real.exp u := Real.exp_pos u
  have hconv : MellinConvergent heckeF ((σ : ℝ) : ℂ) := (heckePair.hasMellin _).1
  have hvert : Complex.VerticalIntegrable (mellin heckeF) σ := by
    unfold Complex.VerticalIntegrable
    rw [← heckeLambda_eq_mellin]
    have h := integrable_Zs h6 h7 (b := 0) (by positivity)
    refine h.mono' (continuous_Zs σ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg t])
  have hcont : ContinuousAt heckeF (Real.exp u) :=
    continuousOn_heckeF.continuousAt (Ioi_mem_nhds hx)
  have hinv := mellinInv_mellin_eq σ heckeF hx hconv hvert hcont
  rw [← heckeLambda_eq_mellin] at hinv
  unfold mellinInv at hinv
  have hcp : ∀ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-(((σ : ℝ) : ℂ) + y * I)) =
      cexp (-σ * u) * cexp (-(y * I * u)) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
      ← Complex.ofReal_log hx.le, Real.log_exp, ← Complex.exp_add]
    congr 1; ring
  have hint : (∫ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-(((σ : ℝ) : ℂ) + y * I)) •
      heckeLambda (((σ : ℝ) : ℂ) + y * I)) = cexp (-σ * u) * Phis σ u := by
    rw [Phis, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, hcp, Zs]
    ring
  rw [hint] at hinv
  have hF : heckeF (Real.exp u) = Dc (cexp u * I) := by
    rw [heckeF, Dc, Complex.ofReal_exp]
  rw [hF] at hinv
  rw [Gs, ← hinv, Complex.real_smul]
  have hE : cexp (σ * (u : ℂ)) * cexp (-σ * u) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have h1 : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by push_cast; field_simp
  calc Phis σ u = (((1 / (2 * π) : ℝ) : ℂ) * (2 * π)) * (cexp (σ * (u : ℂ)) * cexp (-σ * u)) *
        Phis σ u := by rw [h1, hE]; ring
    _ = _ := by ring

/-- The identity theorem: `Φ_σ = 2π G_σ` on the strip. -/
theorem Phis_eq_strip {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {w : ℂ} (hw : w ∈ strip) :
    Phis σ w = 2 * π * Gs σ w := by
  have hU := isOpen_strip
  have hf := (differentiableOn_Phis h6 h7).analyticOnNhd hU
  have hg := ((differentiableOn_Gs σ).const_mul (2 * π : ℂ)).analyticOnNhd hU
  have h0 : (0 : ℂ) ∈ strip := by simp [strip]; positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Phis σ z = 2 * π * Gs σ z := by
    have ht : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have e : (1 : ℂ) / ((n : ℂ) + 1) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [e]; exact Phis_eq_real h6 h7 _
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_strip h0 hfreq hw

/-! ### Fourier inversion -/

/-- `F(t) = Λ(σ+it) e^{βt}`. -/
noncomputable def Fs (σ β t : ℝ) : ℂ := Zs σ t * cexp (β * t)

/-- Its Fourier-side density `ξ ↦ Φ_σ(−2πξ + iβ)`. -/
noncomputable def gS (σ β ξ : ℝ) : ℂ := Phis σ (((-2 * π * ξ : ℝ) : ℂ) + β * I)

lemma continuous_Fs (σ β : ℝ) : Continuous (Fs σ β) :=
  (continuous_Zs σ).mul (by fun_prop)

lemma integrable_Fs {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < π / 2) : Integrable (Fs σ β) := by
  refine (integrable_Zs h6 h7 hβ).mono' (continuous_Fs σ β).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Fs, norm_mul, Complex.norm_exp]
  have e : (((β : ℂ) * (t : ℂ))).re = β * t := by simp
  rw [e]
  have h1 : ‖Zs σ t‖ ≤ ‖Zs σ t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  have h2 : Real.exp (β * t) ≤ Real.exp (β * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hβ0)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

lemma fourier_Fs (σ β ξ : ℝ) :
    𝓕 (Fs σ β) ξ = Phis σ (((2 * π * ξ : ℝ) : ℂ) + β * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Phis]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Fs, smul_eq_mul]
  rw [mul_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- **Fourier inversion**: `Λ(σ+it) e^{βt} = ∫ Φ_σ(−2πξ+iβ) e^{−2πiξt} dξ`, provided the
right-hand density is integrable. -/
theorem Fs_eq_fI {σ : ℝ} (h6 : 6 ≤ σ) (h7 : σ ≤ 7) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2)
    (hgi : Integrable (gS σ β)) (t : ℝ) : Fs σ β t = fI (gS σ β) t := by
  have hFi : Integrable (𝓕 (Fs σ β)) := by
    have : 𝓕 (Fs σ β) = fun ξ => gS σ β (-ξ) := by
      funext ξ; rw [fourier_Fs, gS]; congr 3; ring
    rw [this]; exact hgi.comp_neg
  have hinv := congrFun ((continuous_Fs σ β).fourierInv_fourier_eq
    (integrable_Fs h6 h7 hβ0 hβ) hFi) t
  rw [← hinv, Real.fourierInv_eq', fI, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, gS, ph, fourier_Fs]
  rw [mul_comm]
  congr 1
  · congr 3; ring
  · congr 1; simp; ring

end RamanujanTau.HardyCountHafner
