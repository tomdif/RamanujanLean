/-
# `Z(t) = Λ(6+it)` as a Fourier transform, continued to the strip `|Im w| < π/2`

`Φ(w) = ∫ Λ(6+it) e^{−itw} dt` is holomorphic on the strip `|Im w| < π/2` (decay of `Λ` on the
critical line).  For real `u`, Mellin inversion (`mellinInv_mellin_eq`) at `x = e^u` gives
`Φ(u) = 2π e^{6u} Δ(i e^u)`.  Both sides are holomorphic on the strip, so by the identity
theorem `Φ(w) = 2π e^{6w} Δ(i e^w)` throughout; at `w = iα`:

    ∫ Λ(6+it) e^{αt} dt = 2π e^{6iα} Δ(i e^{iα})        (|α| < π/2).

Also `Z(t) = Λ(6+it)` is real and even (functional equation + real coefficients).
-/
import RamanujanTau.HardyZeros.Decay

set_option autoImplicit false

namespace RamanujanTau.HardyZeros

open Complex ModularForm MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups
open RamanujanTau.HeckeL
open scoped Real ComplexConjugate

/-- `Z(t) = Λ(6+it)` (complex-valued; real by `Zc_conj`). -/
noncomputable def Zc (t : ℝ) : ℂ := heckeLambda (6 + t * I)

/-- `Φ(w) = ∫ Z(t) e^{−itw} dt`. -/
noncomputable def Phi (w : ℂ) : ℂ := ∫ t : ℝ, Zc t * cexp (-(t * I * w))

/-- `Δ` as a function on `ℂ` (junk off `ℍ`). -/
noncomputable def Dc (z : ℂ) : ℂ := (Δf ∘ ofComplex) z

/-- `G(w) = e^{6w} Δ(i e^w)`. -/
noncomputable def Gc (w : ℂ) : ℂ := cexp (6 * w) * Dc (cexp w * I)

/-- The strip `|Im w| < π/2`. -/
def strip : Set ℂ := {w : ℂ | |w.im| < π / 2}

lemma continuous_Zc : Continuous Zc := continuous_heckeLambda_line

lemma norm_cexp_term (t : ℝ) (w : ℂ) : ‖cexp (-(t * I * w))‖ = Real.exp (t * w.im) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma exp_mul_im_le {t : ℝ} {w : ℂ} {b : ℝ} (hw : |w.im| ≤ b) :
    Real.exp (t * w.im) ≤ Real.exp (b * |t|) := by
  apply Real.exp_le_exp.mpr
  calc t * w.im ≤ |t * w.im| := le_abs_self _
    _ = |t| * |w.im| := abs_mul _ _
    _ ≤ |t| * b := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = b * |t| := mul_comm _ _

lemma integrable_Zc_mul {w : ℂ} (hw : w ∈ strip) :
    Integrable fun t : ℝ => Zc t * cexp (-(t * I * w)) := by
  have hb : |w.im| < π / 2 := hw
  refine (integrable_heckeLambda_line hb).mono'
    ((continuous_Zc.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_term]
  have h1 : ‖Zc t‖ ≤ ‖Zc t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  exact mul_le_mul h1 (exp_mul_im_le le_rfl) (Real.exp_pos _).le (by positivity)

/-- **`Φ` is holomorphic on the strip.** -/
theorem differentiableOn_Phi : DifferentiableOn ℂ Phi strip := by
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
    (F := fun w (t : ℝ) => Zc t * cexp (-(t * I * w)))
    (F' := fun w (t : ℝ) => Zc t * (cexp (-(t * I * w)) * (-(t * I))))
    (x₀ := w₀) (bound := fun t => ‖Zc t‖ * (1 + |t|) * Real.exp (b * |t|))
    (Metric.ball_mem_nhds w₀ hεpos)
    (Eventually.of_forall fun w => (continuous_Zc.mul (by fun_prop)).aestronglyMeasurable)
    (integrable_Zc_mul hw₀)
    ((continuous_Zc.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => ?_)
    (integrable_heckeLambda_line hbπ)
    (Eventually.of_forall fun t w _ => ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [norm_mul, norm_mul, norm_cexp_term, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h1 := exp_mul_im_le (t := t) (hball w hw)
    have h2 : |t| ≤ 1 + |t| := by linarith
    calc ‖Zc t‖ * (Real.exp (t * w.im) * |t|)
        ≤ ‖Zc t‖ * (Real.exp (b * |t|) * (1 + |t|)) := by gcongr
      _ = ‖Zc t‖ * (1 + |t|) * Real.exp (b * |t|) := by ring
  · have h := (((hasDerivAt_id w).const_mul ((t : ℂ) * I)).neg.cexp).const_mul (Zc t)
    convert h using 1; simp [id]

lemma Dc_differentiableOn : DifferentiableOn ℂ Dc {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))

lemma im_exp_mul_I_pos {w : ℂ} (hw : w ∈ strip) : 0 < (cexp w * I).im := by
  have hb : |w.im| < π / 2 := hw
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩
  have e : (cexp w * I).im = Real.exp w.re * Real.cos w.im := by
    simp [Complex.exp_re]
  rw [e]; positivity

/-- **`G` is holomorphic on the strip.** -/
theorem differentiableOn_Gc : DifferentiableOn ℂ Gc strip := by
  have h1 : DifferentiableOn ℂ (fun w => Dc (cexp w * I)) strip :=
    Dc_differentiableOn.comp (by fun_prop : Differentiable ℂ fun w => cexp w * I).differentiableOn
      fun w hw => im_exp_mul_I_pos hw
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => cexp (6 * w)).differentiableOn.mul h1

lemma isOpen_strip : IsOpen strip := by
  have : strip = Complex.im ⁻¹' Ioo (-(π / 2)) (π / 2) := by
    ext w; simp [strip, abs_lt]
  rw [this]; exact isOpen_Ioo.preimage Complex.continuous_im

lemma isPreconnected_strip : IsPreconnected strip := by
  have : strip = {c : ℂ | c.im < π / 2} ∩ {c : ℂ | -(π / 2) < c.im} := by
    ext w; simp [strip, abs_lt, and_comm]
  rw [this]
  exact ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _)).isPreconnected

/-- **Mellin inversion on the real axis**: `Φ(u) = 2π G(u)`. -/
theorem Phi_eq_real (u : ℝ) : Phi u = 2 * π * Gc u := by
  have hx : 0 < Real.exp u := Real.exp_pos u
  have hconv : MellinConvergent heckeF ((6 : ℝ) : ℂ) := (heckePair.hasMellin _).1
  have hvert : Complex.VerticalIntegrable (mellin heckeF) 6 := by
    unfold Complex.VerticalIntegrable
    rw [← heckeLambda_eq_mellin]
    have h := integrable_heckeLambda_line (b := 0) (by positivity)
    refine h.mono' (by
      have : Continuous fun y : ℝ => heckeLambda ((6 : ℝ) + y * I) :=
        heckeLambda_entire.continuous.comp (by fun_prop)
      exact this.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
    have e : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
    rw [e]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg t])
  have hcont : ContinuousAt heckeF (Real.exp u) :=
    continuousOn_heckeF.continuousAt (Ioi_mem_nhds hx)
  have hinv := mellinInv_mellin_eq 6 heckeF hx hconv hvert hcont
  rw [← heckeLambda_eq_mellin] at hinv
  unfold mellinInv at hinv
  have hcp : ∀ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-(((6 : ℝ) : ℂ) + y * I)) =
      cexp (-6 * u) * cexp (-(y * I * u)) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
      ← Complex.ofReal_log hx.le, Real.log_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hint : (∫ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-(((6 : ℝ) : ℂ) + y * I)) •
      heckeLambda (((6 : ℝ) : ℂ) + y * I)) = cexp (-6 * u) * Phi u := by
    rw [Phi, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, hcp, Zc]
    have e : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
    rw [e]; ring
  rw [hint] at hinv
  have hF : heckeF (Real.exp u) = Dc (cexp u * I) := by
    rw [heckeF, Dc, Complex.ofReal_exp]
  rw [hF] at hinv
  rw [Gc, ← hinv, Complex.real_smul]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have hE : cexp (6 * (u : ℂ)) * cexp (-6 * u) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have h1 : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by push_cast; field_simp
  calc Phi u = (((1 / (2 * π) : ℝ) : ℂ) * (2 * π)) * (cexp (6 * (u : ℂ)) * cexp (-6 * u)) *
        Phi u := by rw [h1, hE]; ring
    _ = _ := by ring

/-- **The identity theorem**: `Φ = 2π G` on the whole strip. -/
theorem Phi_eq_strip {w : ℂ} (hw : w ∈ strip) : Phi w = 2 * π * Gc w := by
  have hU := isOpen_strip
  have hf := differentiableOn_Phi.analyticOnNhd hU
  have hg := (differentiableOn_Gc.const_mul (2 * π : ℂ)).analyticOnNhd hU
  have h0 : (0 : ℂ) ∈ strip := by simp [strip]; positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Phi z = 2 * π * Gc z := by
    have ht : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have e : (1 : ℂ) / ((n : ℂ) + 1) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [e]; exact Phi_eq_real _
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_strip h0 hfreq hw

/-- **The key identity**: `∫ Λ(6+it) e^{αt} dt = 2π e^{6iα} Δ(i e^{iα})` for `|α| < π/2`. -/
theorem integral_Zc_exp {α : ℝ} (hα : |α| < π / 2) :
    ∫ t : ℝ, Zc t * cexp (α * t) = 2 * π * (cexp (6 * (α * I)) * Dc (cexp (α * I) * I)) := by
  have hw : (α * I : ℂ) ∈ strip := by simpa [strip] using hα
  have h := Phi_eq_strip hw
  rw [Phi, Gc] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  congr 2
  ring_nf; rw [I_sq]; ring

/-! ### Realness and evenness -/

theorem Zc_conj (t : ℝ) : conj (Zc t) = Zc t := by
  rw [Zc, ← RamanujanTau.HeckeZeros.heckeLambda_conj, ← heckeLambda_functional_equation]
  congr 1
  apply Complex.ext <;> simp; norm_num

theorem Zc_neg (t : ℝ) : Zc (-t) = Zc t := by
  rw [Zc, Zc, ← heckeLambda_functional_equation (6 + t * I)]
  congr 1; push_cast; ring

/-- The real function `Z(t) = Λ(6+it)`. -/
noncomputable def Zr (t : ℝ) : ℝ := (Zc t).re

theorem Zc_eq_Zr (t : ℝ) : Zc t = (Zr t : ℂ) := (Complex.conj_eq_iff_re.mp (Zc_conj t)).symm

lemma continuous_Zr : Continuous Zr := Complex.continuous_re.comp continuous_Zc

lemma Zr_neg (t : ℝ) : Zr (-t) = Zr t := by rw [Zr, Zr, Zc_neg]

end RamanujanTau.HardyZeros
