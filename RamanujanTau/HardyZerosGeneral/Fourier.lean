/-
# `Z_f(t) = Λ(f, k/2+it)` as a Fourier transform, continued to the strip `|Im w| < π/2`

For a level-one cusp form `f` of weight `k ≥ 12`, `Φ(w) = ∫ Λ(f,k/2+it) e^{−itw} dt` is
holomorphic on the strip `|Im w| < π/2`.  Mellin inversion at `σ = k/2` gives
`Φ(u) = 2π e^{(k/2)u} f(i e^u)` for real `u`; by the identity theorem, at `w = iα`:

    ∫ Λ(f,k/2+it) e^{αt} dt = 2π e^{i(k/2)α} f(i e^{iα})        (|α| < π/2).

If the Fourier coefficients of `f` are real, `conj Z_f(t) = i^k Z_f(t)` and
`Z_f(−t) = i^k Z_f(t)` (functional equation).
-/
import RamanujanTau.HardyZerosGeneral.Decay

set_option autoImplicit false

namespace RamanujanTau.HardyZerosGeneral

open Complex ModularForm MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups
open RamanujanTau.HeckeConvexGeneral
open scoped Real ComplexConjugate

variable {k : ℕ}

/-- `Z_f(t) = Λ(f, k/2+it)`. -/
noncomputable def Zc (f : CuspForm 𝒮ℒ (k : ℤ)) (t : ℝ) : ℂ := heckeLambda f (sc k t)

/-- `Φ(w) = ∫ Z_f(t) e^{−itw} dt`. -/
noncomputable def Phi (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) : ℂ :=
  ∫ t : ℝ, Zc f t * cexp (-(t * I * w))

/-- `f` as a function on `ℂ` (junk off `ℍ`). -/
noncomputable def Fc (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℂ) : ℂ := (f ∘ ofComplex) z

/-- `G(w) = e^{(k/2)w} f(i e^w)`. -/
noncomputable def Gc (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) : ℂ :=
  cexp ((((k : ℝ) / 2 : ℝ) : ℂ) * w) * Fc f (cexp w * I)

/-- The strip `|Im w| < π/2`. -/
def strip : Set ℂ := {w : ℂ | |w.im| < π / 2}

lemma continuous_Zc (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : Continuous (Zc f) :=
  continuous_heckeLambda_line f hk

lemma norm_cexp_term (t : ℝ) (w : ℂ) : ‖cexp (-(t * I * w))‖ = Real.exp (t * w.im) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma exp_mul_im_le {t : ℝ} {w : ℂ} {b : ℝ} (hw : |w.im| ≤ b) :
    Real.exp (t * w.im) ≤ Real.exp (b * |t|) := by
  apply Real.exp_le_exp.mpr
  calc t * w.im ≤ |t * w.im| := le_abs_self _
    _ = |t| * |w.im| := abs_mul _ _
    _ ≤ |t| * b := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = b * |t| := mul_comm _ _

lemma integrable_Zc_mul (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {w : ℂ} (hw : w ∈ strip) :
    Integrable fun t : ℝ => Zc f t * cexp (-(t * I * w)) := by
  have hb : |w.im| < π / 2 := hw
  refine (integrable_heckeLambda_line f hk hb).mono'
    (((continuous_Zc f (by omega)).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_term]
  have h1 : ‖Zc f t‖ ≤ ‖Zc f t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  exact mul_le_mul h1 (exp_mul_im_le le_rfl) (Real.exp_pos _).le (by positivity)

/-- **`Φ` is holomorphic on the strip.** -/
theorem differentiableOn_Phi (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) :
    DifferentiableOn ℂ (Phi f) strip := by
  intro w₀ hw₀
  have ha : |w₀.im| < π / 2 := hw₀
  have hcZ := continuous_Zc f (by omega)
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
    (F := fun w (t : ℝ) => Zc f t * cexp (-(t * I * w)))
    (F' := fun w (t : ℝ) => Zc f t * (cexp (-(t * I * w)) * (-(t * I))))
    (x₀ := w₀) (bound := fun t => ‖Zc f t‖ * (1 + |t|) * Real.exp (b * |t|))
    (Metric.ball_mem_nhds w₀ hεpos)
    (Eventually.of_forall fun w => (hcZ.mul (by fun_prop)).aestronglyMeasurable)
    (integrable_Zc_mul f hk hw₀)
    ((hcZ.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => ?_)
    (integrable_heckeLambda_line f hk hbπ)
    (Eventually.of_forall fun t w _ => ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [norm_mul, norm_mul, norm_cexp_term, norm_neg, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h1 := exp_mul_im_le (t := t) (hball w hw)
    have h2 : |t| ≤ 1 + |t| := by linarith
    calc ‖Zc f t‖ * (Real.exp (t * w.im) * |t|)
        ≤ ‖Zc f t‖ * (Real.exp (b * |t|) * (1 + |t|)) := by gcongr
      _ = ‖Zc f t‖ * (1 + |t|) * Real.exp (b * |t|) := by ring
  · have h := (((hasDerivAt_id w).const_mul ((t : ℂ) * I)).neg.cexp).const_mul (Zc f t)
    convert h using 1; simp [id]

lemma Fc_differentiableOn (f : CuspForm 𝒮ℒ (k : ℤ)) :
    DifferentiableOn ℂ (Fc f) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)

lemma im_exp_mul_I_pos {w : ℂ} (hw : w ∈ strip) : 0 < (cexp w * I).im := by
  have hb : |w.im| < π / 2 := hw
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩
  have e : (cexp w * I).im = Real.exp w.re * Real.cos w.im := by
    simp [Complex.exp_re]
  rw [e]; positivity

/-- **`G` is holomorphic on the strip.** -/
theorem differentiableOn_Gc (f : CuspForm 𝒮ℒ (k : ℤ)) : DifferentiableOn ℂ (Gc f) strip := by
  have h1 : DifferentiableOn ℂ (fun w => Fc f (cexp w * I)) strip :=
    (Fc_differentiableOn f).comp
      (by fun_prop : Differentiable ℂ fun w => cexp w * I).differentiableOn
      fun w hw => im_exp_mul_I_pos hw
  exact (by fun_prop : Differentiable ℂ
    fun w : ℂ => cexp ((((k : ℝ) / 2 : ℝ) : ℂ) * w)).differentiableOn.mul h1

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
theorem Phi_eq_real (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (u : ℝ) :
    Phi f u = 2 * π * Gc f u := by
  have hk1 : 1 ≤ k := by omega
  set κ : ℝ := (k : ℝ) / 2 with hκ
  have hx : 0 < Real.exp u := Real.exp_pos u
  have hconv : MellinConvergent (heckeF f) ((κ : ℝ) : ℂ) := ((heckePair f hk1).hasMellin _).1
  have hvert : Complex.VerticalIntegrable (mellin (heckeF f)) κ := by
    unfold Complex.VerticalIntegrable
    have h := integrable_heckeLambda_line f hk (b := 0) (by positivity)
    refine h.mono' (continuous_heckeLambda_line f hk1).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg t])
  have hcont : ContinuousAt (heckeF f) (Real.exp u) :=
    (continuousOn_heckeF f).continuousAt (Ioi_mem_nhds hx)
  have hinv := mellinInv_mellin_eq κ (heckeF f) hx hconv hvert hcont
  unfold mellinInv at hinv
  have hcp : ∀ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-((κ : ℂ) + y * I)) =
      cexp (-(κ : ℂ) * u) * cexp (-(y * I * u)) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
      ← Complex.ofReal_log hx.le, Real.log_exp, ← Complex.exp_add]
    congr 1; ring
  have hint : (∫ y : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-((κ : ℂ) + y * I)) •
      mellin (heckeF f) ((κ : ℂ) + y * I)) = cexp (-(κ : ℂ) * u) * Phi f u := by
    rw [Phi, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, hcp, Zc, sc, heckeLambda]
    ring
  rw [hint] at hinv
  have hF : heckeF f (Real.exp u) = Fc f (cexp u * I) := by
    rw [heckeF, Fc, Complex.ofReal_exp]
  rw [hF] at hinv
  rw [Gc, ← hinv, Complex.real_smul]
  have hE : cexp ((κ : ℂ) * (u : ℂ)) * cexp (-(κ : ℂ) * u) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have h1 : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by push_cast; field_simp
  calc Phi f u = (((1 / (2 * π) : ℝ) : ℂ) * (2 * π)) * (cexp ((κ : ℂ) * (u : ℂ)) *
        cexp (-(κ : ℂ) * u)) * Phi f u := by rw [h1, hE]; ring
    _ = _ := by ring

/-- **The identity theorem**: `Φ = 2π G` on the whole strip. -/
theorem Phi_eq_strip (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {w : ℂ} (hw : w ∈ strip) :
    Phi f w = 2 * π * Gc f w := by
  have hU := isOpen_strip
  have hf := (differentiableOn_Phi f hk).analyticOnNhd hU
  have hg := ((differentiableOn_Gc f).const_mul (2 * π : ℂ)).analyticOnNhd hU
  have h0 : (0 : ℂ) ∈ strip := by simp [strip]; positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Phi f z = 2 * π * Gc f z := by
    have ht : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have e : (1 : ℂ) / ((n : ℂ) + 1) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [e]; exact Phi_eq_real f hk _
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_strip h0 hfreq hw

/-- **The key identity**: `∫ Λ(f,k/2+it) e^{αt} dt = 2π e^{i(k/2)α} f(i e^{iα})`,
`|α| < π/2`. -/
theorem integral_Zc_exp (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {α : ℝ} (hα : |α| < π / 2) :
    ∫ t : ℝ, Zc f t * cexp (α * t) =
      2 * π * (cexp ((((k : ℝ) / 2 : ℝ) : ℂ) * (α * I)) * Fc f (cexp (α * I) * I)) := by
  have hw : (α * I : ℂ) ∈ strip := by simpa [strip] using hα
  have h := Phi_eq_strip f hk hw
  rw [Phi, Gc] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  congr 2
  ring_nf; rw [I_sq]; ring

/-! ### Realness and parity -/

/-- Real coefficients make `f(it)` real. -/
lemma heckeF_conj (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) {t : ℝ}
    (ht : 0 < t) : conj (heckeF f t) = heckeF f t := by
  have h := hasSum_heckeF f ht
  have h' := Complex.hasSum_conj'.mpr h
  refine h'.unique (h.congr_fun fun n => ?_)
  rw [map_mul, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr (hreal n)]

lemma heckeF_real (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) {t : ℝ}
    (ht : 0 < t) : heckeF f t = ((heckeF f t).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (heckeF_conj f hreal ht)).symm

/-- `Λ(f, conj s) = conj Λ(f,s)` for real coefficients. -/
theorem heckeLambda_conj (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) (s : ℂ) :
    heckeLambda f (conj s) = conj (heckeLambda f s) := by
  rw [heckeLambda, mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [smul_eq_mul, map_mul]
  rw [heckeF_real f hreal ht, Complex.conj_ofReal,
    ← RamanujanTau.HeckeZeros.ofReal_cpow_conj ht.le]
  simp

lemma conj_sc (t : ℝ) : conj (sc k t) = (k : ℂ) - sc k t := by
  rw [sc, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma sc_neg (t : ℝ) : sc k (-t) = (k : ℂ) - sc k t := by
  unfold sc; push_cast; ring

/-- `conj Z_f(t) = i^k Z_f(t)`. -/
theorem Zc_conj (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (hreal : ∀ n, (coef f n).im = 0)
    (t : ℝ) : conj (Zc f t) = I ^ k * Zc f t := by
  rw [Zc, ← heckeLambda_conj f hreal, conj_sc, heckeLambda_functional_equation f hk]

/-- `Z_f(−t) = i^k Z_f(t)`. -/
theorem Zc_neg (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (t : ℝ) :
    Zc f (-t) = I ^ k * Zc f t := by
  rw [Zc, Zc, sc_neg, heckeLambda_functional_equation f hk]

end RamanujanTau.HardyZerosGeneral
