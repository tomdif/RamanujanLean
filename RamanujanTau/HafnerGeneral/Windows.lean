/-
# Windowed moments for a general cusp form: mean square over centres, and the sign lower bound

Let `f ∈ S_{2p+2}(SL₂(ℤ))` and suppose `Z(t) = Λ(f,p+1+it) = Y(t)·c` with `Y` real and
`‖c‖ = 1` (with real coefficients: `c = 1`, `Y = Re Z` if `k ≡ 0 mod 4`; `c = i`, `Y = Im Z`
if `k ≡ 2 mod 4`).  Put `Iw α R t₀ = ∫ Y(t) e^{αt} tri_R(t − t₀) dt`.

* `integral_Zc_exp_tri`: `∫ Z(t) e^{αt} tri_R(t−t₀) dt = ∫ triHat_R(ξ) e^{−2πiξt₀} Φ(−2πξ+iα) dξ`
  (the general version of `HardyCount.integral_Zc_exp_tri`);
* `mean_sq_Iw`: `∫_T^{2T} Iw(t₀)² dt₀ ≤ 4 S² R³`, `S = 2πM/cos^{p+1}α`
  (Schur, `HardyCountLinear.integral_tri_norm_fI_sq_le`; `|Iw| = |fI gw|` as `‖c‖ = 1`);
* `Iw_lower`: if `Y` has no zero on `[t₀−2r, t₀+2r]` then
  `r e^{−3} c_Z (T/2)^{p+1/2} ∫_{t₀−r}^{t₀+r} |L(f,p+1+it)| dt ≤ |Iw(π/2 − 1/T, 2r, t₀)|`.
-/
import RamanujanTau.HafnerGeneral.Window
import RamanujanTau.HardyCount.Gaps

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter Function ModularForm
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
  RamanujanTau.HardyCountLinear
open RamanujanTau.HardyCount (tri triHat tri_nonneg tri_le tri_of_abs_le tri_of_le_abs
  continuous_tri integrable_tri integrable_triHat triHat_nonneg tri_inversion triC fourier_triC
  integrable_triC const_sign abs_integral_eq_of_sign)
open scoped Real MatrixGroups

variable {k : ℕ}

lemma integrable_norm_Zc_exp (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {α : ℝ} (ha0 : 0 ≤ α)
    (ha : α < π / 2) : Integrable fun t : ℝ => ‖Zc f t‖ * Real.exp (α * t) := by
  refine (integrable_heckeLambda_line f hk ha).mono'
    (((continuous_Zc f (by omega)).norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change ‖Zc f t‖ * _ ≤ ‖Zc f t‖ * (1 + |t|) * Real.exp (α * |t|)
  have h1 : ‖Zc f t‖ ≤ ‖Zc f t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  have h2 : Real.exp (α * t) ≤ Real.exp (α * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) ha0)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

lemma continuous_triHat' {h : ℝ} (hh : 0 ≤ h) : Continuous fun ξ => triHat h ξ := by
  have e : (fun ξ => triHat h ξ) = fun ξ => (FourierTransform.fourier (triC h) ξ).re := by
    funext ξ; rw [fourier_triC hh]; simp
  rw [e]
  exact Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ (integrable_triC h))

/-- **Fourier side of the windowed moment** (general `f`). -/
theorem integral_Zc_exp_tri (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {α : ℝ} (ha0 : 0 ≤ α)
    (ha : α < π / 2) {h : ℝ} (hh : 0 ≤ h) (t₀ : ℝ) :
    ∫ t : ℝ, Zc f t * cexp (α * t) * (tri h (t - t₀) : ℂ) =
      ∫ ξ : ℝ, (triHat h ξ : ℂ) * cexp (-(↑(2 * π * ξ * t₀) * I)) *
        Phi f (((-2 * π * ξ : ℝ) : ℂ) + α * I) := by
  set F : ℝ → ℝ → ℂ := fun t ξ =>
    Zc f t * cexp (α * t) * (cexp (↑(2 * π * ξ * (t - t₀)) * I) * (triHat h ξ : ℂ)) with hF
  have hcont : Continuous (uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => Zc f p.1 :=
      (continuous_Zc f (by omega)).comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => (triHat h p.2 : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_triHat' hh).comp continuous_snd)
    have h3 : Continuous fun p : ℝ × ℝ => cexp (α * p.1) := by fun_prop
    have h4 : Continuous fun p : ℝ × ℝ => cexp (↑(2 * π * p.2 * (p.1 - t₀)) * I) := by fun_prop
    exact (h1.mul h3).mul (h4.mul h2)
  have hint : Integrable (uncurry F) (volume.prod volume) := by
    refine ((integrable_norm_Zc_exp f hk ha0 ha).mul_prod (integrable_triHat hh)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hF, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (triHat_nonneg hh)]
    simp
  have hL : ∀ t : ℝ, Zc f t * cexp (α * t) * (tri h (t - t₀) : ℂ) = ∫ ξ, F t ξ := by
    intro t
    rw [tri_inversion hh, hF, ← integral_const_mul]
  rw [integral_congr_ae (Eventually.of_forall hL), integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hF]
  rw [Phi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  have e : cexp (↑α * ↑t) * cexp (↑(2 * π * ξ * (t - t₀)) * I) =
      cexp (-(↑(2 * π * ξ * t₀) * I)) * cexp (-(↑t * I * (((-2 * π * ξ : ℝ) : ℂ) + ↑α * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]; ring
  calc Zc f t * cexp (↑α * ↑t) * (cexp (↑(2 * π * ξ * (t - t₀)) * I) * ↑(triHat h ξ))
      = ↑(triHat h ξ) * Zc f t * (cexp (↑α * ↑t) * cexp (↑(2 * π * ξ * (t - t₀)) * I)) := by
        ring
    _ = _ := by rw [e]; ring

/-- The windowed moment of the real function `Y`. -/
noncomputable def Iw (Y : ℝ → ℝ) (α R t₀ : ℝ) : ℝ := ∫ t, Y t * Real.exp (α * t) * tri R (t - t₀)

/-- Its Fourier-side density. -/
noncomputable def gw (f : CuspForm 𝒮ℒ (k : ℤ)) (α R ξ : ℝ) : ℂ :=
  (triHat R ξ : ℂ) * Phi f (((-2 * π * ξ : ℝ) : ℂ) + α * I)

lemma mem_strip_line {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) (ξ : ℝ) :
    (((-2 * π * ξ : ℝ) : ℂ) + α * I) ∈ strip := by
  show |(((-2 * π * ξ : ℝ) : ℂ) + α * I).im| < π / 2
  simp [abs_of_nonneg ha0, ha]

lemma continuous_gw (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {α : ℝ} (ha0 : 0 ≤ α)
    (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) : Continuous (gw f α R) := by
  unfold gw
  refine (Complex.continuous_ofReal.comp (continuous_triHat' hR)).mul ?_
  exact (differentiableOn_Phi f hk).continuousOn.comp_continuous (by fun_prop)
    (mem_strip_line ha0 ha)

variable {p : ℕ}

lemma norm_gw_le (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {M : ℝ}
    (hM : ∀ z : ℂ, 0 < z.im → ‖Fc f z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    (hM0 : 0 ≤ M) {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) (ξ : ℝ) :
    ‖gw f α R ξ‖ ≤ 2 * π * M / Real.cos α ^ (p + 1) * triHat R ξ := by
  have hw := mem_strip_line ha0 ha ξ
  have hα : |α| < π / 2 := by rw [abs_of_nonneg ha0]; exact ha
  rw [gw, Phi_eq_strip f hk hw, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (triHat_nonneg hR), GeneralCuspMoments.norm_two_pi_C]
  have h3 := GeneralCuspMoments.norm_Gc_le f hM (u := -2 * π * ξ) hα
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha⟩
  have he : Real.exp (-(π * Real.cos α * Real.exp (-2 * π * ξ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos Real.pi_pos hc) (Real.exp_pos (-2 * π * ξ)); linarith
  have h4 : ‖Gc f (((-2 * π * ξ : ℝ) : ℂ) + α * I)‖ ≤ M / Real.cos α ^ (p + 1) := by
    refine h3.trans ?_
    have : 0 ≤ M / Real.cos α ^ (p + 1) := by positivity
    calc M / Real.cos α ^ (p + 1) * Real.exp (-(π * Real.cos α * Real.exp (-2 * π * ξ)))
        ≤ M / Real.cos α ^ (p + 1) * 1 := by gcongr
      _ = _ := mul_one _
  have := triHat_nonneg (h := R) (ξ := ξ) hR
  calc triHat R ξ * (2 * π * ‖Gc f (((-2 * π * ξ : ℝ) : ℂ) + α * I)‖)
      ≤ triHat R ξ * (2 * π * (M / Real.cos α ^ (p + 1))) := by gcongr
    _ = _ := by ring

/-- A real representation `Z = Y·c`, `‖c‖ = 1`. -/
structure Rep (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (Y : ℝ → ℝ) (c : ℂ) : Prop where
  norm_c : ‖c‖ = 1
  eq : ∀ t, Zc f t = (Y t : ℂ) * c

lemma Rep.continuous {f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)} {Y : ℝ → ℝ} {c : ℂ}
    (hR : Rep f Y c) : Continuous Y := by
  have hc0 : c ≠ 0 := by intro h; have := hR.norm_c; rw [h, norm_zero] at this; norm_num at this
  have : Y = fun t => (Zc f t / c).re := by
    funext t; rw [hR.eq, mul_div_cancel_right₀ _ hc0, ofReal_re]
  rw [this]; exact continuous_re.comp ((continuous_Zc f (by omega)).div_const c)

lemma Rep.abs_eq {f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)} {Y : ℝ → ℝ} {c : ℂ}
    (hR : Rep f Y c) (t : ℝ) : |Y t| = ‖Zc f t‖ := by
  rw [hR.eq, norm_mul, hR.norm_c, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma Iw_eq_fI {f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)} (hk : 12 ≤ 2 * p + 2) {Y : ℝ → ℝ}
    {c : ℂ} (hR : Rep f Y c) {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR0 : 0 ≤ R)
    (t₀ : ℝ) : (Iw Y α R t₀ : ℂ) * c = fI (gw f α R) t₀ := by
  have hcast : ((Iw Y α R t₀ : ℝ) : ℂ) * c =
      ∫ t : ℝ, Zc f t * cexp (α * t) * (tri R (t - t₀) : ℂ) := by
    rw [Iw, show ((∫ t, Y t * Real.exp (α * t) * tri R (t - t₀) : ℝ) : ℂ) =
        ∫ t, ((Y t * Real.exp (α * t) * tri R (t - t₀) : ℝ) : ℂ) from integral_ofReal.symm,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hR.eq]
    push_cast
    ring
  rw [hcast, integral_Zc_exp_tri f hk ha0 ha hR0 t₀, fI]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [gw, ph]
  ring

lemma abs_Iw_eq {f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)} (hk : 12 ≤ 2 * p + 2) {Y : ℝ → ℝ}
    {c : ℂ} (hR : Rep f Y c) {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR0 : 0 ≤ R)
    (t₀ : ℝ) : |Iw Y α R t₀| = ‖fI (gw f α R) t₀‖ := by
  rw [← Iw_eq_fI hk hR ha0 ha hR0, norm_mul, hR.norm_c, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- **Mean square of the windowed moments over centres** (general `f`). -/
theorem mean_sq_Iw (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Y : ℝ → ℝ) (c : ℂ), Rep f Y c → ∀ α : ℝ, 0 ≤ α → α < π / 2 →
    ∀ R : ℝ, 0 ≤ R → Continuous (Iw Y α R) ∧ ∀ T : ℝ, 0 < T →
      ∫ t₀ in Icc T (2 * T), Iw Y α R t₀ ^ 2 ≤
        4 * (2 * π * M / Real.cos α ^ (p + 1)) ^ 2 * R ^ 3 := by
  obtain ⟨M, hM0, hM⟩ := GeneralCuspMoments.exists_cusp_bound f
  refine ⟨M, hM0, fun Y c hRep α ha0 ha R hR => ?_⟩
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha⟩
  have hc0 : c ≠ 0 := by
    intro h; have := hRep.norm_c; rw [h, norm_zero] at this; norm_num at this
  set S : ℝ := 2 * π * M / Real.cos α ^ (p + 1) with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hgc := continuous_gw f hk ha0 ha hR
  have hgb := norm_gw_le f hk hM hM0 ha0 ha hR
  have hIc : Continuous (Iw Y α R) := by
    have : Iw Y α R = fun t₀ => (fI (gw f α R) t₀ / c).re := by
      funext t₀
      rw [← Iw_eq_fI hk hRep ha0 ha hR, mul_div_cancel_right₀ _ hc0, ofReal_re]
    rw [this]
    exact Complex.continuous_re.comp ((continuous_fI hgc hR hgb).div_const c)
  refine ⟨hIc, fun T hT => ?_⟩
  have hBd : ∀ t₀, |Iw Y α R t₀| ≤ ∫ ξ, ‖gw f α R ξ‖ := by
    intro t₀
    rw [abs_Iw_eq hk hRep ha0 ha hR]
    exact norm_fI_le t₀
  have hmain := integral_tri_norm_fI_sq_le hgc hS0 hR hgb (le_of_lt hT) (3 * T / 2)
  have hsq : ∀ t₀, ‖fI (gw f α R) t₀‖ ^ 2 = Iw Y α R t₀ ^ 2 := by
    intro t₀
    rw [← abs_Iw_eq hk hRep ha0 ha hR, sq_abs]
  simp only [hsq] at hmain
  have hWI : Integrable fun t₀ => tri T (t₀ - 3 * T / 2) * Iw Y α R t₀ ^ 2 := by
    have h1 : Integrable fun t₀ => tri T (t₀ - 3 * T / 2) :=
      (integrable_tri T).comp_sub_right _
    have h2 := h1.bdd_mul (f := fun t₀ => Iw Y α R t₀ ^ 2) (c := (∫ ξ, ‖gw f α R ξ‖) ^ 2)
      (hIc.pow 2).aestronglyMeasurable (Eventually.of_forall fun t₀ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hBd t₀) 2)
    refine h2.congr (Eventually.of_forall fun t₀ => ?_)
    simp only; ring
  have hpt : ∀ t₀ ∈ Icc T (2 * T), Iw Y α R t₀ ^ 2 ≤
      2 / T * (tri T (t₀ - 3 * T / 2) * Iw Y α R t₀ ^ 2) := by
    intro t₀ ht₀
    have habs : |t₀ - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    have htri : T / 2 ≤ tri T (t₀ - 3 * T / 2) := by
      rw [tri_of_abs_le (by linarith)]; linarith
    have hsq0 := sq_nonneg (Iw Y α R t₀)
    rw [← mul_assoc]
    have : 1 ≤ 2 / T * tri T (t₀ - 3 * T / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith
    nlinarith
  calc ∫ t₀ in Icc T (2 * T), Iw Y α R t₀ ^ 2
      ≤ ∫ t₀ in Icc T (2 * T), 2 / T * (tri T (t₀ - 3 * T / 2) * Iw Y α R t₀ ^ 2) :=
        setIntegral_mono_on ((hIc.pow 2).integrableOn_Icc) (hWI.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ t₀, 2 / T * (tri T (t₀ - 3 * T / 2) * Iw Y α R t₀ ^ 2) :=
        setIntegral_le_integral (hWI.const_mul _) (Eventually.of_forall fun t₀ =>
          mul_nonneg (by positivity) (mul_nonneg (tri_nonneg _ _) (sq_nonneg _)))
    _ = 2 / T * ∫ t₀, tri T (t₀ - 3 * T / 2) * Iw Y α R t₀ ^ 2 := integral_const_mul _ _
    _ ≤ 2 / T * (2 * S ^ 2 * R ^ 3 * T) := by gcongr
    _ = 4 * S ^ 2 * R ^ 3 := by field_simp; ring

/-- The point `p + 1 + it` of the critical line. -/
lemma sc_eq (p : ℕ) (t : ℝ) : sc (2 * p + 2) t = ((((p : ℝ) + 1 : ℝ)) : ℂ) + t * I := by
  unfold sc; rw [half_k']

/-- The Stirling constant `c_Z = (√π/3) e^{−10} (2π)^{−(p+1)}`. -/
noncomputable def cZ (p : ℕ) : ℝ := Real.sqrt π / 3 * Real.exp (-10) * (2 * π) ^ (-((p : ℝ) + 1))

lemma cZ_pos (p : ℕ) : 0 < cZ p := by unfold cZ; positivity

/-- **Stirling lower bound for `Z`**: `c_Z t^{p+1/2} |L(f,p+1+it)| ≤ |Z(t)| e^{πt/2}`, `t ≥ 0`. -/
lemma Zc_lower (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hp : 1 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    cZ p * t ^ ((p : ℝ) + 1 / 2) * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ ≤
      ‖Zc f t‖ * Real.exp (π * t / 2) := by
  set s : ℂ := (((p : ℝ) + 1 : ℝ) : ℂ) + t * I with hsdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : ∀ n : ℕ, s ≠ -n := ne_neg_nat_of_re_pos (by rw [hsdef]; simp; linarith)
  have hZ : ‖Zc f t‖ = ‖(2 * π : ℂ) ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖fL f s‖ := by
    rw [Zc, sc_eq, ← hsdef, heckeLambda_eq_fL f hs, norm_mul, norm_mul]
  have h2π : ‖(2 * π : ℂ) ^ (-s)‖ = (2 * π) ^ (-((p : ℝ) + 1)) := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1; rw [hsdef]; simp
  have hΓ := RamanujanTau.Stirling.stirling_le_norm_Gamma (σ := (p : ℝ) + 1) (by linarith) t
  have hT : t ^ ((p : ℝ) + 1 / 2) ≤ ‖(3 / 2 : ℂ) + t * I‖ ^ (((p : ℝ) + 1) - 1 / 2) := by
    have h1 : t ≤ ‖(3 / 2 : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((3 / 2 : ℂ) + t * I)
      have e : ((3 / 2 : ℂ) + t * I).im = t := by simp
      rw [e] at this
      exact (le_abs_self t).trans this
    rw [show ((p : ℝ) + 1) - 1 / 2 = (p : ℝ) + 1 / 2 by ring]
    exact Real.rpow_le_rpow ht h1 (by linarith)
  have hE : Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2) = 1 := by
    rw [abs_of_nonneg ht, ← Real.exp_add]; ring_nf; simp
  rw [hZ, h2π]
  have hL0 := norm_nonneg (fL f s)
  have hp0 : 0 ≤ (2 * π) ^ (-((p : ℝ) + 1)) := by positivity
  calc cZ p * t ^ ((p : ℝ) + 1 / 2) * ‖fL f s‖
      = (2 * π) ^ (-((p : ℝ) + 1)) * (Real.sqrt π / 3 * Real.exp (-10) *
          t ^ ((p : ℝ) + 1 / 2) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2))) * ‖fL f s‖ := by
        rw [hE, cZ]; ring
    _ ≤ (2 * π) ^ (-((p : ℝ) + 1)) * (Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (((p : ℝ) + 1) - 1 / 2) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2))) * ‖fL f s‖ := by
        gcongr
    _ = (2 * π) ^ (-((p : ℝ) + 1)) * ((Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ (((p : ℝ) + 1) - 1 / 2) * Real.exp (-(π * |t|) / 2)) *
          Real.exp (π * t / 2)) * ‖fL f s‖ := by ring
    _ ≤ (2 * π) ^ (-((p : ℝ) + 1)) * (‖Complex.Gamma s‖ * Real.exp (π * t / 2)) *
          ‖fL f s‖ := by
        gcongr
    _ = _ := by ring

/-- **The sign lower bound** for a window free of zeros of `Y`. -/
theorem Iw_lower (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {Y : ℝ → ℝ}
    {c : ℂ} (hRep : Rep f Y c) {T t₀ r : ℝ} (hT : 1 ≤ T) (ht₀ : T ≤ t₀) (ht₀' : t₀ ≤ 2 * T)
    (hr : 0 < r) (hrT : r ≤ T / 2) (hno : ∀ t ∈ Icc (t₀ - 2 * r) (t₀ + 2 * r), Y t ≠ 0) :
    r * Real.exp (-3) * cZ p * (T / 2) ^ ((p : ℝ) + 1 / 2) *
        ∫ t in (t₀ - r)..(t₀ + r), ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ ≤
      |Iw Y (π / 2 - 1 / T) (2 * r) t₀| := by
  have hTpos : 0 < T := by linarith
  set α : ℝ := π / 2 - 1 / T with hα
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three]
  have hαπ : α < π / 2 := by rw [hα]; linarith
  have hYc := hRep.continuous
  have hsign := const_sign hYc hno
  set w : ℝ → ℝ := fun t => Real.exp (α * t) * tri (2 * r) (t - t₀) with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => mul_nonneg (Real.exp_pos _).le (tri_nonneg _ _)
  have hwsupp : ∀ t ∉ Icc (t₀ - 2 * r) (t₀ + 2 * r), w t = 0 := by
    intro t ht
    have : 2 * r ≤ |t - t₀| := by
      by_contra hc
      push Not at hc
      exact ht ⟨by linarith [(abs_lt.mp hc).1], by linarith [(abs_lt.mp hc).2]⟩
    simp [hw, tri_of_le_abs this]
  have hEq := abs_integral_eq_of_sign hw0 hwsupp hsign
  have hI : (∫ t, Y t * w t) = Iw Y α (2 * r) t₀ := by
    simp only [hw, Iw, mul_assoc]
  rw [hI] at hEq
  rw [hEq]
  set a' : ℝ := t₀ - r with ha'
  set b' : ℝ := t₀ + r with hb'
  have hab' : a' ≤ b' := by rw [ha', hb']; linarith
  set P : ℝ := (T / 2) ^ ((p : ℝ) + 1 / 2) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hcontL : Continuous fun t : ℝ => ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ :=
    ((fL_entire f (by omega)).continuous.comp (by fun_prop)).norm
  have hcontW : Continuous fun t => |Y t| * w t := by
    simp only [hw]
    exact hYc.abs.mul ((by fun_prop : Continuous fun t => Real.exp (α * t)).mul
      ((continuous_tri (2 * r)).comp (by fun_prop)))
  have hintW : Integrable fun t => |Y t| * w t := by
    refine ((integrable_norm_Zc_exp f hk hα0 hαπ).mul_const (2 * r)).mono'
      hcontW.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simp only [hw, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (tri_nonneg _ _), hRep.abs_eq]
    rw [abs_norm, mul_assoc]
    gcongr
    exact tri_le _ _ (by linarith)
  have hpt : ∀ t ∈ uIcc a' b', r * Real.exp (-3) * cZ p * P *
      ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ ≤ |Y t| * w t := by
    intro t ht
    rw [uIcc_of_le hab'] at ht
    have ht0 : T / 2 ≤ t := by linarith [ht.1]
    have htpos : 0 ≤ t := by linarith
    have htri : r ≤ tri (2 * r) (t - t₀) := by
      have habs : |t - t₀| ≤ r := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      rw [tri_of_abs_le (by linarith)]; linarith
    have hexp : Real.exp (π * t / 2) * Real.exp (-3) ≤ Real.exp (α * t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : t / T ≤ 3 := by rw [div_le_iff₀ hTpos]; linarith [ht.2]
      have e : α * t = π * t / 2 - t / T := by rw [hα]; field_simp
      rw [e]; linarith
    have hPt : P ≤ t ^ ((p : ℝ) + 1 / 2) :=
      Real.rpow_le_rpow (by linarith) ht0 (by positivity)
    have hlow := Zc_lower f (by omega) htpos
    rw [← hRep.abs_eq] at hlow
    have hL0 := norm_nonneg (fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I))
    have hcz := cZ_pos p
    have hZ0 := abs_nonneg (Y t)
    calc r * Real.exp (-3) * cZ p * P * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖
        ≤ r * Real.exp (-3) * (cZ p * t ^ ((p : ℝ) + 1 / 2) *
            ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖) := by
          have : cZ p * P * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ ≤
              cZ p * t ^ ((p : ℝ) + 1 / 2) * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖ := by
            gcongr
          calc r * Real.exp (-3) * cZ p * P * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖
              = r * Real.exp (-3) * (cZ p * P * ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖) := by
                ring
            _ ≤ _ := by gcongr
      _ ≤ r * Real.exp (-3) * (|Y t| * Real.exp (π * t / 2)) := by gcongr
      _ = |Y t| * ((Real.exp (π * t / 2) * Real.exp (-3)) * r) := by ring
      _ ≤ |Y t| * (Real.exp (α * t) * tri (2 * r) (t - t₀)) := by gcongr
  have hlow1 : (∫ t in a'..b', r * Real.exp (-3) * cZ p * P *
      ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖) ≤ ∫ t, |Y t| * w t := by
    calc (∫ t in a'..b', r * Real.exp (-3) * cZ p * P *
          ‖fL f ((((p : ℝ) + 1 : ℝ) : ℂ) + t * I)‖)
        ≤ ∫ t in a'..b', |Y t| * w t :=
          intervalIntegral.integral_mono_on hab'
            ((hcontL.const_mul _).intervalIntegrable _ _) (hcontW.intervalIntegrable _ _)
            fun t ht => hpt t (by rw [uIcc_of_le hab']; exact ht)
      _ = ∫ t in Ioc a' b', |Y t| * w t := intervalIntegral.integral_of_le hab'
      _ ≤ ∫ t, |Y t| * w t := setIntegral_le_integral hintW
          (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hw0 t))
  rw [intervalIntegral.integral_const_mul] at hlow1
  exact hlow1

end RamanujanTau.HafnerGeneral
