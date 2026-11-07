/-
# Windowed moments of `Z(t) = Λ(Δ, 6+it)`: mean square over centres, and the sign lower bound

`Iw α R t₀ = ∫ Z(t) e^{αt} tri_R(t − t₀) dt`.

* `mean_sq_Iw`: `∫_T^{2T} Iw(t₀)² dt₀ ≤ 4 S² R³` with `S = 2πM/cos⁶α`
  (Fourier identity `HardyCount.integral_Zc_exp_tri` + the Schur bound `Mean.lean`).
  This is the averaged replacement for the per-window sup bound `|Iw| ≤ S R²`: it is smaller
  by a factor `R` on average.
* `Iw_lower`: if `Z` has no zero on `[t₀−2r, t₀+2r]` then
  `r e^{−3} c_Z (T/2)^{11/2} ∫_{t₀−r}^{t₀+r} |L(Δ,6+it)| dt ≤ |Iw(π/2 − 1/T, 2r, t₀)|`.
-/
import RamanujanTau.HardyCount.Gaps
import RamanujanTau.HardyCountLinear.Mean

set_option autoImplicit false

namespace RamanujanTau.HardyCountLinear

open Complex MeasureTheory Set Filter Function
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
open scoped Real

/-- The windowed moment. -/
noncomputable def Iw (α R t₀ : ℝ) : ℝ := ∫ t, Zr t * Real.exp (α * t) * tri R (t - t₀)

/-- Its Fourier-side density. -/
noncomputable def gw (α R ξ : ℝ) : ℂ := (triHat R ξ : ℂ) * Phi (((-2 * π * ξ : ℝ) : ℂ) + α * I)

lemma mem_strip_line {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) (ξ : ℝ) :
    (((-2 * π * ξ : ℝ) : ℂ) + α * I) ∈ strip := by
  show |(((-2 * π * ξ : ℝ) : ℂ) + α * I).im| < π / 2
  simp [abs_of_nonneg ha0, ha]

lemma continuous_gw {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) :
    Continuous (gw α R) := by
  unfold gw
  refine (Complex.continuous_ofReal.comp (continuous_triHat hR)).mul ?_
  exact differentiableOn_Phi.continuousOn.comp_continuous (by fun_prop)
    (mem_strip_line ha0 ha)

lemma norm_gw_le {M : ℝ} (hM : ∀ p : UpperHalfPlane, ‖Δf p‖ * p.im ^ 6 ≤ M)
    {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) (ξ : ℝ) :
    ‖gw α R ξ‖ ≤ 2 * π * M / Real.cos α ^ 6 * triHat R ξ := by
  have hw := mem_strip_line ha0 ha ξ
  rw [gw, Phi_eq_strip hw, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (triHat_nonneg hR)]
  have h2 : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  have h3 := norm_Gc_le hM hw
  have e3 : (((-2 * π * ξ : ℝ) : ℂ) + α * I).im = α := by simp
  rw [e3] at h3
  have := triHat_nonneg (h := R) (ξ := ξ) hR
  calc triHat R ξ * (2 * π * ‖Gc (((-2 * π * ξ : ℝ) : ℂ) + α * I)‖)
      ≤ triHat R ξ * (2 * π * (M / Real.cos α ^ 6)) := by gcongr
    _ = _ := by ring

lemma Iw_eq_fI {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) (t₀ : ℝ) :
    (Iw α R t₀ : ℂ) = fI (gw α R) t₀ := by
  have hcast : ((Iw α R t₀ : ℝ) : ℂ) =
      ∫ t : ℝ, Zc t * cexp (α * t) * (tri R (t - t₀) : ℂ) := by
    rw [Iw]
    refine (integral_ofReal).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Zc_eq_Zr]
    norm_cast
  rw [hcast, integral_Zc_exp_tri ha0 ha hR t₀, fI]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [gw, ph]
  ring

lemma Iw_eq_re {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {R : ℝ} (hR : 0 ≤ R) (t₀ : ℝ) :
    Iw α R t₀ = (fI (gw α R) t₀).re := by
  rw [← Iw_eq_fI ha0 ha hR, Complex.ofReal_re]

/-- **Mean square of the windowed moments over centres.** -/
theorem mean_sq_Iw : ∃ M : ℝ, 0 ≤ M ∧ ∀ α : ℝ, 0 ≤ α → α < π / 2 → ∀ R : ℝ, 0 ≤ R →
    Continuous (Iw α R) ∧ ∀ T : ℝ, 0 < T →
      ∫ t₀ in Icc T (2 * T), Iw α R t₀ ^ 2 ≤
        4 * (2 * π * M / Real.cos α ^ 6) ^ 2 * R ^ 3 := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound
  refine ⟨M, hM0, fun α ha0 ha R hR => ?_⟩
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha⟩
  set S : ℝ := 2 * π * M / Real.cos α ^ 6 with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hgc := continuous_gw ha0 ha hR
  have hgb := norm_gw_le hM ha0 ha hR
  have hIc : Continuous (Iw α R) := by
    have : Iw α R = fun t₀ => (fI (gw α R) t₀).re := funext (Iw_eq_re ha0 ha hR)
    rw [this]
    exact Complex.continuous_re.comp (continuous_fI hgc hR hgb)
  refine ⟨hIc, fun T hT => ?_⟩
  have hBd : ∀ t₀, |Iw α R t₀| ≤ ∫ ξ, ‖gw α R ξ‖ := by
    intro t₀
    rw [Iw_eq_re ha0 ha hR]
    exact (Complex.abs_re_le_norm _).trans (norm_fI_le t₀)
  have hmain := integral_tri_norm_fI_sq_le hgc hS0 hR hgb (le_of_lt hT) (3 * T / 2)
  have hsq : ∀ t₀, ‖fI (gw α R) t₀‖ ^ 2 = Iw α R t₀ ^ 2 := by
    intro t₀
    rw [← Iw_eq_fI ha0 ha hR, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hsq] at hmain
  -- integrability of the weighted square
  have hWI : Integrable fun t₀ => tri T (t₀ - 3 * T / 2) * Iw α R t₀ ^ 2 := by
    have h1 : Integrable fun t₀ => tri T (t₀ - 3 * T / 2) :=
      (integrable_tri T).comp_sub_right _
    have h2 := h1.bdd_mul (f := fun t₀ => Iw α R t₀ ^ 2) (c := (∫ ξ, ‖gw α R ξ‖) ^ 2)
      (hIc.pow 2).aestronglyMeasurable (Eventually.of_forall fun t₀ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hBd t₀) 2)
    refine h2.congr (Eventually.of_forall fun t₀ => ?_)
    simp only; ring
  have hpt : ∀ t₀ ∈ Icc T (2 * T), Iw α R t₀ ^ 2 ≤
      2 / T * (tri T (t₀ - 3 * T / 2) * Iw α R t₀ ^ 2) := by
    intro t₀ ht₀
    have habs : |t₀ - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    have htri : T / 2 ≤ tri T (t₀ - 3 * T / 2) := by
      rw [tri_of_abs_le (by linarith)]; linarith
    have hsq0 := sq_nonneg (Iw α R t₀)
    rw [← mul_assoc]
    have : 1 ≤ 2 / T * tri T (t₀ - 3 * T / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith
    nlinarith
  calc ∫ t₀ in Icc T (2 * T), Iw α R t₀ ^ 2
      ≤ ∫ t₀ in Icc T (2 * T), 2 / T * (tri T (t₀ - 3 * T / 2) * Iw α R t₀ ^ 2) :=
        setIntegral_mono_on ((hIc.pow 2).integrableOn_Icc) (hWI.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ t₀, 2 / T * (tri T (t₀ - 3 * T / 2) * Iw α R t₀ ^ 2) :=
        setIntegral_le_integral (hWI.const_mul _) (Eventually.of_forall fun t₀ =>
          mul_nonneg (by positivity) (mul_nonneg (tri_nonneg _ _) (sq_nonneg _)))
    _ = 2 / T * ∫ t₀, tri T (t₀ - 3 * T / 2) * Iw α R t₀ ^ 2 := integral_const_mul _ _
    _ ≤ 2 / T * (2 * S ^ 2 * R ^ 3 * T) := by gcongr
    _ = 4 * S ^ 2 * R ^ 3 := by field_simp; ring

/-- **The sign lower bound** for a window free of zeros. -/
theorem Iw_lower {T t₀ r : ℝ} (hT : 1 ≤ T) (ht₀ : T ≤ t₀) (ht₀' : t₀ ≤ 2 * T) (hr : 0 < r)
    (hrT : r ≤ T / 2) (hno : ∀ t ∈ Icc (t₀ - 2 * r) (t₀ + 2 * r), Zr t ≠ 0) :
    r * Real.exp (-3) * cZ * (T / 2) ^ (11 / 2 : ℝ) *
        ∫ t in (t₀ - r)..(t₀ + r), ‖tauL (6 + t * I)‖ ≤
      |Iw (π / 2 - 1 / T) (2 * r) t₀| := by
  have hTpos : 0 < T := by linarith
  set α : ℝ := π / 2 - 1 / T with hα
  have hinv : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT
  have hinvpos : 0 < 1 / T := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three]
  have hαπ : α < π / 2 := by rw [hα]; linarith
  have hsign := const_sign continuous_Zr hno
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
  have hI : (∫ t, Zr t * w t) = Iw α (2 * r) t₀ := by
    simp only [hw, Iw, mul_assoc]
  rw [hI] at hEq
  rw [hEq]
  set a' : ℝ := t₀ - r with ha'
  set b' : ℝ := t₀ + r with hb'
  have hab' : a' ≤ b' := by rw [ha', hb']; linarith
  set P : ℝ := (T / 2) ^ (11 / 2 : ℝ) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hcontL : Continuous fun t : ℝ => ‖tauL (6 + t * I)‖ :=
    (tauLSeries_entire.continuous.comp (by fun_prop)).norm
  have hcontW : Continuous fun t => |Zr t| * w t := by
    simp only [hw]
    exact continuous_Zr.abs.mul ((by fun_prop : Continuous fun t => Real.exp (α * t)).mul
      ((continuous_tri (2 * r)).comp (by fun_prop)))
  have hintW : Integrable fun t => |Zr t| * w t := by
    refine ((Zr_integrable hα0 hαπ).norm.mul_const (2 * r)).mono' hcontW.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [hw, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (tri_nonneg _ _)]
    rw [mul_assoc]
    gcongr
    exact tri_le _ _ (by linarith)
  have hpt : ∀ t ∈ uIcc a' b', r * Real.exp (-3) * cZ * P * ‖tauL (6 + t * I)‖ ≤
      |Zr t| * w t := by
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
    have hPt : P ≤ t ^ (11 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) ht0 (by norm_num)
    have hlow := Zr_lower htpos
    have hL0 := norm_nonneg (tauL (6 + t * I))
    have hcz := cZ_pos
    have hZ0 := abs_nonneg (Zr t)
    calc r * Real.exp (-3) * cZ * P * ‖tauL (6 + t * I)‖
        ≤ r * Real.exp (-3) * (cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖) := by
          have : cZ * P * ‖tauL (6 + t * I)‖ ≤ cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖ := by
            gcongr
          calc r * Real.exp (-3) * cZ * P * ‖tauL (6 + t * I)‖
              = r * Real.exp (-3) * (cZ * P * ‖tauL (6 + t * I)‖) := by ring
            _ ≤ _ := by gcongr
      _ ≤ r * Real.exp (-3) * (|Zr t| * Real.exp (π * t / 2)) := by gcongr
      _ = |Zr t| * ((Real.exp (π * t / 2) * Real.exp (-3)) * r) := by ring
      _ ≤ |Zr t| * (Real.exp (α * t) * tri (2 * r) (t - t₀)) := by gcongr
  have hlow1 : (∫ t in a'..b', r * Real.exp (-3) * cZ * P * ‖tauL (6 + t * I)‖) ≤
      ∫ t, |Zr t| * w t := by
    calc (∫ t in a'..b', r * Real.exp (-3) * cZ * P * ‖tauL (6 + t * I)‖)
        ≤ ∫ t in a'..b', |Zr t| * w t :=
          intervalIntegral.integral_mono_on hab'
            ((hcontL.const_mul _).intervalIntegrable _ _) (hcontW.intervalIntegrable _ _)
            fun t ht => hpt t (by rw [uIcc_of_le hab']; exact ht)
      _ = ∫ t in Ioc a' b', |Zr t| * w t := intervalIntegral.integral_of_le hab'
      _ ≤ ∫ t, |Zr t| * w t := setIntegral_le_integral hintW
          (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hw0 t))
  rw [intervalIntegral.integral_const_mul] at hlow1
  exact hlow1

end RamanujanTau.HardyCountLinear
