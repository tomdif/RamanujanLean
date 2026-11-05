/-
# Triangle-windowed exponential moments of `Z(t) = Λ(6+it)`

For `0 ≤ α < π/2`, `h ≥ 0` and every centre `t₀`,

    |∫ Z(t) e^{αt} tri_h(t − t₀) dt| ≤ 2π M h / cos⁶ α,

where `M = sup_τ (Im τ)⁶ |Δ(τ)|` (`CuspFormClass.exists_bound`).

Proof: Fourier inversion `tri_h(v) = ∫ 𝓕tri_h(ξ) e^{2πiξv} dξ` (`tri_inversion`), Fubini, and
`∫ Z(t) e^{αt} e^{2πiξt} dt = Φ(−2πξ + iα) = 2π e^{6w} Δ(i e^{w})` (`Phi_eq_strip`).  For
`w = u + iα`, `|e^{6w} Δ(ie^w)| = (Im z)⁶|Δ(z)| / cos⁶α ≤ M / cos⁶α` with `z = i e^w`.  Finally
`𝓕tri_h ≥ 0` and `∫ 𝓕tri_h = tri_h(0) = h`.
-/
import RamanujanTau.HardyCount.Triangle
import RamanujanTau.HardyZeros.Main

set_option autoImplicit false

namespace RamanujanTau.HardyCount

open Complex MeasureTheory Set Filter Function
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros
open scoped Real MatrixGroups

/-- `sup (Im τ)⁶ ‖Δ(τ)‖ < ∞`. -/
lemma exists_Delta_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℍ, ‖Δf p‖ * p.im ^ 6 ≤ M := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  have h := hC p
  have e : ((12 : ℤ) / 2 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast] at h
  have hpos : 0 < p.im ^ 6 := pow_pos p.im_pos 6
  rw [le_div_iff₀ hpos] at h
  exact h.trans (le_max_left _ _)

/-- `‖G(w)‖ ≤ M / cos⁶(Im w)` on the strip. -/
lemma norm_Gc_le {M : ℝ} (hM : ∀ p : ℍ, ‖Δf p‖ * p.im ^ 6 ≤ M) {w : ℂ} (hw : w ∈ strip) :
    ‖Gc w‖ ≤ M / Real.cos w.im ^ 6 := by
  have hb : |w.im| < π / 2 := hw
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩
  have hz := im_exp_mul_I_pos hw
  have e : (cexp w * I).im = Real.exp w.re * Real.cos w.im := by
    simp [Complex.exp_re]
  have h := hM ⟨cexp w * I, hz⟩
  have hD : Dc (cexp w * I) = Δf ⟨cexp w * I, hz⟩ := Dc_of_im_pos hz
  rw [Gc, norm_mul, Complex.norm_exp, hD]
  have him : (⟨cexp w * I, hz⟩ : ℍ).im = Real.exp w.re * Real.cos w.im := e
  rw [him, mul_pow] at h
  have hre : (6 * w).re = 6 * w.re := by simp
  rw [hre, le_div_iff₀ (pow_pos hc 6)]
  have hE : Real.exp (6 * w.re) = Real.exp w.re ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hE]
  calc Real.exp w.re ^ 6 * ‖Δf ⟨cexp w * I, hz⟩‖ * Real.cos w.im ^ 6
      = ‖Δf ⟨cexp w * I, hz⟩‖ * (Real.exp w.re ^ 6 * Real.cos w.im ^ 6) := by ring
    _ ≤ M := h

lemma integrable_norm_Zc_exp {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) :
    Integrable fun t : ℝ => ‖Zc t‖ * Real.exp (α * t) := by
  have := (Zr_integrable ha0 ha).norm
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), norm_Zc_eq]

/-- **Fourier side of the windowed moment.** -/
theorem integral_Zc_exp_tri {α : ℝ} (ha0 : 0 ≤ α) (ha : α < π / 2) {h : ℝ} (hh : 0 ≤ h)
    (t₀ : ℝ) :
    ∫ t : ℝ, Zc t * cexp (α * t) * (tri h (t - t₀) : ℂ) =
      ∫ ξ : ℝ, (triHat h ξ : ℂ) * cexp (-(↑(2 * π * ξ * t₀) * I)) *
        Phi (((-2 * π * ξ : ℝ) : ℂ) + α * I) := by
  set F : ℝ → ℝ → ℂ := fun t ξ =>
    Zc t * cexp (α * t) * (cexp (↑(2 * π * ξ * (t - t₀)) * I) * (triHat h ξ : ℂ)) with hF
  have hcont : Continuous (uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => Zc p.1 := continuous_Zc.comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => (triHat h p.2 : ℂ) := by
      have : Continuous fun ξ => triHat h ξ := by
        have e : (fun ξ => triHat h ξ) = fun ξ => (FourierTransform.fourier (triC h) ξ).re := by
          funext ξ; rw [fourier_triC hh]; simp
        rw [e]
        exact Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ (integrable_triC h))
      exact Complex.continuous_ofReal.comp (this.comp continuous_snd)
    have h3 : Continuous fun p : ℝ × ℝ => cexp (α * p.1) := by fun_prop
    have h4 : Continuous fun p : ℝ × ℝ => cexp (↑(2 * π * p.2 * (p.1 - t₀)) * I) := by fun_prop
    exact (h1.mul h3).mul (h4.mul h2)
  have hint : Integrable (uncurry F) (volume.prod volume) := by
    refine ((integrable_norm_Zc_exp ha0 ha).mul_prod (integrable_triHat hh)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hF, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (triHat_nonneg hh)]
    simp
  have hL : ∀ t : ℝ, Zc t * cexp (α * t) * (tri h (t - t₀) : ℂ) = ∫ ξ, F t ξ := by
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
  calc Zc t * cexp (↑α * ↑t) * (cexp (↑(2 * π * ξ * (t - t₀)) * I) * ↑(triHat h ξ))
      = ↑(triHat h ξ) * Zc t * (cexp (↑α * ↑t) * cexp (↑(2 * π * ξ * (t - t₀)) * I)) := by ring
    _ = _ := by rw [e]; ring

/-- **The window bound.** -/
theorem abs_integral_Zr_exp_tri_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α : ℝ, 0 ≤ α → α < π / 2 → ∀ h : ℝ, 0 ≤ h → ∀ t₀ : ℝ,
      |∫ t : ℝ, Zr t * Real.exp (α * t) * tri h (t - t₀)| ≤
        2 * π * M * h / Real.cos α ^ 6 := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound
  refine ⟨M, hM0, fun α ha0 ha h hh t₀ => ?_⟩
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha⟩
  have hcast : ((∫ t : ℝ, Zr t * Real.exp (α * t) * tri h (t - t₀) : ℝ) : ℂ) =
      ∫ t : ℝ, Zc t * cexp (α * t) * (tri h (t - t₀) : ℂ) := by
    have e : (∫ t : ℝ, ((Zr t * Real.exp (α * t) * tri h (t - t₀) : ℝ) : ℂ)) =
        ((∫ t : ℝ, Zr t * Real.exp (α * t) * tri h (t - t₀) : ℝ) : ℂ) := integral_ofReal
    rw [← e]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Zc_eq_Zr, Complex.ofReal_mul, Complex.ofReal_exp]
  have habs : |∫ t : ℝ, Zr t * Real.exp (α * t) * tri h (t - t₀)| =
      ‖∫ t : ℝ, Zc t * cexp (α * t) * (tri h (t - t₀) : ℂ)‖ := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, integral_Zc_exp_tri ha0 ha hh t₀]
  have hbound : ∀ ξ : ℝ, ‖(triHat h ξ : ℂ) * cexp (-(↑(2 * π * ξ * t₀) * I)) *
      Phi (((-2 * π * ξ : ℝ) : ℂ) + α * I)‖ ≤ triHat h ξ * (2 * π * (M / Real.cos α ^ 6)) := by
    intro ξ
    have hw : (((-2 * π * ξ : ℝ) : ℂ) + α * I) ∈ strip := by
      show |(((-2 * π * ξ : ℝ) : ℂ) + α * I).im| < π / 2
      simp [abs_of_nonneg ha0, ha]
    rw [Phi_eq_strip hw, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (triHat_nonneg hh), Complex.norm_exp]
    have e1 : (-(↑(2 * π * ξ * t₀) * I) : ℂ).re = 0 := by simp
    rw [e1, Real.exp_zero, mul_one, norm_mul]
    have h2 : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2]
    have h3 := norm_Gc_le hM hw
    have e3 : (((-2 * π * ξ : ℝ) : ℂ) + α * I).im = α := by simp
    rw [e3] at h3
    have := triHat_nonneg (h := h) (ξ := ξ) hh
    gcongr
  calc ‖∫ ξ : ℝ, (triHat h ξ : ℂ) * cexp (-(↑(2 * π * ξ * t₀) * I)) *
        Phi (((-2 * π * ξ : ℝ) : ℂ) + α * I)‖
      ≤ ∫ ξ : ℝ, triHat h ξ * (2 * π * (M / Real.cos α ^ 6)) :=
        norm_integral_le_of_norm_le ((integrable_triHat hh).mul_const _)
          (Eventually.of_forall hbound)
    _ = h * (2 * π * (M / Real.cos α ^ 6)) := by rw [integral_mul_const, integral_triHat hh]
    _ = 2 * π * M * h / Real.cos α ^ 6 := by ring

end RamanujanTau.HardyCount
