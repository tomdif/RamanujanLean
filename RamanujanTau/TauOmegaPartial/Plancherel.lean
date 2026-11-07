/-
# Plancherel for `L¹ ∩ L²` functions on `ℝ`

Mathlib has the `L²` Fourier transform as a linear isometry (`Lp.fourierTransformₗᵢ`) and the
`L¹` Fourier integral `𝓕`; here we identify them on `L¹ ∩ L²` (via tempered distributions and the
du Bois-Reymond lemma) and deduce

    ∫ |𝓕 h|² = ∫ |h|²,     𝓕 h ∈ L²,

for every integrable, square-integrable `h : ℝ → ℂ` (no continuity needed).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open MeasureTheory Complex
open scoped FourierTransform ContDiff

lemma integral_norm_sq_Lp (v : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖(v : ℝ → ℂ) x‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) v v
  rw [inner_self_eq_norm_sq_to_K] at h
  have e : ∀ a : ℝ, (inner ℂ ((v : ℝ → ℂ) a) ((v : ℝ → ℂ) a)) = ((‖(v : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) :=
    fun a => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by rw [← h]; push_cast; rfl)

/-- **Plancherel on `L¹ ∩ L²`.** -/
theorem plancherel_of_integrable {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    MemLp (𝓕 h) 2 ∧ ∫ ξ, ‖𝓕 h ξ‖ ^ 2 = ∫ u, ‖h u‖ ^ 2 := by
  set u : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp h with hu
  set v : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 u with hv
  have hcont : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  have hae : (v : ℝ → ℂ) =ᵐ[volume] 𝓕 h := by
    apply ae_eq_of_integral_contDiff_smul_eq
    · exact (Lp.memLp v).locallyIntegrable (by norm_num)
    · exact hcont.locallyIntegrable
    · intro g hg hgc
      have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
      have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
      set φ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂ with hφdef
      have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
      have e1 : ∫ x, g x • (v : ℝ → ℂ) x = Lp.toTemperedDistribution v φ := by
        rw [Lp.toTemperedDistribution_apply]
        congr 1
      have e2 : Lp.toTemperedDistribution v φ = Lp.toTemperedDistribution u (𝓕 φ) := by
        rw [hv, ← Lp.fourier_toTemperedDistribution_eq]; rfl
      have e3 : Lp.toTemperedDistribution u (𝓕 φ) = ∫ x, 𝓕 (φ : ℝ → ℂ) x • h x := by
        rw [Lp.toTemperedDistribution_apply]
        apply integral_congr_ae
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hu, hx]; rfl
      have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
        refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
        simp
      have e4 : ∫ x, 𝓕 (φ : ℝ → ℂ) x • h x = ∫ ξ, φ ξ • 𝓕 h ξ := by
        have := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
          (μ := volume) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
          continuous_inner φ.integrable h1
        rw [hflip] at this
        exact this
      rw [e1, e2, e3, e4]
      congr 1
  have hmem : MemLp (𝓕 h) 2 := (Lp.memLp v).ae_eq hae
  refine ⟨hmem, ?_⟩
  have i1 : ∫ ξ, ‖𝓕 h ξ‖ ^ 2 = ∫ ξ, ‖(v : ℝ → ℂ) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have i2 : ∫ x, ‖h x‖ ^ 2 = ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hu, hx]
  rw [i1, i2, integral_norm_sq_Lp, integral_norm_sq_Lp, hv, Lp.norm_fourier_eq]

end RamanujanTau.TauOmegaPartial
