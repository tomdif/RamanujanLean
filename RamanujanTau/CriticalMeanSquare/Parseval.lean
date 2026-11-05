/-
# Exact Parseval identity for the weighted critical-line mean square

**Theorem** (`weighted_parseval`). For `0 ≤ β < π/2`,

    ∫_ℝ |Λ(Δ, 6+it)|² e^{2βt} dt = 2π ∫_ℝ |e^{6w} Δ(i e^{w})|² du,   w = u + iβ.

So the weighted mean square of `Λ` on the critical line is exactly an `L²` norm of `Δ` along
the ray `arg τ = π/2 + β` (which approaches the real axis as `β → π/2`).

Proof: Plancherel for an integrable continuous `F` with integrable `𝓕F` (`parseval`, from
Mathlib's `integral_sesq_fourierIntegral_eq_neg_flip` plus Fourier inversion), applied to
`F(t) = Λ(6+it)e^{βt}`, whose Fourier transform is `Φ_6(2πξ + iβ) = 2π e^{6w}Δ(ie^w)`.
Integrability of the Fourier side comes from the majorant of `Upper`.
-/
import RamanujanTau.CriticalMeanSquare.Upper

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquare

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCount
  RamanujanTau.HardyCountLinear RamanujanTau.HardyCountHafner
open scoped Real FourierTransform

/-- **Plancherel** for continuous integrable `F : ℝ → ℂ` with integrable Fourier transform. -/
theorem parseval {F : ℝ → ℂ} (hc : Continuous F) (hi : Integrable F) (hFi : Integrable (𝓕 F)) :
    ∫ ξ, ‖𝓕 F ξ‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ (E := ℂ))
    Real.continuous_fourierChar (L := innerₗ ℝ) (μ := volume) (ν := volume)
    continuous_inner hi hFi
  have hflip : (-(innerₗ ℝ).flip : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) = -innerₗ ℝ := by
    congr 1
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp
  have hinv : VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ ℝ).flip) (𝓕 F) = F := by
    rw [hflip]
    exact hc.fourierInv_fourier_eq hi hFi
  rw [hinv] at h
  have h' : ((∫ ξ, ‖𝓕 F ξ‖ ^ 2 : ℝ) : ℂ) = ((∫ t, ‖F t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    have e1 : ∀ z : ℂ, (innerSL ℂ z) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [innerSL_apply_apply, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have e2 : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) F ξ = 𝓕 F ξ :=
      fun ξ => rfl
    simp only [e2, e1] at h
    exact h
  exact_mod_cast h'

/-- The Fourier-side density at `σ = 6` is integrable for `0 ≤ β < π/2`. -/
lemma integrable_gS_six {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (gS 6 β) := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  set c : ℝ := Real.cos β with hcdef
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have hstrip : ∀ ξ : ℝ, (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    intro ξ; show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hgc : Continuous (gS 6 β) := by
    unfold gS
    exact (differentiableOn_Phis (le_refl 6) (by norm_num)).continuousOn.comp_continuous
      (by fun_prop) hstrip
  refine ((integrable_maj c).const_mul (2 * π * (M / c ^ 6))).mono' hgc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  refine (norm_gS_six_le hM0 hM hβ0 hβ ξ).trans ?_
  rw [← hcdef]
  have : 0 ≤ 2 * π * (M / c ^ 6) := by positivity
  exact mul_le_mul_of_nonneg_left (min_le_maj hc0 ξ) this

/-- **Exact weighted Parseval identity on the critical line.** -/
theorem weighted_parseval {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) =
      2 * π * ∫ u : ℝ, ‖cexp (6 * ((u : ℂ) + β * I)) * Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2 := by
  have hgi := integrable_gS_six hβ0 hβ
  have hFi : Integrable (𝓕 (Fs 6 β)) := by
    have : 𝓕 (Fs 6 β) = fun ξ => gS 6 β (-ξ) := by
      funext ξ; rw [fourier_Fs, gS]; congr 3; ring
    rw [this]; exact hgi.comp_neg
  have hP := parseval (continuous_Fs 6 β) (integrable_Fs (le_refl 6) (by norm_num) hβ0 hβ) hFi
  -- left side
  have hL : ∀ t : ℝ, ‖Fs 6 β t‖ ^ 2 = ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) := by
    intro t
    have e : (((β : ℂ) * (t : ℂ))).re = β * t := by simp
    rw [Fs, Zs, norm_mul, Complex.norm_exp, mul_pow, e, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  simp only [hL] at hP
  rw [← hP]
  -- right side: `𝓕F(ξ) = Φ_6(2πξ + iβ) = 2π G_6(2πξ + iβ)`
  have hstrip : ∀ u : ℝ, ((u : ℂ) + β * I) ∈ strip := by
    have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
    intro u; show |((u : ℂ) + β * I).im| < π / 2; simpa using hβabs
  set H : ℝ → ℝ := fun u => ‖cexp (6 * ((u : ℂ) + β * I)) * Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2
    with hH
  have hR : ∀ ξ : ℝ, ‖𝓕 (Fs 6 β) ξ‖ ^ 2 = 4 * π ^ 2 * H (2 * π * ξ) := by
    intro ξ
    rw [fourier_Fs, Phis_eq_strip (le_refl 6) (by norm_num) (hstrip _), Gs, norm_mul, mul_pow, hH]
    congr 1
    · rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      ring
  simp only [hR]
  rw [integral_const_mul, Measure.integral_comp_mul_left H (2 * π), smul_eq_mul]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  field_simp
  ring

end RamanujanTau.CriticalMeanSquare
