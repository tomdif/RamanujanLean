/-
# The transformation of `η` under all of `SL₂(ℤ)`

`η(γτ) = ε_γ · √(cτ + d) · η(τ)` on the upper half-plane, with `ε_γ²⁴ = 1` (for `c > 0`).

Logarithmic derivatives: `(log η)' = (πi/12)E₂`, and `E₂(γτ)(cτ+d)⁻² = E₂(τ) − (1/2ζ(2))·2πic/(cτ+d)`
(Mathlib's `E2_slash_action`). So both sides have log-derivative `(πi/12)E₂ + c/(2(cτ+d))`, and they agree up to
a constant. Comparing 24th powers with the modularity of `Δ = η²⁴` gives `ε²⁴ = 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Rademacher
open Complex ModularForm EisensteinSeries MatrixGroups Filter
open scoped Real
open UpperHalfPlane hiding I

noncomputable section

variable (γ : SL(2, ℤ))

/-- the Möbius map on `ℂ`. -/
def mob (z : ℂ) : ℂ := ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

lemma denom_ne_zero' {z : ℂ} (hz : 0 < z.im) : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero γ ⟨z, hz⟩
  simpa [UpperHalfPlane.denom] using this

lemma mob_eq (z : ℍ) : mob γ z = ((γ • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; rfl

lemma mob_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (mob γ z).im := by
  show 0 < (mob γ ((⟨z, hz⟩ : ℍ) : ℂ)).im
  rw [mob_eq]; exact (γ • (⟨z, hz⟩ : ℍ)).im_pos

lemma denom_mem_slit (hc : 0 < γ 1 0) {z : ℂ} (hz : 0 < z.im) : (γ 1 0 : ℂ) * z + γ 1 1 ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inr ?_)
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
  have : (0 : ℝ) < γ 1 0 := by exact_mod_cast hc
  positivity

lemma hasDerivAt_mob {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)⁻¹ z := by
  have hd := denom_ne_zero' γ hz
  have h := ((hasDerivAt_id z).const_mul (γ 0 0 : ℂ) |>.add_const (γ 0 1 : ℂ)).div
    ((hasDerivAt_id z).const_mul (γ 1 0 : ℂ) |>.add_const (γ 1 1 : ℂ)) hd
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  convert h using 1
  simp only [id, mul_one]
  rw [inv_eq_one_div]
  congr 1
  linear_combination -hdet

lemma differentiableOn_eta : DifferentiableOn ℂ η upperHalfPlaneSet := fun z hz =>
  (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt

/-- `E₂` under `γ`, evaluated. -/
lemma E2_mob (z : ℍ) : E2 (γ • z) * (denom γ z ^ 2)⁻¹ = E2 z - 6 / π ^ 2 * (π * I * γ 1 0 / denom γ z) := by
  have h := congrFun (E2_slash_action γ) z
  simp only [SL_slash_def, Pi.sub_apply, Pi.smul_apply, D2, smul_eq_mul, riemannZeta_two] at h
  have e : (denom γ z ^ 2)⁻¹ = denom γ z ^ (-2 : ℤ) := by rw [zpow_neg, zpow_ofNat]
  rw [e, h]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  field_simp

/-- the linear form `cz + d`. -/
def lin (z : ℂ) : ℂ := (γ 1 0 : ℂ) * z + γ 1 1

lemma differentiable_lin : Differentiable ℂ (lin γ) := by unfold lin; fun_prop

lemma sqrt_lin_ne {z : ℂ} (hz : 0 < z.im) : sqrt (lin γ z) ≠ 0 := by
  simp only [sqrt]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (denom_ne_zero' γ hz)

lemma differentiableAt_sqrt_lin (hc : 0 < γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun z => sqrt (lin γ z)) z := by
  have hm : lin γ z ∈ slitPlane := denom_mem_slit γ hc hz
  exact (differentiableAt_sqrt hm).comp (f := lin γ) z ((differentiable_lin γ) z)

lemma logDeriv_sqrt_lin (hc : 0 < γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    logDeriv (fun z => sqrt (lin γ z)) z = γ 1 0 / (2 * lin γ z) := by
  have hm := denom_mem_slit γ hc hz
  have hw : lin γ z ≠ 0 := denom_ne_zero' γ hz
  have hd : HasDerivAt (fun z => sqrt (lin γ z)) (lin γ z ^ (-1 / 2 : ℂ) / 2 * γ 1 0) z := by
    have h1 : HasDerivAt (lin γ) (γ 1 0 : ℂ) z := by
      have := ((hasDerivAt_id z).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
      simp only [id, mul_one] at this
      exact this
    exact (hasDerivAt_sqrt hm).comp z h1
  rw [logDeriv_apply, hd.deriv, sqrt]
  rw [show (-1 / 2 : ℂ) = -(2⁻¹) by norm_num, cpow_neg]
  have h2 : lin γ z ^ (2⁻¹ : ℂ) * lin γ z ^ (2⁻¹ : ℂ) = lin γ z := by
    rw [← cpow_add _ _ hw]; norm_num
  have h3 : lin γ z ^ (2⁻¹ : ℂ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h2; exact hw h2.symm
  generalize lin γ z ^ (2⁻¹ : ℂ) = s at h2 h3 ⊢
  rw [← h2]
  field_simp

/-- **the log-derivatives agree**. -/
lemma logDeriv_eq (hc : 0 < γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    logDeriv (η ∘ mob γ) z = logDeriv (fun z => sqrt (lin γ z) * η z) z := by
  have hmob := mob_im_pos γ hz
  rw [logDeriv_comp (differentiableAt_eta_of_mem_upperHalfPlaneSet hmob) (hasDerivAt_mob γ hz).differentiableAt,
    (hasDerivAt_mob γ hz).deriv]
  rw [logDeriv_mul (f := fun z => sqrt (lin γ z)) (g := η) z (sqrt_lin_ne γ hz)
    (eta_ne_zero hz) (differentiableAt_sqrt_lin γ hc hz)
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz), logDeriv_sqrt_lin γ hc hz]
  have e1 := logDeriv_eta_eq_E2 (⟨mob γ z, hmob⟩ : ℍ)
  have e2 := logDeriv_eta_eq_E2 (⟨z, hz⟩ : ℍ)
  rw [e1, e2]
  have hE := E2_mob γ ⟨z, hz⟩
  have hγ : (⟨mob γ z, hmob⟩ : ℍ) = γ • (⟨z, hz⟩ : ℍ) := by
    ext; rw [UpperHalfPlane.coe_mk, ← mob_eq]
  rw [← hγ] at hE
  have hden : denom γ (⟨z, hz⟩ : ℍ) = lin γ z := by simp [UpperHalfPlane.denom, lin]
  rw [hden] at hE
  have hw : lin γ z ≠ 0 := denom_ne_zero' γ hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)⁻¹ = (lin γ z ^ 2)⁻¹ from rfl]
  calc π * I / 12 * E2 ⟨mob γ z, hmob⟩ * (lin γ z ^ 2)⁻¹ =
      π * I / 12 * (E2 ⟨mob γ z, hmob⟩ * (lin γ z ^ 2)⁻¹) := by ring
    _ = _ := by
      rw [hE]
      field_simp
      ring_nf
      rw [I_sq]
      ring

/-- **`η(γτ) = ε √(cτ+d) η(τ)`** with a constant `ε ≠ 0`. -/
lemma eta_mob_const (hc : 0 < γ 1 0) :
    ∃ ε : ℂ, ε ≠ 0 ∧ Set.EqOn (η ∘ mob γ) (ε • fun z => sqrt (lin γ z) * η z) upperHalfPlaneSet := by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz => logDeriv_eq γ hc hz
  · intro z hz
    exact ((differentiableAt_eta_of_mem_upperHalfPlaneSet (mob_im_pos γ hz)).comp z
      (hasDerivAt_mob γ hz).differentiableAt).differentiableWithinAt
  · intro z hz
    exact ((differentiableAt_sqrt_lin γ hc hz).mul
      (differentiableAt_eta_of_mem_upperHalfPlaneSet hz)).differentiableWithinAt
  · exact isOpen_upperHalfPlaneSet
  · exact Convex.isPreconnected (convex_halfSpace_im_gt 0)
  · intro z hz
    exact mul_ne_zero (sqrt_lin_ne γ hz) (eta_ne_zero hz)
  · exact fun z hz => eta_ne_zero (mob_im_pos γ hz)

end

end Rademacher

namespace Rademacher
open Complex ModularForm MatrixGroups
open scoped Real
open UpperHalfPlane hiding I

noncomputable section

variable (γ : SL(2, ℤ))

lemma sqrt_pow_24 {w : ℂ} (hw : w ≠ 0) : sqrt w ^ 24 = w ^ 12 := by
  have h2 : sqrt w ^ 2 = w := by
    simp only [sqrt]; rw [sq, ← cpow_add _ _ hw]; norm_num
  rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, h2]

/-- **`ε²⁴ = 1`**. -/
lemma eta_mob_unit (hc : 0 < γ 1 0) :
    ∃ ε : ℂ, ε ^ 24 = 1 ∧ ∀ z : ℂ, 0 < z.im → η (mob γ z) = ε * sqrt (lin γ z) * η z := by
  obtain ⟨ε, hε0, hε⟩ := eta_mob_const γ hc
  refine ⟨ε, ?_, fun z hz => by simpa [mul_assoc] using hε hz⟩
  -- compare 24th powers at `z = i`
  have hI : (0 : ℝ) < (Complex.I).im := by simp
  have h := hε (show Complex.I ∈ upperHalfPlaneSet from hI)
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at h
  have hΔ := congrFun (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ)
    (⟨Complex.I, hI⟩ : ℍ)
  simp only [SL_slash_def, discriminant] at hΔ
  have hmob : ((γ • (⟨Complex.I, hI⟩ : ℍ) : ℍ) : ℂ) = mob γ Complex.I := (mob_eq γ ⟨Complex.I, hI⟩).symm
  have hden : denom γ (⟨Complex.I, hI⟩ : ℍ) = lin γ Complex.I := by simp [UpperHalfPlane.denom, lin]
  rw [hden] at hΔ
  have hw : lin γ Complex.I ≠ 0 := denom_ne_zero' γ hI
  have hη := eta_ne_zero hI
  have h24 : η (mob γ Complex.I) ^ 24 = lin γ Complex.I ^ 12 * η Complex.I ^ 24 := by
    have e : η ((γ • (⟨Complex.I, hI⟩ : ℍ) : ℍ) : ℂ) ^ 24 * lin γ Complex.I ^ (-12 : ℤ) = η Complex.I ^ 24 := hΔ
    rw [hmob, zpow_neg, zpow_ofNat, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hw)] at e
    linear_combination e
  rw [h, mul_pow, mul_pow, sqrt_pow_24 hw] at h24
  have hne : lin γ Complex.I ^ 12 * η Complex.I ^ 24 ≠ 0 := mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hη)
  have : ε ^ 24 * (lin γ Complex.I ^ 12 * η Complex.I ^ 24) = 1 * (lin γ Complex.I ^ 12 * η Complex.I ^ 24) := by
    linear_combination h24
  exact mul_right_cancel₀ hne this

end

end Rademacher
