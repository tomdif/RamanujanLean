/-
# Pointwise bound for `G_h`, part 1: `‖G_h(W₀)‖ ≤ (2/(2Y)¹²) (‖Q‖/W + E)`
-/
import RamanujanTau.SCSProof.Main4

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma W0_eq : 2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)) =
    (4 * π * P.Y : ℝ) + (2 * π * P.Y * P.θ : ℝ) * I := by
  rw [coe_zeta0]
  simp only [map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

lemma norm_u0_ge : 2 * P.Y ≤ ‖(P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg P.hY.le]
  have : 2 ≤ ‖I - conj ((zeta0 P : ℍ) : ℂ)‖ := by
    rw [coe_zeta0]
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp; norm_num
  have := P.hY
  nlinarith

/-- **Division by the prefactor.** -/
theorem norm_G0_le (hh : P.h * (4 * π * P.Y) ≤ 1) :
    ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 / (2 * P.Y) ^ 12 * ‖cf P P.Y (zeta0 P)‖ := by
  have hY := P.hY
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cf P P.Y (zeta0 P) = u0 ^ 12 * (e0 : ℂ) *
      Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))) := rfl
  have he0 : 1 / 2 ≤ e0 := by
    have h1 : -(1 / 2 : ℝ) ≤ -2 * π * P.h * P.Y := by nlinarith
    have h2 : Real.exp (-(1 / 2 : ℝ)) ≤ e0 := Real.exp_le_exp.2 h1
    have h3 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      have := Real.add_one_le_exp (-(1 / 2 : ℝ)); linarith
    linarith
  have hu := norm_u0_ge P
  have hpos : 0 < (2 * P.Y) ^ 12 := by positivity
  rw [hcf, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set G := ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖
  have hG : 0 ≤ G := norm_nonneg _
  have hp : (2 * P.Y) ^ 12 * (1 / 2) ≤ ‖u0‖ ^ 12 * e0 := by
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

end RamanujanTau.SCSProof
