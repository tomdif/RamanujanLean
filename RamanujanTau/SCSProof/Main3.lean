/-
# Lipschitz bound for the horocycle coefficient `cf` on the box
-/
import RamanujanTau.SCSProof.Main2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

/-- `ζ₀ = θ + i`. -/
def zeta0 : ℍ := ⟨(P.θ : ℂ) + I, by simp⟩

lemma coe_zeta0 : ((zeta0 P : ℍ) : ℂ) = (P.θ : ℂ) + I := rfl

/-- `A = |θ| + 3`. -/
noncomputable def Aθ : ℝ := |P.θ| + 3

lemma Aθ_ge : 3 ≤ Aθ P := by unfold Aθ; linarith [abs_nonneg P.θ]

lemma norm_le_re_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z

lemma inB_bounds {ζ : ℍ} (hζ : inB P (ζ : ℂ)) :
    |(ζ : ℂ).re| ≤ |P.θ| + 1 / 2 ∧ 1 / 2 ≤ (ζ : ℂ).im ∧ (ζ : ℂ).im ≤ 3 / 2 := by
  obtain ⟨h1, h2⟩ := hζ
  have hε1 := P.hε1
  rw [abs_le] at h2
  refine ⟨?_, by linarith, by linarith⟩
  have := abs_sub_abs_le_abs_sub (ζ : ℂ).re P.θ
  linarith

lemma norm_I_sub_conj {ζ : ℍ} (hζ : inB P (ζ : ℂ)) : ‖I - conj (ζ : ℂ)‖ ≤ Aθ P := by
  obtain ⟨h1, h2, h3⟩ := inB_bounds P hζ
  refine (norm_le_re_im _).trans ?_
  simp only [Complex.sub_re, Complex.I_re, Complex.conj_re, zero_sub, abs_neg, Complex.sub_im,
    Complex.I_im, Complex.conj_im, sub_neg_eq_add]
  unfold Aθ
  rw [abs_of_pos (show (0 : ℝ) < 1 + (ζ : ℂ).im by linarith)]
  linarith

lemma norm_one_add_I_conj {ζ : ℍ} (hζ : inB P (ζ : ℂ)) : ‖1 + I * conj (ζ : ℂ)‖ ≤ Aθ P := by
  obtain ⟨h1, h2, h3⟩ := inB_bounds P hζ
  refine (norm_le_re_im _).trans ?_
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.conj_re,
    zero_mul, Complex.I_im, Complex.conj_im, one_mul, sub_neg_eq_add, zero_add, Complex.add_im,
    Complex.one_im, Complex.mul_im, mul_neg]
  unfold Aθ
  rw [abs_of_pos (by linarith)]
  simp only [neg_zero, zero_add] at *
  linarith

lemma inB_zeta0 : inB P ((zeta0 P : ℍ) : ℂ) := by
  rw [coe_zeta0]; constructor <;> simp [P.hε.le]

lemma norm_sub_zeta0 {ζ : ℍ} (hζ : inB P (ζ : ℂ)) : ‖(ζ : ℂ) - (zeta0 P : ℂ)‖ ≤ 2 * P.ε := by
  obtain ⟨h1, h2⟩ := hζ
  refine (norm_le_re_im _).trans ?_
  rw [coe_zeta0]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
    Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  linarith

lemma real_exp_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (by have := Real.exp_le_exp.2 (neg_le_neg hab); linarith),
      abs_of_nonpos (by linarith)]
    have h1 : 1 - Real.exp (-(b - a)) ≤ b - a := by
      have := Real.add_one_le_exp (-(b - a)); linarith
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [h2]
    have h4 : 0 ≤ 1 - Real.exp (-(b - a)) := by
      have := Real.exp_le_one_iff.2 (show -(b - a) ≤ 0 by linarith); linarith
    nlinarith [Real.exp_pos (-a)]
  · rw [abs_of_nonpos (by have := Real.exp_le_exp.2 (neg_le_neg hab); linarith),
      abs_of_nonneg (by linarith)]
    have h1 : 1 - Real.exp (-(a - b)) ≤ a - b := by
      have := Real.add_one_le_exp (-(a - b)); linarith
    have h2 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [h2]
    have h4 : 0 ≤ 1 - Real.exp (-(a - b)) := by
      have := Real.exp_le_one_iff.2 (show -(a - b) ≤ 0 by linarith); linarith
    nlinarith [Real.exp_pos (-b)]

lemma pow12_sub_le (u v : ℂ) {m : ℝ} (hu : ‖u‖ ≤ m) (hv : ‖v‖ ≤ m) :
    ‖u ^ 12 - v ^ 12‖ ≤ 12 * m ^ 11 * ‖u - v‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  have hm : 0 ≤ m := (norm_nonneg _).trans hu
  calc ∑ i ∈ Finset.range 12, ‖u ^ i * v ^ (12 - 1 - i)‖ ≤ ∑ i ∈ Finset.range 12, m ^ 11 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < 12 := Finset.mem_range.1 hi
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖u‖ ^ i * ‖v‖ ^ (12 - 1 - i) ≤ m ^ i * m ^ (12 - 1 - i) := by gcongr
          _ = m ^ 11 := by rw [← pow_add]; congr 1; omega
    _ = 12 * m ^ 11 := by simp

end RamanujanTau.SCSProof
