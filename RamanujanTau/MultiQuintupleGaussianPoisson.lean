/-
# Shifted and modulated Gaussian Poisson summation

The analytic kernel used to transform each finite congruence projection.
Summability is proved for every parameter with positive real quadratic part.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace Ramanujan.MultiQuintuple
open Real
open scoped BigOperators

noncomputable def shiftedGaussian (a s b : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-π*a*((n : ℂ)+s)^2+2*π*Complex.I*b*((n : ℂ)+s))

theorem summable_complex_gaussian_quadratic {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    Summable (fun n : ℤ => Complex.exp (-π*a*(n : ℂ)^2+2*π*b*(n : ℂ))) := by
  have hs := (summable_jacobiTheta₂_term_iff (-Complex.I*b) (Complex.I*a)).mpr
    (by simpa using ha)
  apply hs.congr
  intro n
  apply congrArg Complex.exp
  dsimp [jacobiTheta₂_term]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

theorem shiftedGaussian_factor (a s b : ℂ) (n : ℤ) :
    shiftedGaussian a s b n =
      Complex.exp (-π*a*s^2+2*π*Complex.I*b*s) *
        Complex.exp (-π*a*(n : ℂ)^2+2*π*(-a*s+Complex.I*b)*(n : ℂ)) := by
  rw [shiftedGaussian,← Complex.exp_add]
  congr 1
  ring

theorem summable_shiftedGaussian {a : ℂ} (ha : 0 < a.re) (s b : ℂ) :
    Summable (shiftedGaussian a s b) := by
  have hs := (summable_complex_gaussian_quadratic ha (-a*s+Complex.I*b)).mul_left
    (Complex.exp (-π*a*s^2+2*π*Complex.I*b*s))
  exact hs.congr (fun n => (shiftedGaussian_factor a s b n).symm)

/-- Poisson summation with both the shift and Fourier modulation retained.
This is the form needed by the residue-class projection of a Watson branch. -/
theorem tsum_shiftedGaussian_poisson {a : ℂ} (ha : 0 < a.re) (s b : ℂ) :
    (∑' n : ℤ, shiftedGaussian a s b n) =
      (1 / a^(1/2 : ℂ)) * ∑' m : ℤ,
        Complex.exp (-π/a*((m : ℂ)-b)^2+2*π*Complex.I*s*(m : ℂ)) := by
  have ha0 : a ≠ 0 := by intro hz; rw [hz] at ha; simpa using ha
  simp_rw [shiftedGaussian_factor]
  rw [tsum_mul_left,Complex.tsum_exp_neg_quadratic ha (-a*s+Complex.I*b)]
  rw [← mul_assoc,mul_comm (Complex.exp _) (1/a^(1/2 : ℂ)),mul_assoc,← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem tsum_three_separated_complex {f g h : ℤ → ℂ}
    (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    (∑' x : (ℤ × ℤ) × ℤ, f x.1.1*g x.1.2*h x.2) =
      (∑' a, f a)*(∑' b, g b)*(∑' c, h c) := by
  have hfg := summable_mul_of_summable_norm hf.norm hg.norm
  calc
    (∑' x : (ℤ × ℤ) × ℤ, f x.1.1*g x.1.2*h x.2) =
        (∑' ab : ℤ × ℤ, f ab.1*g ab.2)*(∑' c, h c) :=
      (tsum_mul_tsum_of_summable_norm hfg.norm hh.norm).symm
    _ = _ := by rw [← tsum_mul_tsum_of_summable_norm hf.norm hg.norm]

theorem summable_three_separated_complex {f g h : ℤ → ℂ}
    (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    Summable (fun x : (ℤ × ℤ) × ℤ => f x.1.1*g x.1.2*h x.2) := by
  have hfg := summable_mul_of_summable_norm hf.norm hg.norm
  have hfull := summable_mul_of_summable_norm hfg.norm hh.norm
  exact hfull

noncomputable def dualShiftedGaussian (a s b : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-π/a*((n : ℂ)-b)^2+2*π*Complex.I*s*(n : ℂ))

theorem summable_dualShiftedGaussian {a : ℂ} (ha : 0 < a.re) (s b : ℂ) :
    Summable (dualShiftedGaussian a s b) := by
  have ha0 : a ≠ 0 := by intro hz; rw [hz] at ha; simpa using ha
  have hai : 0 < (1/a).re := by
    rw [one_div,Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.mpr ha0)
  have hs := (summable_shiftedGaussian hai (-b) s).mul_left
    (Complex.exp (2*π*Complex.I*s*b))
  apply hs.congr
  intro n
  rw [shiftedGaussian,dualShiftedGaussian,← Complex.exp_add]
  congr 1
  ring

/-- The full three-dimensional Gaussian transform, with absolute summability
used to identify the product of one-dimensional sums with the lattice sum. -/
theorem tsum_ternary_shiftedGaussian_poisson {a : ℂ} (ha : 0 < a.re)
    (s1 s2 s3 b1 b2 b3 : ℂ) :
    (∑' x : (ℤ × ℤ) × ℤ,
      shiftedGaussian a s1 b1 x.1.1 * shiftedGaussian a s2 b2 x.1.2 *
        shiftedGaussian a s3 b3 x.2) =
      (1/a^(1/2 : ℂ))^3 * ∑' y : (ℤ × ℤ) × ℤ,
        dualShiftedGaussian a s1 b1 y.1.1 * dualShiftedGaussian a s2 b2 y.1.2 *
          dualShiftedGaussian a s3 b3 y.2 := by
  rw [tsum_three_separated_complex (summable_shiftedGaussian ha s1 b1)
    (summable_shiftedGaussian ha s2 b2) (summable_shiftedGaussian ha s3 b3)]
  rw [tsum_three_separated_complex (summable_dualShiftedGaussian ha s1 b1)
    (summable_dualShiftedGaussian ha s2 b2) (summable_dualShiftedGaussian ha s3 b3)]
  rw [tsum_shiftedGaussian_poisson ha s1 b1,tsum_shiftedGaussian_poisson ha s2 b2,
    tsum_shiftedGaussian_poisson ha s3 b3]
  change _ = (1/a^(1/2 : ℂ))^3 *
    ((∑' n : ℤ, Complex.exp (-π/a*((n : ℂ)-b1)^2+2*π*Complex.I*s1*(n : ℂ))) *
      (∑' n : ℤ, Complex.exp (-π/a*((n : ℂ)-b2)^2+2*π*Complex.I*s2*(n : ℂ))) *
        (∑' n : ℤ, Complex.exp (-π/a*((n : ℂ)-b3)^2+2*π*Complex.I*s3*(n : ℂ))))
  ring

end Ramanujan.MultiQuintuple
