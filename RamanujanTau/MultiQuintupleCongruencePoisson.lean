/-
# Poisson summation after a finite congruence projection
-/
import RamanujanTau.MultiQuintupleGaussianPoisson
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

theorem congruence_exponential_projector (p : ℕ) [NeZero p] (D : ℤ) :
    (if (p : ℤ) ∣ D then (1 : ℂ) else 0) =
      (1/(p : ℂ))*∑ h : ZMod p, Complex.exp
        (2*Real.pi*Complex.I*(h.val : ℂ)*(D : ℂ)/(p : ℂ)) := by
  classical
  have hsum := AddChar.sum_mulShift (R' := ℂ) (D : ZMod p) (ZMod.isPrimitive_stdAddChar p)
  have hterm : ∀ h : ZMod p, ZMod.stdAddChar (h*(D : ZMod p)) =
      Complex.exp (2*Real.pi*Complex.I*(h.val : ℂ)*(D : ℂ)/(p : ℂ)) := by
    intro h
    have he : h*(D : ZMod p)=(((h.val : ℤ)*D : ℤ) : ZMod p) := by simp
    rw [he,ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp only [hterm,ZMod.card] at hsum
  rw [hsum]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  by_cases hd : (p : ℤ) ∣ D
  · simp [hd,(ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hd,hpC]
  · simp [hd,((ZMod.intCast_zmod_eq_zero_iff_dvd D p).not).mpr hd]

abbrev TernaryComplexPoint := (ℂ × ℂ) × ℂ

noncomputable def separatedGaussian (a : ℂ) (s b : TernaryComplexPoint)
    (x : (ℤ × ℤ) × ℤ) : ℂ :=
  shiftedGaussian a s.1.1 b.1.1 x.1.1 * shiftedGaussian a s.1.2 b.1.2 x.1.2 *
    shiftedGaussian a s.2 b.2 x.2

noncomputable def separatedDualGaussian (a : ℂ) (s b : TernaryComplexPoint)
    (x : (ℤ × ℤ) × ℤ) : ℂ :=
  dualShiftedGaussian a s.1.1 b.1.1 x.1.1 * dualShiftedGaussian a s.1.2 b.1.2 x.1.2 *
    dualShiftedGaussian a s.2 b.2 x.2

theorem summable_separatedGaussian {a : ℂ} (ha : 0 < a.re) (s b : TernaryComplexPoint) :
    Summable (separatedGaussian a s b) := by
  have h1 := summable_shiftedGaussian ha s.1.1 b.1.1
  have h2 := summable_shiftedGaussian ha s.1.2 b.1.2
  have h3 := summable_shiftedGaussian ha s.2 b.2
  exact summable_three_separated_complex h1 h2 h3

theorem summable_separatedDualGaussian {a : ℂ} (ha : 0 < a.re) (s b : TernaryComplexPoint) :
    Summable (separatedDualGaussian a s b) := by
  have h1 := summable_dualShiftedGaussian ha s.1.1 b.1.1
  have h2 := summable_dualShiftedGaussian ha s.1.2 b.1.2
  have h3 := summable_dualShiftedGaussian ha s.2 b.2
  exact summable_three_separated_complex h1 h2 h3

noncomputable def congruenceModulation (p : ℕ) (c1 c2 c3 : ℤ) (h : ZMod p) : TernaryComplexPoint :=
  (((h.val : ℂ)*c1/p,(h.val : ℂ)*c2/p),(h.val : ℂ)*c3/p)

noncomputable def congruenceGaussianPhase (p : ℕ) (c1 c2 c3 d : ℤ)
    (s : TernaryComplexPoint) (h : ZMod p) : ℂ :=
  Complex.exp (-2*Real.pi*Complex.I*(h.val : ℂ)/p*
    ((d : ℂ)+c1*s.1.1+c2*s.1.2+c3*s.2))

theorem modulated_separatedGaussian (p : ℕ) (c1 c2 c3 d : ℤ)
    (a : ℂ) (s : TernaryComplexPoint) (h : ZMod p) (x : (ℤ × ℤ) × ℤ) :
    Complex.exp (2*Real.pi*Complex.I*(h.val : ℂ)*
      ((c1*x.1.1+c2*x.1.2+c3*x.2-d : ℤ) : ℂ)/p)*separatedGaussian a s 0 x =
      congruenceGaussianPhase p c1 c2 c3 d s h *
        separatedGaussian a s (congruenceModulation p c1 c2 c3 h) x := by
  unfold separatedGaussian shiftedGaussian congruenceGaussianPhase congruenceModulation
  simp only [Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,add_zero]
  repeat rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A congruence-restricted ternary Gaussian transforms into a finite sum
of shifted dual Gaussians. All exchanges of infinite sums use absolute
summability of the actual Gaussian terms. -/
theorem congruence_gaussian_poisson (p : ℕ) [NeZero p] (c1 c2 c3 d : ℤ)
    {a : ℂ} (ha : 0 < a.re) (s : TernaryComplexPoint) :
    (∑' x : (ℤ × ℤ) × ℤ,
      if (p : ℤ) ∣ c1*x.1.1+c2*x.1.2+c3*x.2-d then separatedGaussian a s 0 x else 0) =
      (1/(p : ℂ))*(1/a^(1/2 : ℂ))^3 * ∑ h : ZMod p,
        congruenceGaussianPhase p c1 c2 c3 d s h *
          ∑' y : (ℤ × ℤ) × ℤ,
            separatedDualGaussian a s (congruenceModulation p c1 c2 c3 h) y := by
  classical
  have hpoint (x : (ℤ × ℤ) × ℤ) :
      (if (p : ℤ) ∣ c1*x.1.1+c2*x.1.2+c3*x.2-d then separatedGaussian a s 0 x else 0) =
      (1/(p : ℂ))*∑ h : ZMod p, congruenceGaussianPhase p c1 c2 c3 d s h *
        separatedGaussian a s (congruenceModulation p c1 c2 c3 h) x := by
    calc
      _ = (if (p : ℤ) ∣ c1*x.1.1+c2*x.1.2+c3*x.2-d then (1 : ℂ) else 0)*
          separatedGaussian a s 0 x := by split_ifs <;> simp
      _ = _ := by
        rw [congruence_exponential_projector,mul_assoc,Finset.sum_mul]
        simp_rw [modulated_separatedGaussian]
  simp_rw [hpoint]
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun h _ =>
    (summable_separatedGaussian ha s (congruenceModulation p c1 c2 c3 h)).mul_left _)]
  simp_rw [tsum_mul_left]
  have hpoisson (h : ZMod p) :
      (∑' x, separatedGaussian a s (congruenceModulation p c1 c2 c3 h) x) =
        (1/a^(1/2 : ℂ))^3 * ∑' y, separatedDualGaussian a s (congruenceModulation p c1 c2 c3 h) y :=
    tsum_ternary_shiftedGaussian_poisson ha _ _ _ _ _ _
  simp_rw [hpoisson]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

end Ramanujan.MultiQuintuple
