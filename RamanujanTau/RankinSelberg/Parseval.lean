/-
# Parseval on a horizontal line for a level-one cusp form

For a cusp form `f = ∑ aₙ qⁿ` of weight `k` for `SL₂(ℤ)` and `y > 0`,

  `∫₀¹ |f(x + iy)|² dx = ∑ₙ |aₙ|² e^{-4πny}`.

Proof: write `|f|² = f · conj f = ∑ₙ f · conj(aₙ qⁿ)`; dominated convergence (the cusp-form
bound `‖f‖ ≤ C / y^{k/2}` times the absolutely convergent `∑ |aₙ| e^{-2πny}`) swaps `∫` and `∑`;
then `conj(qⁿ) = e^{-4πny} q^{-n}` and Mathlib's coefficient integral
`aₙ = ∫₀¹ q^{-n} f dx` (`ModularFormClass.qExpansion_coeff_eq_intervalIntegral`) finishes.
-/
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne

set_option autoImplicit false

namespace RamanujanTau.RankinSelberg

open Complex ModularForm MeasureTheory
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real

local notation "𝕢" => Function.Periodic.qParam

/-- The point `x + iy` of `ℍ`. -/
def hp {y : ℝ} (hy : 0 < y) (x : ℝ) : ℍ := ⟨(x : ℂ) + y * I, by simpa using hy⟩

lemma hp_coe {y : ℝ} (hy : 0 < y) (x : ℝ) : ((hp hy x : ℍ) : ℂ) = (x : ℂ) + y * I := rfl

lemma hp_im {y : ℝ} (hy : 0 < y) (x : ℝ) : (hp hy x).im = y := by
  simp [UpperHalfPlane.im, hp]

lemma continuous_hp {y : ℝ} (hy : 0 < y) : Continuous (hp hy) :=
  Continuous.upperHalfPlaneMk (by fun_prop) (fun x => by simpa using hy)

lemma norm_qParam_hp {y : ℝ} (x : ℝ) :
    ‖𝕢 1 ((x : ℂ) + y * I)‖ = Real.exp (-2 * π * y) := by
  rw [Function.Periodic.norm_qParam]; simp

/-- `conj (qⁿ) = e^{-4πny} · q^{-n}` on the line `Im = y`. -/
lemma conj_qParam_pow {y : ℝ} (x : ℝ) (n : ℕ) :
    conj (𝕢 1 ((x : ℂ) + y * I) ^ n) =
      ((Real.exp (-2 * π * y) ^ (2 * n) : ℝ) : ℂ) * (1 / 𝕢 1 ((x : ℂ) + y * I) ^ n) := by
  set q := 𝕢 1 ((x : ℂ) + y * I)
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hns : (Complex.normSq q : ℂ) = ((Real.exp (-2 * π * y) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_norm_sq, norm_qParam_hp]
  have hmc : q * conj q = ((Real.exp (-2 * π * y) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, hns]
  have hc : conj q = ((Real.exp (-2 * π * y) ^ 2 : ℝ) : ℂ) / q := by
    rw [eq_div_iff hq0, mul_comm, hmc]
  rw [map_pow, hc, div_pow, pow_mul]
  push_cast
  field_simp

variable {F : Type*} [FunLike F ℍ ℂ]

/-- **Parseval on the horizontal line `Im z = y`**: for a level-one cusp form `f` and `y > 0`,
`∑ₙ |aₙ(f)|² e^{-4πny} = ∫₀¹ |f(x+iy)|² dx`. -/
theorem hasSum_normSq_coeff {k : ℤ} [CuspFormClass F 𝒮ℒ k] (f : F) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-2 * π * y) ^ (2 * n))
      (∫ x in (0 : ℝ)..1, ‖f (hp hy x)‖ ^ 2) := by
  set r := Real.exp (-2 * π * y) with hr
  set a : ℕ → ℂ := fun n => (qExpansion 1 f).coeff n
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hq : ∀ x : ℝ, HasSum (fun n => a n * 𝕢 1 ((x : ℂ) + y * I) ^ n) (f (hp hy x)) := fun x =>
    by simpa [a, smul_eq_mul, hp_coe] using
      hasSum_qExpansion one_pos hper (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
        (hp hy x)
  -- absolute summability of `|aₙ| rⁿ`
  have hsum : Summable (fun n => ‖a n‖ * r ^ n) := by
    have := (summable_norm_iff.mpr (hq 0).summable)
    refine this.congr fun n => ?_
    rw [norm_mul, norm_pow, norm_qParam_hp]
  -- the uniform bound on the line
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  set B := C / y ^ ((k : ℝ) / 2)
  have hB : ∀ x, ‖f (hp hy x)‖ ≤ B := fun x => by
    have := hC (hp hy x); rwa [hp_im] at this
  set Fn : ℕ → ℝ → ℂ := fun n x => f (hp hy x) * conj (a n * 𝕢 1 ((x : ℂ) + y * I) ^ n)
  have hcontf : Continuous (fun x : ℝ => f (hp hy x)) :=
    (ModularFormClass.holo f).continuous.comp (continuous_hp hy)
  have hcontq : Continuous (fun x : ℝ => 𝕢 1 ((x : ℂ) + y * I)) := by
    unfold Function.Periodic.qParam; fun_prop
  have hDCT : HasSum (fun n => ∫ x in (0 : ℝ)..1, Fn n x)
      (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (hp hy x))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => B * (‖a n‖ * r ^ n)) (fun n => ?_) (fun n => ?_) ?_ intervalIntegrable_const ?_
    · exact (hcontf.mul (continuous_conj.comp
        (continuous_const.mul (hcontq.pow n)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x _ => ?_
      simp only [Fn, norm_mul, Complex.norm_conj, norm_pow, norm_qParam_hp]
      gcongr
      exact hB x
    · exact Filter.Eventually.of_forall fun x _ => hsum.mul_left B
    · refine Filter.Eventually.of_forall fun x _ => ?_
      exact ((hasSum_conj'.mpr (hq x)).mul_left (f (hp hy x)))
  -- evaluate each term
  have hterm : ∀ n, ∫ x in (0 : ℝ)..1, Fn n x =
      ((‖a n‖ ^ 2 * r ^ (2 * n) : ℝ) : ℂ) := by
    intro n
    have hcoef := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos
      one_mem_strictPeriods_SL n hy
    have hpt : ∀ x : ℝ, Fn n x = (conj (a n) * ((r ^ (2 * n) : ℝ) : ℂ)) *
        (1 / 𝕢 1 ((x : ℂ) + y * I) ^ n * f ⟨(x : ℂ) + y * I, by simpa using hy⟩) := by
      intro x
      simp only [Fn, map_mul, conj_qParam_pow x n]
      rw [← hr]; simp only [hp]; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    have : (∫ x in (0 : ℝ)..1, 1 / 𝕢 1 ((x : ℂ) + y * I) ^ n *
        f ⟨(x : ℂ) + y * I, by simpa using hy⟩) = a n := by
      simp only [a, hcoef]; simp
    rw [this]
    have hnc : conj (a n) * a n = ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast at hnc ⊢
    rw [← hnc]; ring
  have hint : (∫ x in (0 : ℝ)..1, f (hp hy x) * conj (f (hp hy x))) =
      ((∫ x in (0 : ℝ)..1, ‖f (hp hy x)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1 with x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hterm, hint] at hDCT
  exact Complex.hasSum_ofReal.mp hDCT

end RamanujanTau.RankinSelberg
