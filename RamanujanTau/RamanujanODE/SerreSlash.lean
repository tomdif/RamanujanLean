import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Slash-equivariance of the Serre derivative

* `D_slash`: `D (F ∣[k] γ) = (D F) ∣[k+2] γ − k (2πi)⁻¹ (c / (cz+d)) (F ∣[k] γ)`.
* `serre_slash_equivariant`: `(∂_k F) ∣[k+2] γ = ∂_k (F ∣[k] γ)`; hence `∂_k` preserves level-one
  slash invariance (`serre_slash_invariant`).
* `serreE2_slash_invariant`: `∂₁ E₂ = D E₂ − E₂²/12` is weight-4 slash invariant, although `E₂` is not.

The computations in this file are adapted from the Sphere-Packing-Lean project
(https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean, files
`SpherePacking/ModularForms/Derivative.lean` and `SerreDerivativeSlash.lean`, commit `0c19dab`),
Copyright (c) 2024 The Sphere Packing Contributors, released under the Apache 2.0 license,
and adjusted to the present Mathlib (`Derivative.normalizedDerivOfComplex`, `serreDerivative`).
-/

set_option autoImplicit false

namespace RamanujanODEProof
open UpperHalfPlane hiding I
open Real Complex ModularForm EisensteinSeries Derivative
open scoped MatrixGroups Manifold

noncomputable section

section DSlashHelpers
variable (γ : SL(2, ℤ))

lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

lemma differentiableAt_denom (z : ℂ) : DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]; fun_prop

lemma differentiableAt_num (z : ℂ) : DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]; fun_prop

lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  simp only [ModularGroup.denom_apply, num, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, ofReal_intCast] at *
  have hnum_eq : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 0 : ℤ) * z + (γ 1 1 : ℤ)) -
      ((γ 0 0 : ℤ) * z + (γ 0 1 : ℤ)) * (γ 1 0 : ℤ) = 1 := by linear_combination hdet
  simp only [hnum_eq, one_div]

lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff := differentiableAt_denom γ (z : ℂ)
  have hderiv_zpow := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    rw [← deriv_denom]; exact hdiff.hasDerivAt
  have hcomp := hderiv_zpow.comp (z : ℂ) hderiv_denom
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := rfl
  rw [← heq, hcomp.deriv]; simp only [Int.cast_neg]; ring

end DSlashHelpers

/-- How `D` interacts with the slash action. -/
lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  ext z
  unfold normalizedDerivOfComplex
  simp only [Pi.sub_apply]
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    congr 1
    · let gz : ℍ := γ • ⟨w, hw⟩
      have hsmul_coe : (gz : ℂ) = num γ w / denom γ w := by
        have h := UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
        simp only [gz] at h ⊢
        exact h
      have hmob_im : (num γ w / denom γ w).im > 0 := by
        rw [← hsmul_coe]; exact gz.im_pos
      congr 1
      apply UpperHalfPlane.ext
      rw [ofComplex_apply_of_im_pos hmob_im]
      exact hsmul_coe
  rw [hcomp]
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z z.im_pos))
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z z.im_pos)
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]
    exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  have hdiff_F_mobius :
      DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]
    exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  have hfun_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * (fun w => (denom γ w) ^ (-k))) := rfl
  rw [hfun_eq]
  have hprod := deriv_mul hdiff_F_mobius hdiff_denom_zpow
  rw [hprod]
  have hchain : deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
      deriv (F ∘ ofComplex) (num γ z / denom γ z) * deriv (fun w => num γ w / denom γ w) z := by
    rw [hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv]
  have hderiv_mob := deriv_moebius γ z
  have hderiv_zpow := deriv_denom_zpow γ k z
  rw [hchain, hderiv_mob, hderiv_zpow]
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _]
    rw [hpow_combine, hpow_m1]
  simp only [zpow_neg_one]
  ring

/-- **Equivariance of the Serre derivative.** -/
theorem serre_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k (F ∣[k] γ) := by
  have hD := D_slash k F hF γ
  have hE₂ := E2_slash_action γ
  have hmul := ModularForm.mul_slash_SL2 (2 : ℤ) k γ E2 F
  ext z
  simp only [serreDerivative_apply]
  have hLHS : (serreDerivative (↑k) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((E2 ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
    have h := congrFun hmul z
    simp only [Pi.mul_apply, show (2 : ℤ) + k = k + 2 from by omega] at h
    simp only [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply] at h ⊢
    rw [← h]; ring
  rw [hLHS]
  have hE₂z := congrFun hE₂ z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE₂z
  rw [hE₂z]
  have hDz := congrFun hD z
  simp only [Pi.sub_apply] at hDz
  rw [hDz]
  simp only [show D2 γ z = (2 * ↑π * I * ↑↑(γ 1 0)) / denom γ ↑z from rfl, riemannZeta_two]
  have hpi_ne : (↑π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdenom_ne : denom γ ↑z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  field_simp [hdenom_ne, hpi_ne]
  ring_nf
  simp only [I_sq]
  ring

theorem serre_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k F := by
  rw [serre_slash_equivariant k F hF, h]

/-! ### `∂₁ E₂` -/

lemma D_D2 (γ : SL(2, ℤ)) (z : ℍ) :
    D (D2 γ) z = - (γ 1 0 : ℂ) ^ 2 / (denom γ z) ^ 2 := by
  have hz_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hderiv : deriv ((D2 γ) ∘ ofComplex) z =
      deriv (fun w => (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, EisensteinSeries.D2]
  simp only [normalizedDerivOfComplex, hderiv, div_eq_mul_inv, ← zpow_neg_one]
  rw [deriv_const_mul _ (.zpow (differentiableAt_denom γ z) (.inl hz_ne)),
      deriv_denom_zpow γ 1 z]
  simp only [Int.reduceNeg, Int.reduceSub, zpow_neg_one]; field_simp; ring

lemma mdifferentiable_D2 (γ : SL(2, ℤ)) : MDiff (D2 γ) := fun z => by
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have : DifferentiableAt ℂ (fun w => (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) z :=
    .div (differentiableAt_const _) (differentiableAt_denom γ z) (denom_ne_zero γ z)
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, EisensteinSeries.D2]

/-- `∂₁ E₂ = D E₂ − E₂²/12` is weight-4 slash invariant under `SL(2, ℤ)`. -/
lemma serreE2_slash_invariant (γ : SL(2, ℤ)) :
    (serreDerivative 1 E2) ∣[(4 : ℤ)] γ = serreDerivative 1 E2 := by
  have hserre12 : serreDerivative 1 E2 = serreDerivative 2 E2 + (1 / 12 : ℂ) • (E2 * E2) := by
    ext z; simp only [serreDerivative_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]; ring
  have hequiv := serre_slash_equivariant 2 E2 E2_mdifferentiable γ
  have hE₂slash := E2_slash_action γ
  have hprod := ModularForm.mul_slash_SL2 (2 : ℤ) (2 : ℤ) γ E2 E2
  ext z
  rw [hserre12]
  simp only [SlashAction.add_slash, Pi.add_apply, ModularForm.SL_smul_slash, Pi.smul_apply,
    smul_eq_mul]
  rw [show (serreDerivative 2 E2 ∣[(4 : ℤ)] γ) z = serreDerivative 2 (E2 ∣[(2 : ℤ)] γ) z by
        simpa using congrFun hequiv z,
      show ((E2 * E2) ∣[(4 : ℤ)] γ) z = (E2 ∣[(2 : ℤ)] γ) z * (E2 ∣[(2 : ℤ)] γ) z by
        simpa using congrFun hprod z]
  set α := (1 : ℂ) / (2 * riemannZeta 2) with hα_def
  have hE₂slash_fun : (E2 ∣[(2 : ℤ)] γ) = E2 - α • D2 γ := by
    ext w; simpa using congrFun hE₂slash w
  rw [hE₂slash_fun]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hD_lin : D (E2 - α • D2 γ) z = D E2 z - α * D (D2 γ) z := by
    have hαD₂ := (mdifferentiable_D2 γ).const_smul α
    simp only [normalizedDerivOfComplex_sub E2 _ E2_mdifferentiable hαD₂,
      normalizedDerivOfComplex_smul α _ (mdifferentiable_D2 γ), Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  simp only [serreDerivative_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hD_lin, D_D2 γ z]
  have hα_val : α = 3 / π ^ 2 := by simp only [hα_def, riemannZeta_two]; field_simp; ring
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show D2 γ z = (2 * π * I * (γ 1 0 : ℂ)) / denom γ z from rfl, hα_val]
  field_simp [UpperHalfPlane.denom_ne_zero γ z, hpi_ne]
  ring_nf
  simp only [Complex.I_sq]
  ring

end

end RamanujanODEProof
