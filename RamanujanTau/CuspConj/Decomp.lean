/-
# Real/imaginary decomposition `f = g + i h` and linearity of `L(f,s)`

* `coef_add`, `coef_smul`: `a_{f+g} = a_f + a_g`, `a_{c f} = c a_f`;
* `reF f = (f + f^ρ)/2`, `imF f = −(i/2)(f − f^ρ)` have real coefficients
  (`Re a_f(n)`, `Im a_f(n)`), and `f = reF f + i • imF f`;
* `fL_add`, `fL_smul`: `L(f₁+f₂,s) = L(f₁,s) + L(f₂,s)`, `L(c f,s) = c L(f,s)` (`k ≥ 1`).
-/
import RamanujanTau.CuspConj.Basic

set_option autoImplicit false

namespace RamanujanTau.CuspConj

open Complex MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate
open RamanujanTau.HeckeConvexGeneral

variable {k : ℕ}

lemma coef_add (f g : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : coef (f + g) n = coef f n + coef g n := by
  refine coef_eq_of_hasSum (f + g) (c := fun n => coef f n + coef g n) (fun w => ?_) n
  rw [CuspForm.add_apply]
  refine ((hasSum_coef f w).add (hasSum_coef g w)).congr_fun fun m => ?_
  simp only [smul_eq_mul]; ring

lemma coef_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (c : ℂ) (n : ℕ) : coef (c • f) n = c * coef f n := by
  refine coef_eq_of_hasSum (c • f) (c := fun n => c * coef f n) (fun w => ?_) n
  simp only [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine ((hasSum_coef f w).mul_left c).congr_fun fun m => ?_
  simp only [smul_eq_mul]; ring

/-- `(f + f^ρ)/2`, coefficients `Re a_f(n)`. -/
noncomputable def reF (f : CuspForm 𝒮ℒ (k : ℤ)) : CuspForm 𝒮ℒ (k : ℤ) :=
  (1 / 2 : ℂ) • (f + cuspConj f)

/-- `−(i/2)(f − f^ρ)`, coefficients `Im a_f(n)`. -/
noncomputable def imF (f : CuspForm 𝒮ℒ (k : ℤ)) : CuspForm 𝒮ℒ (k : ℤ) :=
  (-I / 2 : ℂ) • (f + (-1 : ℂ) • cuspConj f)

lemma coef_reF (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : coef (reF f) n = ((coef f n).re : ℂ) := by
  rw [reF, coef_smul, coef_add, coef_cuspConj]
  apply Complex.ext <;> simp <;> ring

lemma coef_imF (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : coef (imF f) n = ((coef f n).im : ℂ) := by
  rw [imF, coef_smul, coef_add, coef_smul, coef_cuspConj]
  apply Complex.ext <;> simp <;> ring

lemma reF_real (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : (coef (reF f) n).im = 0 := by
  rw [coef_reF]; simp

lemma imF_real (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : (coef (imF f) n).im = 0 := by
  rw [coef_imF]; simp

/-- **`f = (f+f^ρ)/2 + i · (−(i/2))(f − f^ρ)`.** -/
theorem eq_reF_add_imF (f : CuspForm 𝒮ℒ (k : ℤ)) : f = reF f + I • imF f := by
  ext z
  simp only [reF, imF, CuspForm.coe_add, CuspForm.IsGLPos.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  linear_combination ((f z - cuspConj f z) / 2) * Complex.I_sq

/-! ### Linearity of `L(f,s)` -/

lemma heckeF_add (f g : CuspForm 𝒮ℒ (k : ℤ)) (t : ℝ) :
    heckeF (f + g) t = heckeF f t + heckeF g t := by
  simp [heckeF, CuspForm.add_apply]

lemma heckeF_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (c : ℂ) (t : ℝ) :
    heckeF (c • f) t = c • heckeF f t := by
  simp [heckeF, CuspForm.IsGLPos.coe_smul]

lemma heckeLambda_add (f g : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (s : ℂ) :
    heckeLambda (f + g) s = heckeLambda f s + heckeLambda g s := by
  have hf : MellinConvergent (heckeF f) s := ((heckePair f hk).hasMellin s).1
  have hg : MellinConvergent (heckeF g) s := ((heckePair g hk).hasMellin s).1
  unfold heckeLambda mellin
  simp_rw [heckeF_add, smul_add]
  exact integral_add hf hg

lemma heckeLambda_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (c : ℂ) (s : ℂ) :
    heckeLambda (c • f) s = c * heckeLambda f s := by
  unfold heckeLambda
  have : heckeF (c • f) = fun t => c • heckeF f t := funext (heckeF_smul f c)
  rw [this, mellin_const_smul, smul_eq_mul]

theorem fL_add (f g : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (s : ℂ) :
    fL (f + g) s = fL f s + fL g s := by
  unfold fL; rw [heckeLambda_add f g hk]; ring

theorem fL_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (c : ℂ) (s : ℂ) : fL (c • f) s = c * fL f s := by
  unfold fL; rw [heckeLambda_smul]; ring

end RamanujanTau.CuspConj
