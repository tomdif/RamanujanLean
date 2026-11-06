/-
# Level-one cusp forms of odd weight vanish; trivial SCS for `f = 0`

`(-1) • z = z` and `f((-1)•z) = (-1)^k f(z)`, so `f = −f` for odd `k`.
-/
import RamanujanTau.SubconvexGeneral.TwoPointF

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open RamanujanTau.SubconvexGeneral RamanujanTau.HeckeConvexGeneral RamanujanTau.EigenformEdge
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

theorem eq_zero_of_odd (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : Odd k) : f = 0 := by
  ext z
  have h := f_smul f (-1) z
  have e : ((-1 : SL(2, ℤ)) • z : ℍ) = z := by
    rw [ModularGroup.SL_neg_smul, one_smul]
  rw [e] at h
  have hc : ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℂ) * (z : ℂ) +
      ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℂ) = -1 := by
    simp
  rw [hc, hk.neg_one_pow] at h
  have : f z = 0 := by linear_combination h / 2
  simpa using this

/-- `SCS_f` holds trivially (with any exponents) when `f = 0`. -/
theorem scsf_of_eq_zero {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : f = 0) (η B : ℝ) : SCSf f η B := by
  subst hf
  refine ⟨⟨0, le_rfl, fun h N _ => ?_⟩⟩
  have : ∀ n, nlam (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
    simp [nlam, coef, UpperHalfPlane.qExpansion_zero]
  simp [shS, this]

end RamanujanTau.SubconvexGeneral2
