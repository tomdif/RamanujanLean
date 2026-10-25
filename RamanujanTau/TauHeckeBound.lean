/-
# Hecke's bound for Ramanujan's τ: `τ(n) = O(n⁶)`

Mathlib's `CuspFormClass.qExpansion_isBigO` (Hecke's bound `O(n^{k/2})` for the coefficients of a cusp form of weight
`k`) applied to `Δ` (weight 12), transported to the integer sequence `τ` through the analytic–formal bridge
`qExpansion_discriminant_coeff` and `tau_eq_tauPS`.

This is the trivial (Hecke) exponent `k/2 = 6`; Deligne's bound is `11/2 + ε`.
-/
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.TauBridge
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false

namespace RamanujanTau
open Filter Asymptotics ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- **Hecke's bound**: `τ(n) = O(n⁶)`. -/
theorem tau_isBigO : (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (6 : ℝ) := by
  have h := CuspFormClass.qExpansion_isBigO (k := 12) (Γ := 𝒮ℒ) CuspForm.discriminant
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  have h12 : ((12 : ℤ) : ℝ) / 2 = 6 := by norm_num
  rw [h12] at h
  refine (IsBigO.of_norm_left ?_).trans h.norm_left
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [one_mul, norm_norm]
  have hc : (UpperHalfPlane.qExpansion 1 CuspForm.discriminant).coeff n = ((tau n : ℤ) : ℂ) := by
    rw [tau_eq_tauPS, ← DiscriminantBridge.qExpansion_discriminant_coeff]; rfl
  rw [hc, Complex.norm_intCast]; simp

end RamanujanTau
