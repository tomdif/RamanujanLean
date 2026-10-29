import RamanujanTau.TheoremA.EtaCuspDecay

/-!
# Three actual weight-six cusp forms at level six

The eta quotients are holomorphic, satisfy the full Γ₀(6) transformation law,
and vanish at every cusp. Identifying their first Fourier coefficients is a
separate step, completed in `EtaQExpansion`; `WeightSixIdentity` proves that
their first three coefficients give coordinates on the entire cusp space.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm CongruenceSubgroup Matrix
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

theorem basisFunction_slash_zero (a : Fin 3) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (basisFunction a ∣[(6 : ℤ)] γ) := by
  obtain ⟨i, hi⟩ := LevelSix.exists_rep γ
  have he : γ = (γ * (LevelSix.rep i)⁻¹) * LevelSix.rep i := by group
  rw [he, SlashAction.slash_mul, basisFunction_slash a _ hi]
  exact basisFunction_rep_zero a i

/-- The three eta quotients, now bundled as genuine complex cusp forms. -/
noncomputable def basisCuspForm (a : Fin 3) :
    CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6 where
  toSlashInvariantForm := basisSlashInvariant a
  holo' := basisFunction_holo a
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact basisFunction_slash_zero a γ

@[simp] theorem basisCuspForm_apply (a : Fin 3) (z : ℍ) :
    basisCuspForm a z = basisFunction a z := rfl

theorem basisCuspForm_ne_zero (a : Fin 3) : basisCuspForm a ≠ 0 := by
  intro h
  exact basisFunction_ne_zero a UpperHalfPlane.I (congrArg (fun f => f UpperHalfPlane.I) h)

end RamanujanTau.TheoremA.EtaSquared
