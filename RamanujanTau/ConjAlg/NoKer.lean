/-
# `HConj` without the Tate-kernel hypothesis

`TateAdd.tateKernels` proves `HeckeBridge.TateKernels` for every prime `p ≥ 5`, so
`ConjAlg.HConj_C_of_val` holds with only the quotient valuation bound `QuotValBound`.
-/
import RamanujanTau.ConjAlg.HConj
import RamanujanTau.TateAdd.Final

set_option autoImplicit false

namespace ConjAlg
open Classical

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`HConj (φC ℓ)` from the quotient valuation bounds alone.** -/
theorem HConj_C_of_val' (hV : QuotValBound ℓ hℓ (SharpHQ.φC ℓ)) : SharpHQ.HConj ℓ hℓ (SharpHQ.φC ℓ) := by
  have hℓ0 : ℓ ≠ 0 := hℓp.out.ne_zero
  haveI : NeZero (ℓ : ℂ_[ℓ]) := ⟨by
    have : (ℓ : ℂ_[ℓ]) = algebraMap ℚ_[ℓ] ℂ_[ℓ] (ℓ : ℚ_[ℓ]) := by simp
    rw [this]; exact (map_ne_zero _).mpr (by exact_mod_cast hℓ0)⟩
  obtain ⟨ζK, hζK⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[ℓ] ℓ
  set F := FractionRing (PowerSeries ℂ_[ℓ])
  set L := AlgebraicClosure F
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let ι : PowerSeries ℂ_[ℓ] →+* L := (algebraMap F L).comp (algebraMap (PowerSeries ℂ_[ℓ]) F)
  have hι : Function.Injective ι :=
    (algebraMap F L).injective.comp (IsFractionRing.injective (PowerSeries ℂ_[ℓ]) F)
  exact HConj_C_of_val hℓ hζK ι hι (TateAdd.tateKernels hι hζK hℓ) hV

end ConjAlg
