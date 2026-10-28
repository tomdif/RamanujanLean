import RamanujanTau.HeckeBridge.Final
import RamanujanTau.HeckeBridge.Transport

/-!
# `HeckeBridge` entry point: `hKer` over any field of characteristic `0`

`hU_classical_of_field`: `hU_classical_unconditional` with `hKer` stated over an arbitrary field
`F ⊇ K⟦t⟧` (e.g. `LaurentSeries K`, `FractionRing K⟦t⟧`); it is moved to `AlgebraicClosure F`
by `tateKernels_lift`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial ModP

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [IsAlgClosed K]
  [DecidableEq K] (p : ℕ) [hp : Fact p.Prime]

/-- **Classical `hU`, modulo `hKer` over any characteristic-`0` field `F` receiving `K⟦t⟧`.** -/
theorem hU_classical_of_field {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    {F : Type*} [Field F] [CharZero F] [DecidableEq F] (ι₀ : PowerSeries K →+* F)
    (hι₀ : Function.Injective ι₀) (hKer : TateKernels p F ι₀ ζ) {k : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (Qall : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K) :
    ∀ W, KatzForms.IsTest W → IsQuotEnum p W (Qall W) →
      ∑ c : Fin p, eval (KatzForms.pt (Qall W c.succ)) P =
        (p : K) * eval (KatzForms.pt W) (HeckeQExp.heckePoly p P) - eval (KatzForms.pt (Qall W 0)) P := by
  classical
  haveI : CharZero (AlgebraicClosure F) :=
    charZero_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective
  exact hU_classical_unconditional p hζ hp2 ((algebraMap F (AlgebraicClosure F)).comp ι₀)
    ((algebraMap F (AlgebraicClosure F)).injective.comp hι₀)
    (tateKernels_lift p ι₀ ζ hKer) hP Qall

end HeckeBridge

#print axioms HeckeBridge.hU_classical_of_field
#print axioms HeckeBridge.hU_classical_unconditional
#print axioms HeckeBridge.classical_hU_short
#print axioms HeckeBridge.subSum_hecke
#print axioms HeckeBridge.Siso_eq_hecke
#print axioms HeckeBridge.hAlg
#print axioms HeckeBridge.hT_of_kernels
#print axioms HeckeBridge.exists_quotEnum
#print axioms HeckeBridge.tateKernels_lift
#print axioms HeckeBridge.tateKernels_of_kernels
