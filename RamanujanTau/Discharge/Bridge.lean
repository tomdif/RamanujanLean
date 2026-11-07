import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.MathlibBridge
import RamanujanTau.HeckeQExp
import RamanujanTau.HeckeTheory
import RamanujanTau.HeckeRecurrence
import RamanujanTau.Multiplicativity
import RamanujanTau.TauBridge

/-! # Discharging `TauMatchesDiscriminant`; auditing the Hecke classes

* `TauMatchesDiscriminant` (`MathlibBridge.lean`) had **no instance** anywhere in the repo, although the
  needed analytic fact is `DiscriminantBridge.qExpansion_discriminant_coeff` (`DiscriminantQExpansion.lean`).
  We provide the instance here via `tau_eq_tauPS`.
* `TauHeckeMaster` has the global instance `HeckeQExp.tauHeckeMaster`; `TauHeckeRecurrence` and
  `TauMultiplicative` then follow from the global instances `instTauHeckeRecurrenceOfMaster`,
  `instTauMultiplicativeOfMaster` (`HeckeTheory.lean`). We only re-export them under audit names.
-/

set_option autoImplicit false

namespace RamanujanTau.Discharge
open RamanujanTau

/-- **`Δ`'s q-expansion is `Σ τ(n) qⁿ`**, for Mathlib's `ModularForm.discriminant`. -/
theorem discriminantQExpansion_eq_tau_unconditional (n : ℕ) : discriminantQExpansion n = tauComplex n := by
  have h := DiscriminantBridge.qExpansion_discriminant_coeff n
  rw [← tau_eq_tauPS] at h
  exact h

instance tauMatchesDiscriminant : TauMatchesDiscriminant :=
  ⟨fun n _ => discriminantQExpansion_eq_tau_unconditional n,
   by rw [discriminantQExpansion_eq_tau_unconditional, tauComplex_zero]⟩

/-- Global instances, re-exported for the audit. -/
theorem tauHeckeMaster_holds : TauHeckeMaster := inferInstance
theorem tauHeckeRecurrence_holds : TauHeckeRecurrence := inferInstance
theorem tauMultiplicative_holds : TauMultiplicative := inferInstance

/-- Lehmer's conjecture ⇔ non-vanishing of `Δ`'s q-coefficients, now with the bridge discharged. -/
theorem lehmer_iff_qExpansion_nonvanishing_unconditional :
    (∀ n : ℕ, 1 ≤ n → tau n ≠ 0) ↔ (∀ n : ℕ, 1 ≤ n → discriminantQExpansion n ≠ 0) :=
  lehmer_iff_qExpansion_nonvanishing

end RamanujanTau.Discharge

#print axioms RamanujanTau.Discharge.tauMatchesDiscriminant
#print axioms RamanujanTau.Discharge.tauHeckeMaster_holds
#print axioms RamanujanTau.Discharge.tauHeckeRecurrence_holds
#print axioms RamanujanTau.Discharge.tauMultiplicative_holds
#print axioms RamanujanTau.Discharge.lehmer_iff_qExpansion_nonvanishing_unconditional
