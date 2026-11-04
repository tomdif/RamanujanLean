import RamanujanTau.FiniteArithmetic.SmallThreshold
import RamanujanTau.OrdQuot.Final
import RamanujanTau.AllQuotients.Final
import RamanujanTau.OrdQuot.Atkin
import RamanujanTau.VLayer.HG

/-! # The Atkin–O'Brien analytic hypotheses, discharged at every prime `ℓ ≥ 5` (resp. `ℓ ≥ 11`)

The Atkin–O'Brien chain in the repo threads a family of named `Prop` hypotheses
(`UB`, `DB`, `HQ`, `SharpHQ.HConj`, `UBSharp.QuotBound`, `UBSharp.QuotEBound`, `ConjAlg.QuotValBound`,
`QuotE.OrdEBound`, `AllQuotients.OrdBound`, `OrdQuot.ProdDelta`) through ~40 conditional theorems
(`atkin_obrien_13'`, `''`, `'''`, `''''`, `_conj`, `_quot`, `_velu`, `_ordE`, `_ord`, `_UB`, `_geom`, `_Cp`, …).
All of these hypotheses are now theorems at the canonical embedding `SharpHQ.φC ℓ : ℤ_[ℓ] →+* ℂ_[ℓ]`;
the proofs are scattered (`OrdQuot.prodDelta_C`, `OrdQuot.ordEBound_C'`, `QuotE.quotEBound_C_of_ord`,
`UBSharp.UB_of_E_C`, `ConjAlg.HConj_C_of_val'`, `SharpHQ.HQ_of_conj_C`, `VLayer.DB_of_UB_HQ`,
`OrdQuot.ordBound_C`, `FiniteArithmetic.SmallThreshold.ub_db`). This file collects them under uniform
`…_unconditional` names. The headline unconditional theorems are `OrdQuot.atkin_obrien_{13,17,19,23}`.

Not discharged (and not needed: bypassed by `VLayer.DB_of_UB_HQ`): `DBound.HV`, `VLayer.HVQ`, `DBound.HW`.
-/

set_option autoImplicit false

namespace RamanujanTau.Discharge.AtkinInputs
open AtkinOBrienFinal

variable {ℓ : ℕ} [Fact ℓ.Prime]
open Classical

theorem prodDelta_unconditional (hℓ : 5 ≤ ℓ) : OrdQuot.ProdDelta ℓ ℂ_[ℓ] := OrdQuot.prodDelta_C hℓ

theorem ordEBound_unconditional (hℓ : 5 ≤ ℓ) : QuotE.OrdEBound hℓ (SharpHQ.φC ℓ) := OrdQuot.ordEBound_C' hℓ

theorem quotEBound_unconditional (hℓ : 5 ≤ ℓ) : UBSharp.QuotEBound ℓ hℓ (SharpHQ.φC ℓ) :=
  QuotE.quotEBound_C_of_ord hℓ (ordEBound_unconditional hℓ)

theorem quotValBound_unconditional (hℓ : 5 ≤ ℓ) : ConjAlg.QuotValBound ℓ hℓ (SharpHQ.φC ℓ) := by
  classical exact (quotEBound_unconditional hℓ).toQuotValBound _

theorem quotBound_unconditional (hℓ : 5 ≤ ℓ) : UBSharp.QuotBound ℓ hℓ (SharpHQ.φC ℓ) := by
  classical exact UBSharp.quotBound_of_E_C hℓ (quotEBound_unconditional hℓ)

theorem ordBound_unconditional (hℓ : 5 ≤ ℓ) : AllQuotients.OrdBound hℓ (SharpHQ.φC ℓ) := by
  classical exact OrdQuot.ordBound_C hℓ

theorem hConj_unconditional (hℓ : 5 ≤ ℓ) : SharpHQ.HConj ℓ hℓ (SharpHQ.φC ℓ) :=
  ConjAlg.HConj_C_of_val' hℓ (quotValBound_unconditional hℓ)

theorem UB_unconditional (hℓ : 5 ≤ ℓ) : UB ℓ hℓ := by
  classical exact UBSharp.UB_of_E_C hℓ (quotEBound_unconditional hℓ)

theorem HQ_unconditional (hℓ : 5 ≤ ℓ) (h11 : 11 ≤ ℓ) : DBound.HQ ℓ hℓ :=
  SharpHQ.HQ_of_conj_C hℓ h11 (hConj_unconditional hℓ)

theorem HG_unconditional (hℓ : 5 ≤ ℓ) : DBound.HG ℓ hℓ := VLayer.HG_holds hℓ

theorem DB_unconditional (hℓ : 5 ≤ ℓ) (h11 : 11 ≤ ℓ) : DB ℓ hℓ :=
  (FiniteArithmetic.SmallThreshold.ub_db hℓ h11).2

end RamanujanTau.Discharge.AtkinInputs

#print axioms RamanujanTau.Discharge.AtkinInputs.prodDelta_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.ordEBound_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.quotEBound_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.quotValBound_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.quotBound_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.ordBound_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.hConj_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.UB_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.HQ_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.HG_unconditional
#print axioms RamanujanTau.Discharge.AtkinInputs.DB_unconditional
