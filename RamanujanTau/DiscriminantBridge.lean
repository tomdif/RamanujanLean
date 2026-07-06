/-
# Bridge: the modular discriminant's q-expansion — leading coefficients

Toward `qExpansion(Δ).coeff n = τ(n)` (connecting Mathlib's analytic `ModularForm.discriminant = η²⁴` to the
combinatorial `∏(1−qⁿ)²⁴`). The *general* bridge is a deep analytic build (expanding the analytic infinite
product `∏'(1−qⁿ)²⁴` into its formal Taylor coefficients — an unformalized TODO in Mathlib). This file
records the reachable leading-coefficient facts:

  * **`coeff_zero_discriminant`**: `qExpansion(Δ).coeff 0 = 0` — `Δ` is a cusp form.

`Δ` here is `CuspForm.discriminant` coerced to `ModularForm 𝒮ℒ 12`.
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

namespace RamanujanTau.DiscriminantBridge

open ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- `Δ` as a weight-12 modular form (coercion of the cusp form `CuspForm.discriminant`). -/
noncomputable def Δmod : ModularForm 𝒮ℒ (12 : ℤ) := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

/-- `Δ` is a cusp form (it *is* the coercion of one). -/
lemma isCuspForm_Δmod : ModularForm.IsCuspForm Δmod :=
  ⟨CuspForm.discriminant, CuspForm.toModularFormₗ_eq_coe _⟩

/-- **The constant term of `Δ`'s q-expansion is `0`** (a cusp form). -/
lemma coeff_zero_discriminant : (qExpansion 1 Δmod).coeff 0 = 0 :=
  (ModularForm.isCuspForm_iff_coeffZero_eq_zero Δmod).mp isCuspForm_Δmod

end RamanujanTau.DiscriminantBridge
