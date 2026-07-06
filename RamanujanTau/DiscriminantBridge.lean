/-
# Bridge: the modular discriminant's q-expansion — leading coefficients

Toward `qExpansion(Δ).coeff n = τ(n)` (connecting Mathlib's analytic `ModularForm.discriminant = η²⁴` to the
combinatorial `∏(1−qⁿ)²⁴`). This file proves the two leading coefficients directly from the analytic product:

  * **`coeff_zero_discriminant`**: `qExpansion(Δ).coeff 0 = 0` — `Δ` is a cusp form.
  * **`coeff_one_discriminant`**: `qExpansion(Δ).coeff 1 = 1` (`τ(1) = 1`) — the leading Taylor coefficient
    of `Δ`'s cusp function `q ↦ q · ∏'(1 − qⁿ⁺¹)²⁴`, obtained by identifying the cusp function on the unit
    disc (via `discriminant_eq_q_prod`) and differentiating at `0`.

`coeff 1 = 1` is the normalization that pins the linear relations in `M₁₂` (e.g. `E₄³ = E₁₂ + (432000/691)·Δ`
and `E₄³ − E₆² = 1728·Δ`), which then make *every* `Δ`-coefficient computable from the `E₄`, `E₆` q-expansions
Mathlib provides. The **general** bridge (`coeff n =` the formal `∏(1−qⁿ)²⁴` coefficient for all `n`) still
needs the full analytic-product ↔ formal-power-series expansion — an unformalized TODO in Mathlib.

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

/-! ### `coeff 1 = 1` (the leading Taylor coefficient) -/

open Complex Filter Metric Function Periodic Set
open scoped Real Topology

local notation "𝕢" => Periodic.qParam

/-- The analytic product `G(q) = ∏'(1 − qⁿ⁺¹)²⁴`. -/
noncomputable def Gprod (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

lemma Gprod_zero : Gprod 0 = 1 := by
  rw [Gprod, show (fun n : ℕ => (1 - (0 : ℂ) ^ (n + 1)) ^ 24) = fun _ => 1 from ?_, tprod_one]
  funext n; rw [zero_pow n.succ_ne_zero, sub_zero, one_pow]

lemma differentiableAt_Gprod_zero : DifferentiableAt ℂ Gprod 0 :=
  ((ModularForm.differentiableOn_tprod_one_sub_pow_pow 24).differentiableAt
    (Metric.ball_mem_nhds 0 one_pos))

lemma coe_Δmod : (Δmod : ℍ → ℂ) = ModularForm.discriminant := rfl

/-- The cusp function of `Δ` is `q ↦ q · G(q)` on the open unit disc. -/
lemma cuspFunction_Δmod_eq {q : ℂ} (hq : ‖q‖ < 1) :
    cuspFunction 1 Δmod q = q * Gprod q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [zero_mul, cuspFunction_apply_zero one_pos
        (ModularFormClass.analyticAt_cuspFunction_zero Δmod one_pos one_mem_strictPeriods_SL)
        (SlashInvariantFormClass.periodic_comp_ofComplex Δmod one_mem_strictPeriods_SL)]
    have := coeff_zero_discriminant
    rwa [qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero Δmod one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex Δmod one_mem_strictPeriods_SL)] at this
  · have him : 0 < (invQParam 1 q).im := im_invQParam_pos_of_norm_lt_one one_pos hq hq0
    have hqz : 𝕢 1 (invQParam 1 q) = q := qParam_right_inv one_ne_zero hq0
    have hcoe : ((⟨invQParam 1 q, him⟩ : ℍ) : ℂ) = invQParam 1 q := rfl
    have hprod : (∏' n, (1 - ModularForm.eta_q n ((⟨invQParam 1 q, him⟩ : ℍ) : ℂ)) ^ 24) = Gprod q := by
      rw [Gprod]
      refine tprod_congr (fun n => ?_)
      rw [ModularForm.eta_q, hcoe, hqz]
    rw [UpperHalfPlane.cuspFunction, cuspFunction_eq_of_nonzero _ _ hq0, comp_apply,
        ofComplex_apply_of_im_pos him, coe_Δmod,
        ModularForm.discriminant_eq_q_prod ⟨invQParam 1 q, him⟩, hprod, hcoe, hqz]

/-- **The `q¹` coefficient of `Δ`'s q-expansion is `1`** (`τ(1) = 1`). -/
lemma coeff_one_discriminant : (qExpansion 1 Δmod).coeff 1 = 1 := by
  rw [qExpansion_coeff, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedDeriv_one]
  have heqon : EqOn (cuspFunction 1 Δmod) (fun q => q * Gprod q) (ball 0 1) :=
    fun q hq => cuspFunction_Δmod_eq (mem_ball_zero_iff.mp hq)
  have hev : cuspFunction 1 Δmod =ᶠ[𝓝 0] (fun q => q * Gprod q) :=
    heqon.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 one_pos)
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun q : ℂ => q * Gprod q) (Gprod 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul differentiableAt_Gprod_zero.hasDerivAt
  rw [hd.deriv, Gprod_zero]

end RamanujanTau.DiscriminantBridge
