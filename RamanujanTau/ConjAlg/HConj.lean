import RamanujanTau.ConjAlg.Conj

/-!
# `HConj` from the valuation bounds alone (modulo `hKer`)

With algebraicity proved (`ConjAlg.algebraicity_conj`), `SharpHQ.HConj` reduces to an intrinsic
statement about the Vélu quotients of the short model `Wₛ = short (−c₄/48) (−c₆/864)` of a test
curve `W` in the break region:

**`QuotValBound ℓ hℓ φ`**: for every test curve `W` with `‖ℓ‖^ℓ < ‖E(W)‖^{ℓ+1}` there is an order-`ℓ`
subgroup `H` of `Wₛ` (the canonical one) with
* `‖Δ(Wₛ/H)‖ · ‖E(W)‖^{12} ≤ ‖ℓ‖^{12}`,
* `‖Δ(Wₛ/C)‖^ℓ ≤ ‖E(W)‖^{12}` for every other order-`ℓ` subgroup `C`.

* **`HConj_of_val`**: `hKer → QuotValBound → HConj ℓ hℓ (ψ ∘ ιz)`.
* **`HConj_C_of_val`**: the same over `ℂ_ℓ` with `φ = SharpHQ.φC ℓ`, the hypothesis of
  `SharpHQ.atkin_obrien_13⁗` etc.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConjAlg
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal DBound HeckeBridge SubgroupSum Velu

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [IsAlgClosed K]
  [DecidableEq K]

variable (ℓ) in
/-- **The valuation half of `HConj`**, intrinsic to the order-`ℓ` subgroups of the short model. -/
def QuotValBound (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ W : WeierstrassCurve K, KatzForms.IsTest W → UpContraction.Brk ℓ (KatzForms.Eh φ hℓ) W →
    ∃ H ∈ subs (sa W) (sb W) ℓ,
      ‖(veluC H).Δ‖ * ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
      ∀ C ∈ subs (sa W) (sb W) ℓ, C ≠ H →
        ‖(veluC C).Δ‖ ^ ℓ ≤ ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12

/-- **`HConj` from the valuation bounds** (modulo `hKer`). -/
theorem HConj_of_val (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (hV : QuotValBound ℓ hℓ (ψ.comp (ιz ℓ))) : SharpHQ.HConj ℓ hℓ (ψ.comp (ιz ℓ)) := by
  intro f hf hJ W hW hBr
  obtain ⟨H, hH, hH1, hH2⟩ := hV W hW hBr
  obtain ⟨G, hmem, hinj, -, h0, hk⟩ := algebraicity_conj hℓ ψ hζK ι hι hKer f hf hJ W hW hH
  refine ⟨_, hk, ?_, fun j => ?_⟩
  · simpa [h0] using hH1
  · refine hH2 _ (hmem _) ?_
    rw [← h0]
    exact fun h => Fin.succ_ne_zero j (hinj h)

/-- **`HConj (φC ℓ)` from the valuation bounds over `ℂ_ℓ`** (modulo `hKer`). -/
theorem HConj_C_of_val [DecidableEq ℂ_[ℓ]] {ζK : ℂ_[ℓ]} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries ℂ_[ℓ] →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (hV : QuotValBound ℓ hℓ (SharpHQ.φC ℓ)) : SharpHQ.HConj ℓ hℓ (SharpHQ.φC ℓ) :=
  HConj_of_val hℓ (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hζK ι hι hKer hV

end ConjAlg

#print axioms ConjAlg.map_heckePoly
#print axioms ConjAlg.f_zero
#print axioms ConjAlg.newton_poly
#print axioms ConjAlg.eq_esymm_of_newton
#print axioms ConjAlg.eval_Pdisc
#print axioms ConjAlg.algebraicity_short
#print axioms ConjAlg.shortModel_ptR
#print axioms ConjAlg.algebraicity_general
#print axioms ConjAlg.algebraicity_conj
#print axioms ConjAlg.conj_first
#print axioms ConjAlg.algebraicity_conj_C
#print axioms ConjAlg.HConj_of_val
#print axioms ConjAlg.HConj_C_of_val
