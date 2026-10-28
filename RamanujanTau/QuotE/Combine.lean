/-
# `QuotEBound` from its ordinary half

* `QuotE.Concl hℓ φ W`: the conclusion of `UBSharp.QuotEBound` at `W` (so `QuotEBound` is
  `∀ W, IsTest W → Brk → Concl`, `quotEBound_iff`).
* `QuotE.OrdEBound hℓ φ`: `Concl` at every break-region test curve with `‖E(W)‖ = 1` (the ordinary
  locus; not proved here).
* **`quotEBound_of_ord`**, **`quotEBound_C_of_ord`**: `OrdEBound → QuotEBound`, the supersingular
  part being `QuotE.quotEBound_ss`.
* **`atkin_obrien_ℓ_ordE (hord : OrdEBound)`** for `ℓ ∈ {13, 17, 19, 23}`.
-/
import RamanujanTau.QuotE.Main
import RamanujanTau.UBSharp.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotE
open KatzForms MvPolynomial

section Gen
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [DecidableEq K]
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- the conclusion of `UBSharp.QuotEBound` at a curve `W`. -/
def Concl (φ : ℤ_[ℓ] →+* K) (W : WeierstrassCurve K) : Prop :=
  ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      (‖(SubgroupSum.veluC H).Δ‖ * ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
        ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
          ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤ ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12) ∧
      ‖eval (KatzForms.pt (SubgroupSum.veluC H)) (KatzForms.Eh φ hℓ)‖ *
          ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) * ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖eval (KatzForms.pt (SubgroupSum.veluC C)) (KatzForms.Eh φ hℓ)‖ ≤
          ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖) ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₄‖ ^ 3 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ ∧
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₆‖ ^ 2 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖

lemma quotEBound_iff (φ : ℤ_[ℓ] →+* K) :
    UBSharp.QuotEBound ℓ hℓ φ ↔
      ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W → Concl hℓ φ W :=
  Iff.rfl

/-- the ordinary half of `QuotEBound` (`‖E(W)‖ = 1`; not proved here). -/
def OrdEBound (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
    ‖eval (KatzForms.pt W) (Eh φ hℓ)‖ = 1 → Concl hℓ φ W

end Gen

section Comb
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`QuotEBound` from its ordinary half.** -/
theorem quotEBound_of_ord (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hord : OrdEBound hℓ φ) : UBSharp.QuotEBound ℓ hℓ φ := by
  intro W hW hB
  have hEle : ‖eval (KatzForms.pt W) (Eh φ hℓ)‖ ≤ 1 :=
    (norm_eval_le (integral_pt hW) _).trans (gnorm_le zero_le_one (Eh_integral φ hφ hℓ))
  rcases hEle.lt_or_eq with hlt | heq
  · exact quotEBound_ss hℓ φ hφ hε W hW hB hlt
  · exact hord W hW hB heq

end Comb

section C
open Classical
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`QuotEBound` over `ℂ_ℓ` from its ordinary half.** -/
theorem quotEBound_C_of_ord (hℓ : 5 ≤ ℓ) (hord : OrdEBound hℓ (SharpHQ.φC ℓ)) :
    UBSharp.QuotEBound ℓ hℓ (SharpHQ.φC ℓ) :=
  quotEBound_of_ord hℓ (SharpHQ.φC ℓ) UBSharp.φC_le_one UBSharp.ell_C_pos hord

theorem atkin_obrien_13_ordE (hord : OrdEBound (by norm_num : 5 ≤ 13) (SharpHQ.φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  UBSharp.atkin_obrien_13_velu (quotEBound_C_of_ord _ hord)

theorem atkin_obrien_17_ordE (hord : OrdEBound (by norm_num : 5 ≤ 17) (SharpHQ.φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  UBSharp.atkin_obrien_17_velu (quotEBound_C_of_ord _ hord)

theorem atkin_obrien_19_ordE (hord : OrdEBound (by norm_num : 5 ≤ 19) (SharpHQ.φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  UBSharp.atkin_obrien_19_velu (quotEBound_C_of_ord _ hord)

theorem atkin_obrien_23_ordE (hord : OrdEBound (by norm_num : 5 ≤ 23) (SharpHQ.φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  UBSharp.atkin_obrien_23_velu (quotEBound_C_of_ord _ hord)

end C

end QuotE
