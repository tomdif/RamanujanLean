import RamanujanTau.UBSharp.Main
import RamanujanTau.UBSharp.HConj
import RamanujanTau.UBSharp.Velu

/-!
# The final theorem on pointwise hypotheses only

Over `ℂ_ℓ` (`SharpHQ.φC ℓ`):
* `UB_of_quot_C : QuotBound → UB`, `UB_of_E_C : QuotEBound → UB`;
* **`atkin_obrien_ℓ_conj (hQ : QuotBound) (hConj : HConj)`** for `ℓ ∈ {13, 17, 19, 23}`: both hypotheses
  are pointwise algebraicity-and-valuation statements at test curves of the break region (no `GeomU`,
  no `QuotHyp`, no overconvergence);
* `atkin_obrien_ℓ_quot (hQ : QuotBound)`, since `HConj_of_quotBound : QuotBound → HConj`;
* **`atkin_obrien_ℓ_velu (hE : QuotEBound)`**: the single hypothesis is a valuation statement on the
  Vélu quotients `veluC C` of the short model (`QuotValBound` + Hasse/integrality bounds of the same
  objects); algebraicity is proved (`HeckeBridge.classical_hU_short` + `TateAdd.tateKernels`), and
  `HConj` comes from `ConjAlg.HConj_C_of_val'`.
-/

set_option autoImplicit false

namespace UBSharp
open AtkinOBrienFinal SharpHQ Classical

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

lemma φC_le_one (x : ℤ_[ℓ]) : ‖φC ℓ x‖ ≤ 1 := (norm_φC x).trans_le (PadicInt.norm_le_one x)

lemma ell_C_pos : 0 < ‖((ℓ : ℕ) : ℂ_[ℓ])‖ := by
  rw [norm_ell_C]; exact inv_pos.mpr (by exact_mod_cast hℓp.out.pos)

lemma ell_C_lt_one : ‖((ℓ : ℕ) : ℂ_[ℓ])‖ < 1 := by
  rw [norm_ell_C]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓp.out.one_lt)

/-- **(UB) over `ℂ_ℓ` from `QuotBound`.** -/
theorem UB_of_quot_C (hℓ : 5 ≤ ℓ) (hQ : QuotBound ℓ hℓ (φC ℓ)) : UB ℓ hℓ :=
  UB_of_quot hℓ (φC ℓ) φC_le_one ell_C_pos ell_C_lt_one hQ

/-- `HConj` over `ℂ_ℓ` from `QuotBound`. -/
theorem HConj_of_quot_C (hℓ : 5 ≤ ℓ) (hQ : QuotBound ℓ hℓ (φC ℓ)) : HConj ℓ hℓ (φC ℓ) :=
  HConj_of_quotBound hℓ (φC ℓ) φC_le_one ell_C_pos hQ

/-- **(UB) over `ℂ_ℓ` from the Vélu-quotient bound `QuotEBound`.** -/
theorem UB_of_E_C (hℓ : 5 ≤ ℓ) (hE : QuotEBound ℓ hℓ (φC ℓ)) : UB ℓ hℓ :=
  UB_of_quot_C hℓ (quotBound_of_E_C hℓ hE)

/-- **The final theorem for `ℓ = 13`** on the pointwise hypotheses `QuotBound` and `HConj`. -/
theorem atkin_obrien_13_conj (hQ : QuotBound 13 (by norm_num) (φC 13))
    (hConj : HConj 13 (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13'''' (UB_of_quot_C _ hQ) hConj

/-- The final theorem for `ℓ = 13` on `QuotBound` alone. -/
theorem atkin_obrien_13_quot (hQ : QuotBound 13 (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13_conj hQ (HConj_of_quot_C _ hQ)

/-- **The final theorem for `ℓ = 13`** on the single Vélu-quotient bound `QuotEBound`. -/
theorem atkin_obrien_13_velu (hE : QuotEBound 13 (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13_conj (quotBound_of_E_C _ hE)
    (ConjAlg.HConj_C_of_val' (by norm_num) (hE.toQuotValBound _))

/-- **The final theorem for `ℓ = 17`** on the pointwise hypotheses `QuotBound` and `HConj`. -/
theorem atkin_obrien_17_conj (hQ : QuotBound 17 (by norm_num) (φC 17))
    (hConj : HConj 17 (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17'''' (UB_of_quot_C _ hQ) hConj

/-- The final theorem for `ℓ = 17` on `QuotBound` alone. -/
theorem atkin_obrien_17_quot (hQ : QuotBound 17 (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17_conj hQ (HConj_of_quot_C _ hQ)

/-- **The final theorem for `ℓ = 17`** on the single Vélu-quotient bound `QuotEBound`. -/
theorem atkin_obrien_17_velu (hE : QuotEBound 17 (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17_conj (quotBound_of_E_C _ hE)
    (ConjAlg.HConj_C_of_val' (by norm_num) (hE.toQuotValBound _))

/-- **The final theorem for `ℓ = 19`** on the pointwise hypotheses `QuotBound` and `HConj`. -/
theorem atkin_obrien_19_conj (hQ : QuotBound 19 (by norm_num) (φC 19))
    (hConj : HConj 19 (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19'''' (UB_of_quot_C _ hQ) hConj

/-- The final theorem for `ℓ = 19` on `QuotBound` alone. -/
theorem atkin_obrien_19_quot (hQ : QuotBound 19 (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19_conj hQ (HConj_of_quot_C _ hQ)

/-- **The final theorem for `ℓ = 19`** on the single Vélu-quotient bound `QuotEBound`. -/
theorem atkin_obrien_19_velu (hE : QuotEBound 19 (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19_conj (quotBound_of_E_C _ hE)
    (ConjAlg.HConj_C_of_val' (by norm_num) (hE.toQuotValBound _))

/-- **The final theorem for `ℓ = 23`** on the pointwise hypotheses `QuotBound` and `HConj`. -/
theorem atkin_obrien_23_conj (hQ : QuotBound 23 (by norm_num) (φC 23))
    (hConj : HConj 23 (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23'''' (UB_of_quot_C _ hQ) hConj

/-- The final theorem for `ℓ = 23` on `QuotBound` alone. -/
theorem atkin_obrien_23_quot (hQ : QuotBound 23 (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23_conj hQ (HConj_of_quot_C _ hQ)

/-- **The final theorem for `ℓ = 23`** on the single Vélu-quotient bound `QuotEBound`. -/
theorem atkin_obrien_23_velu (hE : QuotEBound 23 (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23_conj (quotBound_of_E_C _ hE)
    (ConjAlg.HConj_C_of_val' (by norm_num) (hE.toQuotValBound _))

end UBSharp

