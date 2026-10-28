/-
# Main theorem on UB + OrdBound

`AllQuotients.quotValBound_C` proves `QuotValBound` on the supersingular part of the break region outright.
On the ordinary locus ‖E(W)‖ = 1 it is reduced to `AllQuotients.OrdBound`.
-/
import RamanujanTau.AtkinOBrienMain.Main
import RamanujanTau.AllQuotients.Final

set_option autoImplicit false

namespace AtkinOBrienMain
open AtkinOBrienFinal SharpHQ Classical

theorem atkin_obrien_13_ord (hUB : UB 13 (by norm_num)) (hord : AllQuotients.OrdBound (ℓ := 13) (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13 hUB (AllQuotients.quotValBound_C (by norm_num) hord)

theorem atkin_obrien_17_ord (hUB : UB 17 (by norm_num)) (hord : AllQuotients.OrdBound (ℓ := 17) (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17 hUB (AllQuotients.quotValBound_C (by norm_num) hord)

theorem atkin_obrien_19_ord (hUB : UB 19 (by norm_num)) (hord : AllQuotients.OrdBound (ℓ := 19) (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19 hUB (AllQuotients.quotValBound_C (by norm_num) hord)

theorem atkin_obrien_23_ord (hUB : UB 23 (by norm_num)) (hord : AllQuotients.OrdBound (ℓ := 23) (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23 hUB (AllQuotients.quotValBound_C (by norm_num) hord)

end AtkinOBrienMain
