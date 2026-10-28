/-
# Atkin–O'Brien on UB alone

`OrdQuot.ordBound_C` discharges `AllQuotients.OrdBound`, so the main theorem
`AtkinOBrienMain.atkin_obrien_ℓ_ord` holds with the single hypothesis UB, for ℓ ∈ {13, 17, 19, 23}.
-/
import RamanujanTau.AtkinOBrienMain.Ord
import RamanujanTau.OrdQuot.Final

set_option autoImplicit false

namespace OrdQuot
open AtkinOBrienMain AtkinOBrienFinal SharpHQ Classical

theorem atkin_obrien_13_UB (hUB : UB 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13_ord hUB (ordBound_C (by norm_num))

theorem atkin_obrien_17_UB (hUB : UB 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17_ord hUB (ordBound_C (by norm_num))

theorem atkin_obrien_19_UB (hUB : UB 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19_ord hUB (ordBound_C (by norm_num))

theorem atkin_obrien_23_UB (hUB : UB 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23_ord hUB (ordBound_C (by norm_num))

end OrdQuot
