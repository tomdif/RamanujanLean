import RamanujanTau.DBound.HW
import RamanujanTau.AtkinOBrienFinal.Main

/-!
# The final theorem with (DB) discharged

`atkin_obrien_ℓ'`: the Atkin–O'Brien-type congruences for `ℓ ∈ {13, 17, 19, 23}` from
(UB) (`I1`, U-part), `HQ` (I2), `HV` (I3) and `HG` (I1, `G = E/V(E)` part), via
`DBound.DB_of_UB_I2_I3`.
-/

set_option autoImplicit false

namespace DBound
open AtkinOBrienFinal

theorem atkin_obrien_13' (hUB : UB 13 (by norm_num)) (hQ : HQ 13 (by norm_num))
    (hV : HV 13 (by norm_num)) (hG : HG 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13 hUB (DB_of_UB_I2_I3 _ hUB hQ hV hG)

theorem atkin_obrien_17' (hUB : UB 17 (by norm_num)) (hQ : HQ 17 (by norm_num))
    (hV : HV 17 (by norm_num)) (hG : HG 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17 hUB (DB_of_UB_I2_I3 _ hUB hQ hV hG)

theorem atkin_obrien_19' (hUB : UB 19 (by norm_num)) (hQ : HQ 19 (by norm_num))
    (hV : HV 19 (by norm_num)) (hG : HG 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19 hUB (DB_of_UB_I2_I3 _ hUB hQ hV hG)

theorem atkin_obrien_23' (hUB : UB 23 (by norm_num)) (hQ : HQ 23 (by norm_num))
    (hV : HV 23 (by norm_num)) (hG : HG 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23 hUB (DB_of_UB_I2_I3 _ hUB hQ hV hG)

end DBound
