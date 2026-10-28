/-
# Atkin–O'Brien for l in {13,17,19,23}: current main theorem

There is kappa in Z_l with l^m dividing p((l^{m+2}n+1)/24) - kappa*p((l^m n+1)/24) for all m >= 1. It is
proved from two explicit hypotheses:
* `UB l`: the U_l column bounds on Katz expansions (`AtkinOBrienFinal.UB`);
* `QuotValBound l`: valuation bounds on the l+1 Velu quotients of every break-region test curve over C_l
  (`ConjAlg.QuotValBound`).
-/
import RamanujanTau.SharpHQ.Final
import RamanujanTau.ConjAlg.NoKer

set_option autoImplicit false

namespace AtkinOBrienMain
open AtkinOBrienFinal SharpHQ Classical

theorem atkin_obrien_13 (hUB : UB 13 (by norm_num)) (hV : ConjAlg.QuotValBound 13 (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13'''' hUB (ConjAlg.HConj_C_of_val' (by norm_num) hV)

theorem atkin_obrien_17 (hUB : UB 17 (by norm_num)) (hV : ConjAlg.QuotValBound 17 (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17'''' hUB (ConjAlg.HConj_C_of_val' (by norm_num) hV)

theorem atkin_obrien_19 (hUB : UB 19 (by norm_num)) (hV : ConjAlg.QuotValBound 19 (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19'''' hUB (ConjAlg.HConj_C_of_val' (by norm_num) hV)

theorem atkin_obrien_23 (hUB : UB 23 (by norm_num)) (hV : ConjAlg.QuotValBound 23 (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23'''' hUB (ConjAlg.HConj_C_of_val' (by norm_num) hV)

end AtkinOBrienMain
