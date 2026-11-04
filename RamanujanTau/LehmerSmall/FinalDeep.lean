import RamanujanTau.LehmerSmall.QuasiLin

/-! # `τ(n) ≠ 0` for all `1 ≤ n < 21 492 863 999`

A prime zero `p` of `τ` satisfies `p ≡ −1` modulo `691` (`prime_zero_conditions`) and modulo `2⁹, 3⁵, 5³`
(`prime_zero_deep`, from quasimodular integrality). It also satisfies `p ≡ 3, 5, 6 (mod 7)`. So
`p ≡ −1 (mod 10 746 432 000 = 2⁹·3⁵·5³·691)`. Below `21 492 863 999 = 2·10746432000 − 1` the only number
of this form is `10 746 431 999`, which is `≡ 2 (mod 7)`. `21 492 863 999` is prime and `≡ 5 (mod 7)`: it is
the first candidate the congruences cannot exclude. (Lehmer 1947: `214 928 639 999 = 2¹¹·3⁵·5⁴·691 − 1`.)
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open RamanujanTau

theorem no_candidate_below_21492863999 {p : ℕ} (hpN : p < 21492863999) (c691 : p % 691 = 690)
    (c512 : p % 512 = 511) (c243 : p % 243 = 242) (c125 : p % 125 = 124)
    (c7 : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) : False := by
  have d1 : 691 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c691])
  have d2 : 512 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c512])
  have d3 : 243 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c243])
  have d4 : 125 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c125])
  have e12 : 691 * 512 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have e123 : 691 * 512 * 243 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e12 d3
  have hM : 691 * 512 * 243 * 125 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e123 d4
  obtain ⟨k, hk⟩ := hM
  rw [show 691 * 512 * 243 * 125 = 10746432000 by norm_num] at hk
  clear c691 c512 c243 c125 d1 d2 d3 d4 e12 e123
  have hk1 : k = 1 := by omega
  subst hk1
  have hp : p = 10746431999 := by omega
  subst hp
  norm_num at c7

/-- **`τ(n) ≠ 0` for `1 ≤ n < 21 492 863 999`** (kernel-checked, axiom-clean). -/
theorem lehmer_below_21492863999 : ∀ n, 1 ≤ n → n < 21492863999 → τ n ≠ 0 := by
  apply tau_ne_zero_of_primes_below
  intro p hp hpN h
  obtain ⟨c691, -, -, -, c7⟩ := prime_zero_conditions hp h
  obtain ⟨c512, c243, c125⟩ := prime_zero_deep hp h
  exact no_candidate_below_21492863999 hpN c691 c512 c243 c125 c7

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.lehmer_below_21492863999
