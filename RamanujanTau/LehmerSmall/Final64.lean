import RamanujanTau.LehmerSmall.TwoAdic64

/-! # `τ(n) ≠ 0` for all `1 ≤ n < 258 710 399`

A prime zero `p` of `τ` satisfies `p ≡ −1` modulo `691, 25, 9` (`prime_zero_conditions`), `p ≡ −1 (mod 64)`
(`prime_zero_mod64`), and `p ≡ 3, 5, 6 (mod 7)`. So `p ≡ −1 (mod 9 950 400 = 691·25·9·64)`. The 25 numbers
`9950400 k − 1` with `1 ≤ k ≤ 25` are composite or fail the mod-7 condition, and
`258 710 399 = 26·9950400 − 1` is prime and `≡ 3 (mod 7)`: it is the first surviving candidate.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open RamanujanTau

theorem no_candidate_below_258710399 {p : ℕ} (hp : p.Prime) (hpN : p < 258710399) (c691 : p % 691 = 690)
    (c25 : p % 25 = 24) (c9 : p % 9 = 8) (c64 : p % 64 = 63) (c7 : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    False := by
  have d1 : 691 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c691])
  have d2 : 25 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c25])
  have d3 : 9 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c9])
  have d4 : 64 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c64])
  have e12 : 691 * 25 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have e123 : 691 * 25 * 9 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e12 d3
  have hM : 691 * 25 * 9 * 64 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e123 d4
  obtain ⟨k, hk⟩ := hM
  clear c691 c25 c9 c64 d1 d2 d3 d4 e12 e123
  have hk1 : 1 ≤ k := by rcases k with _ | k <;> omega
  have hk25 : k ≤ 25 := by omega
  obtain rfl : p = 9950400 * k - 1 := by omega
  clear hk hpN
  interval_cases k <;> first | (norm_num at c7; done) | (norm_num at hp)

/-- **`τ(n) ≠ 0` for `1 ≤ n < 258 710 399`** (kernel-checked, axiom-clean). -/
theorem lehmer_below_258710399 : ∀ n, 1 ≤ n → n < 258710399 → τ n ≠ 0 := by
  apply tau_ne_zero_of_primes_below
  intro p hp hpN h
  obtain ⟨c691, c25, c9, -, c7⟩ := prime_zero_conditions hp h
  exact no_candidate_below_258710399 hp hpN c691 c25 c9 (prime_zero_mod64 hp h) c7

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.lehmer_below_258710399
