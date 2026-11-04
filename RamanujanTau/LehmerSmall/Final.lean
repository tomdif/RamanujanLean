import RamanujanTau.LehmerSmall.PrimePower
import RamanujanTau.LehmerSmall.Refined
import RamanujanTau.TauModular
import Mathlib.Tactic.NormNum.Prime

/-! # Lehmer's method: `τ(n) ≠ 0` for all `1 ≤ n < 74 627 999`

By `exists_prime_dvd_tau_eq_zero` a zero of `τ` below `N` gives a prime zero `p < N`. A prime with
`τ(p) = 0` satisfies (`prime_zero_conditions`)
* `p ≡ −1 (mod 691)`  (`τ(p) ≡ 1 + p¹¹`, Ramanujan; `x ↦ x¹¹` is injective on `𝔽₆₉₁`),
* `p ≡ −1 (mod 25)`   (`τ(p) ≡ p(1 + p⁹)`),
* `p ≡ −1 (mod 9)`    (`tau_mod9_all`),
* `p ≡ −1 (mod 32)`   (`two_adic_of_tau_eq_zero`),
* `p ≡ 3, 5, 6 (mod 7)` (`τ(p) ≡ p(1 + p³)`),
the small primes `2, 3, 5, 7` being excluded by their (nonzero) values. Hence `p ≡ −1 (mod 4 975 200)`, and
the fourteen numbers `4975200 j − 1`, `1 ≤ j ≤ 14`, below `74 627 999` are composite or fail the mod-7
condition; `74 627 999` itself is the first candidate.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open RamanujanTau
open scoped ArithmeticFunction.sigma

lemma sigma_prime_cast {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (σ k p : R) = 1 + (p : R) ^ k := by
  have h := ArithmeticFunction.sigma_apply_prime_pow (k := k) (i := 1) hp
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]; push_cast; ring

lemma d691 : ∀ x : ZMod 691, 1 + x ^ 11 = 0 → x = -1 := by decide +kernel
lemma d25 : ∀ x : ZMod 25, x * (1 + x ^ 9) = 0 → x = 0 ∨ x = -1 := by decide +kernel
lemma d7 : ∀ x : ZMod 7, x * (1 + x ^ 3) = 0 → x.val = 0 ∨ x.val = 3 ∨ x.val = 5 ∨ x.val = 6 := by
  decide +kernel
lemma d9 : ∀ x : ZMod 9, 256 * 0 = 160 * (1 + x ^ 7) + 176 * (1 + x ^ 9) - 320 * x ^ 2 * (1 + x ^ 7) +
    2 * ((1 + x) + 5 * (1 + x ^ 3) - 6 * x * (1 + x)) + 6 * (1 + x) → x.val = 3 ∨ x.val = 8 := by
  decide +kernel
lemma d4096 : ∀ x : ZMod 4096,
    691 * (1440 * (1 + x ^ 7) - 720 * (1 + x ^ 3)) - 65520 * (1 + x ^ 11) = 0 →
      x.val % 2 = 0 ∨ x.val % 32 = 31 := by decide +kernel

lemma prime_eq_of_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : q ∣ p) : p = q :=
  ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm

/-- **Congruence conditions on a prime zero of `τ`.** -/
theorem prime_zero_conditions {p : ℕ} (hp : p.Prime) (h : τ p = 0) :
    p % 691 = 690 ∧ p % 25 = 24 ∧ p % 9 = 8 ∧ p % 32 = 31 ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := by
  have ht : TauCong.tauPS p = 0 := by rw [← tau_eq_tauPS]; exact h
  have hp0 := hp.ne_zero
  have h2 : p ≠ 2 := by rintro rfl; rw [tau_two] at h; norm_num at h
  have h3 : p ≠ 3 := by rintro rfl; rw [tau_three] at h; norm_num at h
  have h5 : p ≠ 5 := by rintro rfl; rw [tau_five] at h; norm_num at h
  have h7 : p ≠ 7 := by rintro rfl; rw [tau_seven] at h; norm_num at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := TauModular.tau_prime_mod691 hp
    rw [ht, Int.cast_zero] at this
    have hx := d691 (p : ZMod 691) (by simpa using this.symm)
    have := congrArg ZMod.val hx
    rw [ZMod.val_natCast] at this; rw [this]; rfl
  · have := tau_mod25_all hp0
    rw [ht, Int.cast_zero, sigma_prime_cast hp] at this
    rcases d25 (p : ZMod 25) (by simpa using this.symm) with hx | hx
    · exfalso
      have := (ZMod.natCast_eq_zero_iff p 25).mp hx
      exact h5 (prime_eq_of_dvd hp Nat.prime_five (dvd_trans (by norm_num) this))
    · have := congrArg ZMod.val hx
      rw [ZMod.val_natCast] at this; rw [this]; rfl
  · have := tau_mod9_all hp0
    rw [ht, Int.cast_zero, sigma_prime_cast hp, sigma_prime_cast hp, sigma_prime_cast hp,
      sigma_prime_cast hp] at this
    rcases d9 (p : ZMod 9) (by simpa using this) with hx | hx
    · exfalso; rw [ZMod.val_natCast] at hx
      exact h3 (prime_eq_of_dvd hp Nat.prime_three (by omega))
    · rw [ZMod.val_natCast] at hx; exact hx
  · have := two_adic_of_tau_eq_zero hp0 ht
    rw [sigma_prime_cast hp, sigma_prime_cast hp, sigma_prime_cast hp] at this
    rcases d4096 (p : ZMod 4096) (by simpa using this) with hx | hx
    · exfalso; rw [ZMod.val_natCast] at hx
      exact h2 (prime_eq_of_dvd hp Nat.prime_two (by omega))
    · rw [ZMod.val_natCast] at hx; omega
  · have := tau_mod7_all hp0
    rw [ht, Int.cast_zero, sigma_prime_cast hp] at this
    rcases d7 (p : ZMod 7) (by simpa using this.symm) with hx | hx | hx | hx <;> rw [ZMod.val_natCast] at hx
    · exact absurd (prime_eq_of_dvd hp (by norm_num) (by omega)) h7
    · left; exact hx
    · right; left; exact hx
    · right; right; exact hx

/-- The arithmetic sieve: no prime `p < 74 627 999` satisfies the five congruence conditions. -/
theorem no_candidate_below {p : ℕ} (hp : p.Prime) (hpN : p < 74627999) (c691 : p % 691 = 690) (c25 : p % 25 = 24)
    (c9 : p % 9 = 8) (c32 : p % 32 = 31) (c7 : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) : False := by
  have d1 : 691 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c691])
  have d2 : 25 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c25])
  have d3 : 9 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c9])
  have d4 : 32 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c32])
  have e12 : 691 * 25 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have e123 : 691 * 25 * 9 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e12 d3
  have hM : 691 * 25 * 9 * 32 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e123 d4
  obtain ⟨k, hk⟩ := hM
  clear c691 c25 c9 c32 d1 d2 d3 d4 e12 e123
  have hk1 : 1 ≤ k := by rcases k with _ | k <;> omega
  have hk14 : k ≤ 14 := by omega
  obtain rfl : p = 4975200 * k - 1 := by omega
  clear hk hpN
  interval_cases k <;> first | (norm_num at c7; done) | (norm_num at hp)

/-- **Lehmer's theorem, small range (kernel-checked, axiom-clean):** `τ(n) ≠ 0` for `1 ≤ n < 74 627 999`. -/
theorem lehmer_below_74627999 : ∀ n, 1 ≤ n → n < 74627999 → τ n ≠ 0 := by
  apply tau_ne_zero_of_primes_below
  intro p hp hpN h
  obtain ⟨c691, c25, c9, c32, c7⟩ := prime_zero_conditions hp h
  exact no_candidate_below hp hpN c691 c25 c9 c32 c7

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.prime_zero_conditions
#print axioms RamanujanTau.LehmerSmall.lehmer_below_74627999
