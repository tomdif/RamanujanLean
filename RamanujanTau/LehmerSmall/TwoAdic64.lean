import RamanujanTau.LehmerSmall.Final

/-! # One more 2-adic digit: `τ(p) = 0 ⇒ p ≡ −1 (mod 64)`

In `two_adic_of_tau_eq_zero` the `S₃³` term enters as `13824000·c(n)`, `c(n) = [qⁿ]S₃³`,
`13824000 = 2¹²·3375`. Here we show `c(n)` is **even for `n ≡ 7 (mod 8)`**, so the condition holds
mod `2¹³`; at a prime zero (already `≡ 31 mod 32`) this forces `p ≡ 63 (mod 64)`.

Parity of `c(n)`, in `𝔽₂⟦q⟧` with `A = S₃ mod 2`:
* `σ₃(m)` is even when `m ≡ 3, 5, 6, 7 (mod 8)`: for odd `m` not a square the divisors pair off as
  `d ↔ m/d` (`Finset.sum_involution`), and odd squares are `≡ 1 (mod 8)`; `m ≡ 6` reduces to the odd
  part `≡ 3 (mod 4)` by multiplicativity. So `A` is supported on residues `{0,1,2,4} mod 8`.
* `[qʲ]A² = 0` for `j ≡ 1,3,5,6,7 (mod 8)`: the swap `(k,l) ↦ (l,k)` cancels off-diagonal terms in
  characteristic 2, and the diagonal `j = 2k` has `2k mod 8 ∈ {0,2,4}`.
* `[qⁿ]A³ = Σ a_i [q^{n−i}]A²`, and `i ∈ {0,1,2,4}`, `n ≡ 7` gives `n − i ≡ 7,6,5,3`.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open PowerSeries
open scoped ArithmeticFunction.sigma

/-- For odd non-square `m`, `σ_k(m)` is even. -/
lemma sigma_odd_nonsquare_zmod2 (k : ℕ) {m : ℕ} (hm : m % 2 = 1) (hsq : ∀ d, d * d ≠ m) :
    (σ k m : ZMod 2) = 0 := by
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  have hm0 : m ≠ 0 := by omega
  refine Finset.sum_involution (fun d _ => m / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    obtain ⟨e, he⟩ := hdm
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hq : m / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hd0
    dsimp only
    rw [hq]
    have hdodd : d % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one d with h | h
      · exfalso; have : m % 2 = 0 := by rw [he, Nat.mul_mod, h, zero_mul, Nat.zero_mod]
        omega
      · exact h
    have heodd : e % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one e with h | h
      · exfalso; have : m % 2 = 0 := by rw [he, Nat.mul_mod, h, mul_zero, Nat.zero_mod]
        omega
      · exact h
    have h1 : (d : ZMod 2) = 1 := by
      rw [← Nat.mod_add_div d 2, hdodd]; push_cast
      rw [show (2 : ZMod 2) = 0 by decide]; ring
    have h2 : (e : ZMod 2) = 1 := by
      rw [← Nat.mod_add_div e 2, heodd]; push_cast
      rw [show (2 : ZMod 2) = 0 by decide]; ring
    rw [h1, h2, one_pow]; decide
  · intro d hd _ heq
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hq : m / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hd0
    dsimp only at heq
    rw [hq] at heq
    exact hsq d (by rw [he, heq])
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hm0

lemma odd_sq_mod8 {d m : ℕ} (h : d * d = m) (hm : m % 2 = 1) : m % 8 = 1 := by
  subst h
  have : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · rw [Nat.mul_mod, h] at hm; simp at hm
    · exact h
  have h8 : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by omega
  rw [Nat.mul_mod]; rcases h8 with h | h | h | h <;> rw [h]

/-- `σ_k(m)` is even when `m ≡ 3, 5, 6, 7 (mod 8)`. -/
lemma sigma_zmod2_support (k : ℕ) {m : ℕ} (hm : (σ k m : ZMod 2) ≠ 0) :
    m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 4 := by
  by_contra hc
  apply hm
  have hodd : ∀ m' : ℕ, m' % 2 = 1 → m' % 8 ≠ 1 → (σ k m' : ZMod 2) = 0 := fun m' h1 h2 =>
    sigma_odd_nonsquare_zmod2 k h1 fun d hd => h2 (odd_sq_mod8 hd h1)
  have h8 : m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · exact hodd m (by omega) (by omega)
  · exact hodd m (by omega) (by omega)
  · obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
    have hcop : Nat.Coprime 2 m' := by
      rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (by omega)
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    push_cast
    rw [hodd m' (by omega) (by omega), mul_zero]
  · exact hodd m (by omega) (by omega)

/-- `S₃ mod 2`. -/
noncomputable def A2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) (Sk 3)

lemma coeff_A2 (m : ℕ) : coeff m A2 = (σ 3 m : ZMod 2) := by
  rw [A2, coeff_map, coeff_Sk]; simp

lemma A2_support {m : ℕ} (h : coeff m A2 ≠ 0) : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 4 :=
  sigma_zmod2_support 3 (by rwa [coeff_A2] at h)

lemma A2_sq_zero {j : ℕ} (hj : j % 8 = 1 ∨ j % 8 = 3 ∨ j % 8 = 5 ∨ j % 8 = 6 ∨ j % 8 = 7) :
    coeff j (A2 ^ 2) = 0 := by
  rw [pow_two, coeff_mul]
  refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
  · intro x _
    rw [mul_comm (coeff x.2 A2), ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  · intro x hx hne heq
    rw [Finset.mem_antidiagonal] at hx
    have h12 : x.2 = x.1 := congrArg Prod.fst heq
    have ha : coeff x.1 A2 ≠ 0 := left_ne_zero_of_mul hne
    have := A2_support ha
    omega
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx ⊢; simp only; omega
  · intro x _; rfl

/-- **`[qⁿ]S₃³` is even for `n ≡ 7 (mod 8)`.** -/
theorem S3_cube_even {n : ℕ} (hn : n % 8 = 7) : ((coeff n (Sk 3 ^ 3) : ℤ) : ZMod 2) = 0 := by
  have : ((coeff n (Sk 3 ^ 3) : ℤ) : ZMod 2) = coeff n (A2 ^ 3) := by
    rw [A2, ← map_pow, coeff_map]; simp
  rw [this, pow_succ, mul_comm, coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases ha : coeff x.1 A2 = 0
  · rw [ha, zero_mul]
  · have := A2_support ha
    rw [A2_sq_zero (by omega), mul_zero]

/-- **The 2-adic condition mod `2¹³`** for `n ≡ 7 (mod 8)` with `τ(n) = 0`. -/
theorem two_adic8192_of_tau_eq_zero {n : ℕ} (hn : n ≠ 0) (h8 : n % 8 = 7) (h0 : TauCong.tauPS n = 0) :
    (691 * (1440 * (σ 7 n : ZMod 8192) - 720 * (σ 3 n : ZMod 8192)) - 65520 * (σ 11 n : ZMod 8192)) = 0 := by
  have hc := S3_cube_even h8
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨t, ht⟩ := hc
  have h := tau_E4cube_int hn
  rw [E4_cube, h0] at h
  simp only [map_add, map_sub, coeff_one, if_neg hn, coeff_ofNat_mul', coeff_Sk, ht] at h
  have := congrArg (fun x : ℤ => (x : ZMod 8192)) h
  simp only at this
  push_cast at this
  rw [show (13824000 : ZMod 8192) * (2 * (t : ZMod 8192)) = 0 by
    rw [← mul_assoc, show (13824000 : ZMod 8192) * 2 = 0 by decide, zero_mul]] at this
  linear_combination this

lemma d8192 : ∀ x : ZMod 8192,
    691 * (1440 * (1 + x ^ 7) - 720 * (1 + x ^ 3)) - 65520 * (1 + x ^ 11) = 0 →
      x.val % 2 = 0 ∨ x.val % 64 = 63 := by decide +kernel

/-- **A prime zero of `τ` is `≡ −1 (mod 64)`.** -/
theorem prime_zero_mod64 {p : ℕ} (hp : p.Prime) (h : τ p = 0) : p % 64 = 63 := by
  have ht : TauCong.tauPS p = 0 := by rw [← tau_eq_tauPS]; exact h
  obtain ⟨-, -, -, c32, -⟩ := prime_zero_conditions hp h
  have h2 : p ≠ 2 := by omega
  have := two_adic8192_of_tau_eq_zero hp.ne_zero (by omega) ht
  rw [sigma_prime_cast hp, sigma_prime_cast hp, sigma_prime_cast hp] at this
  rcases d8192 (p : ZMod 8192) (by simpa using this) with hx | hx
  · exfalso; rw [ZMod.val_natCast] at hx
    exact h2 (prime_eq_of_dvd hp Nat.prime_two (by omega))
  · rw [ZMod.val_natCast] at hx; omega

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.S3_cube_even
#print axioms RamanujanTau.LehmerSmall.prime_zero_mod64
