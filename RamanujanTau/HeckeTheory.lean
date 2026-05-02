import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Multiplicativity
import RamanujanTau.HeckeRecurrence
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! # Hecke theory: master identity unifies multiplicativity and recurrence

This module exposes a single hypothesis class `TauHeckeMaster` that packages the
**master Hecke identity** for the action of `T_p` on the q-expansion of a weight-12
eigenform. The deep theorem behind the class is that the space of weight-12 cusp
forms is one-dimensional (spanned by Δ), so Δ is automatically a Hecke eigenform
at every prime, and the eigenvalue of `T_p` on Δ is `τ(p)`. Reading off the q-
expansion of `T_p Δ = τ(p)·Δ` gives the master identity below.

```
For prime p, all n ≥ 1:
    τ(p) · τ(n) = τ(p·n) + p^{11} · τ(n / p)        if p ∣ n
    τ(p) · τ(n) = τ(p·n)                            if p ∤ n
```

From this single identity we derive both:
* `TauHeckeRecurrence` — by setting `n = p^r` (so `p ∣ n` iff `r ≥ 1`).
* `TauMultiplicative`  — by induction on the prime factorization of `m`.

This is the audit point: a downstream Hecke-on-cusp-forms argument discharges
`TauHeckeMaster`, and both `TauMultiplicative` and `TauHeckeRecurrence` follow
mechanically.
-/

namespace RamanujanTau

/-- **Master Hecke identity** for `τ`.

For every prime `p` and every `n ≥ 1`,
`τ(p) · τ(n) = τ(p·n) + p^{11} · τ(n/p)` when `p ∣ n`, else `τ(p)·τ(n) = τ(p·n)`.

The conditional second term encodes the convention `τ(n/p) := 0` whenever
`p ∤ n`. -/
class TauHeckeMaster : Prop where
  master : ∀ {p : ℕ}, p.Prime → ∀ n : ℕ, n ≥ 1 →
    τ p * τ n = τ (p * n) + (if p ∣ n then (p : ℤ)^11 * τ (n / p) else 0)

/-! ## Numerical sanity for the master identity

These checks evaluate the master identity at small `(p, n)` pairs and verify
it matches the computed values of `τ`. They are instances of the identity, not
a proof. -/

theorem master_check_p2_n1 : τ 2 * τ 1 = τ 2 + 0 := by
  rw [tau_two, tau_one]; norm_num

theorem master_check_p2_n2 : τ 2 * τ 2 = τ 4 + (2 : ℤ)^11 * τ 1 := by
  rw [tau_two, tau_four, tau_one]; norm_num

theorem master_check_p2_n3 : τ 2 * τ 3 = τ 6 + 0 := by
  rw [tau_two, tau_three, tau_six]; norm_num

theorem master_check_p2_n4 : τ 2 * τ 4 = τ 8 + (2 : ℤ)^11 * τ 2 := by
  rw [tau_two, tau_four, tau_eight]; norm_num

theorem master_check_p3_n2 : τ 3 * τ 2 = τ 6 + 0 := by
  rw [tau_three, tau_two, tau_six]; norm_num

theorem master_check_p3_n3 : τ 3 * τ 3 = τ 9 + (3 : ℤ)^11 * τ 1 := by
  rw [tau_three, tau_nine, tau_one]; norm_num

/-! ## Derivation 1: master ⇒ Hecke recurrence

Set `n = p^r` with `r ≥ 1`. Since `p ∣ p^r` and `p^r / p = p^{r-1}`, the
master identity reads
`τ(p) · τ(p^r) = τ(p^{r+1}) + p^{11} · τ(p^{r-1})`,
which rearranges to the recurrence. -/

private lemma pow_div_self_of_one_le {p : ℕ} (hp : p.Prime) (r : ℕ) (hr : r ≥ 1) :
    p ^ r / p = p ^ (r - 1) := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hr)
  rw [Nat.succ_sub_one, pow_succ, Nat.mul_div_cancel _ hp.pos]

private lemma p_dvd_pow {p : ℕ} (_hp : p.Prime) (r : ℕ) (hr : r ≥ 1) : p ∣ p ^ r :=
  dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hr)

instance instTauHeckeRecurrenceOfMaster [TauHeckeMaster] : TauHeckeRecurrence where
  hecke {p} hp r hr := by
    have hpr_pos : p ^ r ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero r hp.pos.ne')
    have hmaster := TauHeckeMaster.master hp (p ^ r) hpr_pos
    rw [if_pos (p_dvd_pow hp r hr), pow_div_self_of_one_le hp r hr] at hmaster
    -- hmaster : τ p * τ (p^r) = τ (p * p^r) + p^11 * τ (p^(r-1))
    -- Goal:    τ (p^(r+1))    = τ p * τ (p^r) - p^11 * τ (p^(r-1))
    have hpow : p * p ^ r = p ^ (r + 1) := by ring
    rw [hpow] at hmaster
    linarith

/-! ## Derivation 2: master ⇒ multiplicativity

The harder derivation. We split into:

* `tau_mul_prime_of_not_dvd` — direct corollary: for `p ∤ n` the master
  identity collapses to `τ(p · n) = τ(p) · τ(n)`.
* `tau_pow_mul_coprime` — for `p ∤ k`, all `a ≥ 0`: `τ(p^a · k) = τ(p^a) · τ(k)`.
  By induction on `a`, using the master identity to step from `a` to `a + 1`
  and the previously-derived recurrence to factor `τ(p^{a+1})`.
* The main theorem follows by `Nat.recOnPosPrimePosCoprime`. -/

private lemma tau_mul_prime_of_not_dvd [TauHeckeMaster] {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n ≥ 1) (hpn : ¬ p ∣ n) :
    τ (p * n) = τ p * τ n := by
  have h := TauHeckeMaster.master hp n hn
  rw [if_neg hpn] at h
  linarith

private lemma tau_pow_mul_coprime [TauHeckeMaster] {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hpk : ¬ p ∣ k) (a : ℕ) :
    τ (p ^ a * k) = τ (p ^ a) * τ k := by
  have hk : k ≥ 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (dvd_zero p) hpk
    · exact h
  -- Strong induction on `a` to allow appealing to the IH at both `a` and `a - 1`.
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
      -- τ(1 · k) = τ(k) = 1 · τ(k) = τ(1) · τ(k)
      simp only [pow_zero, one_mul, tau_one]
    | 1 =>
      -- τ(p · k) = τ(p) · τ(k), direct from master + p ∤ k
      simp only [pow_one]
      exact tau_mul_prime_of_not_dvd hp hk hpk
    | a + 2 =>
      -- a' = a + 2 ≥ 2: apply master at n = p^(a+1) · k, where p ∣ n.
      set a' : ℕ := a + 1 with ha'def
      have ha'1 : a' ≥ 1 := by simp [a']
      have hpa'_ne : p ^ a' ≠ 0 := pow_ne_zero a' (Nat.pos_iff_ne_zero.mp hp.pos)
      have hpa'k_pos : p ^ a' * k ≥ 1 :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero hpa'_ne (Nat.one_le_iff_ne_zero.mp hk))
      have hp_dvd_pa'k : p ∣ p ^ a' * k :=
        dvd_mul_of_dvd_left (p_dvd_pow hp a' ha'1) k
      have hdiv : p ^ a' * k / p = p ^ (a' - 1) * k := by
        rw [Nat.mul_comm (p ^ a') k,
            Nat.mul_div_assoc k (p_dvd_pow hp a' ha'1),
            pow_div_self_of_one_le hp a' ha'1,
            Nat.mul_comm k]
      have hmaster := TauHeckeMaster.master hp (p ^ a' * k) hpa'k_pos
      rw [if_pos hp_dvd_pa'k, hdiv] at hmaster
      -- IH at a' (= a+1 < a+2) and at a' - 1 = a (< a+2)
      have ih_a' : τ (p ^ a' * k) = τ (p ^ a') * τ k :=
        ih a' (by omega)
      have ih_am1 : τ (p ^ (a' - 1) * k) = τ (p ^ (a' - 1)) * τ k :=
        ih (a' - 1) (by omega)
      -- Recurrence for τ at prime powers (we already derived TauHeckeRecurrence
      -- as an instance from `TauHeckeMaster`, but inline it here for clarity).
      have hrec : τ (p ^ (a' + 1)) = τ p * τ (p ^ a') - (p : ℤ) ^ 11 * τ (p ^ (a' - 1)) := by
        haveI : TauHeckeRecurrence := instTauHeckeRecurrenceOfMaster
        exact TauHeckeRecurrence.hecke hp a' ha'1
      -- p * (p^a' * k) = p^(a'+1) * k
      have hpow : p * (p ^ a' * k) = p ^ (a' + 1) * k := by ring
      rw [hpow] at hmaster
      -- hmaster : τ p * τ (p^a' * k) = τ (p^(a'+1) * k) + p^11 * τ (p^(a'-1) * k)
      rw [ih_a', ih_am1] at hmaster
      -- Now solve for τ (p^(a'+1) * k):
      have hsolve : τ (p ^ (a' + 1) * k) =
          τ p * (τ (p ^ a') * τ k) - (p : ℤ) ^ 11 * (τ (p ^ (a' - 1)) * τ k) := by
        linarith
      have : a + 2 = a' + 1 := by simp [a']
      rw [this, hsolve, hrec]; ring

/-- The main multiplicativity theorem under `TauHeckeMaster`.

Stated in a form amenable to `Nat.recOnPosPrimePosCoprime`. -/
private theorem tau_mul_coprime_aux [TauHeckeMaster] :
    ∀ m n : ℕ, Nat.Coprime m n → τ (m * n) = τ m * τ n := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    -- m = p^k, k > 0: ∀ n coprime to p^k, τ(p^k · n) = τ(p^k) · τ(n)
    intro n hcop
    -- Coprime (p^k) n means gcd(p^k, n) = 1, hence p ∤ n
    have hpn : ¬ p ∣ n := by
      intro hd
      have hpdvd : p ∣ Nat.gcd (p ^ k) n :=
        Nat.dvd_gcd (dvd_pow_self p hk.ne') hd
      rw [hcop] at hpdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvd)
    exact tau_pow_mul_coprime hp hpn k
  | zero =>
    -- m = 0: Coprime 0 n forces n = 1
    intro n hcop
    have hn1 : n = 1 := by
      have h := hcop
      simp [Nat.Coprime, Nat.gcd_zero_left] at h
      exact h
    subst hn1
    simp [tau_one]
  | one =>
    intro n _
    simp [tau_one]
  | coprime a b ha hb hab IHa IHb =>
    -- m = a · b with a,b > 1 coprime: motive a, motive b → motive (a*b)
    intro n hcop
    -- gcd(a*b, n) = 1 → gcd(a,n) = 1 and gcd(b,n) = 1
    have han : Nat.Coprime a n := hcop.coprime_dvd_left ⟨b, by ring⟩
    have hbn : Nat.Coprime b n := hcop.coprime_dvd_left ⟨a, by ring⟩
    -- gcd(a, b*n) = 1 (a coprime to b and to n)
    have habn : Nat.Coprime a (b * n) := hab.mul_right han
    -- τ(a*b*n) = τ(a*(b*n)) = τ(a) * τ(b*n) = τ(a) * τ(b) * τ(n)
    have step1 : τ (a * b * n) = τ a * τ (b * n) := by
      rw [show a * b * n = a * (b * n) from by ring]
      exact IHa (b * n) habn
    have step2 : τ (b * n) = τ b * τ n := IHb n hbn
    have step3 : τ (a * b) = τ a * τ b := IHa b hab
    rw [step1, step2, step3]; ring

/-- **Theorem (multiplicativity from master).** -/
instance instTauMultiplicativeOfMaster [TauHeckeMaster] : TauMultiplicative where
  tau_one_eq := tau_one
  mul_coprime {m n} hmn := tau_mul_coprime_aux m n hmn

end RamanujanTau
