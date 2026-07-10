import RamanujanTau.Multiplicativity
import RamanujanTau.Lehmer
import Mathlib.Data.Nat.Factorization.Induction

/-! # Lehmer's conjecture reduces to prime powers

**Lehmer's conjecture** — `τ(n) ≠ 0` for all `n ≥ 1` — is open (see `Lehmer.lean`). This file
proves the one genuinely reachable structural fact about it: assuming `τ` is multiplicative
(`TauMultiplicative`, discharged unconditionally by `TauHeckeMaster` in `HeckeTheory.lean`), the
whole conjecture is **equivalent** to its restriction to prime powers,

`(∀ n ≥ 1, τ n ≠ 0)  ↔  (∀ p prime, ∀ k ≥ 1, τ(pᵏ) ≠ 0)`.

This is honest partial progress, not a proof of the conjecture: it does not close the open problem,
it *locates* it. Every remaining bit of open content sits in the prime-power values `τ(pᵏ)`.

Note this is the *correct* reduction — it does **not** go further, to primes alone. `τ(pᵏ)` can
vanish independently of `τ(p)`: by the Hecke recurrence `τ(pᵏ) = p^{11k/2}·sin((k+1)θ_p)/sin θ_p`
with `cos θ_p = τ(p)/(2p^{11/2})`, so `τ(pᵏ) = 0 ⇔ (k+1)θ_p ∈ πℤ`, which can happen with `τ(p) ≠ 0`
(i.e. `θ_p ≠ π/2`) whenever `θ_p/π` is rational. So prime powers, not primes, is the true floor.
-/

namespace RamanujanTau

/-- **The reachable half of Lehmer.** If `τ(pᵏ) ≠ 0` for every prime power (`k ≥ 1`), then
`τ(n) ≠ 0` for every `n ≥ 1`. Proved by multiplicative induction on the factorization of `n`;
uses only `TauMultiplicative`, which is unconditional given `TauHeckeMaster`. -/
theorem tau_ne_zero_of_prime_powers [TauMultiplicative]
    (H : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → τ (p ^ k) ≠ 0) :
    ∀ n : ℕ, 1 ≤ n → τ n ≠ 0 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => intro _; exact H p hp k hk
  | zero => intro h; exact absurd h (by norm_num)
  | one => intro _; rw [tau_one]; exact one_ne_zero
  | coprime a b ha hb hab IHa IHb =>
    intro _
    rw [TauMultiplicative.mul_coprime hab]
    exact mul_ne_zero (IHa (by omega)) (IHb (by omega))

/-- **Lehmer ⇔ prime-power non-vanishing** (assuming multiplicativity). The full conjecture is
equivalent to its restriction to prime powers: this pins the entire open content to the values
`τ(pᵏ)`. The forward direction is immediate (`pᵏ ≥ 1`); the reverse is
`tau_ne_zero_of_prime_powers`. -/
theorem lehmer_iff_prime_powers [TauMultiplicative] :
    (∀ n : ℕ, 1 ≤ n → τ n ≠ 0) ↔ (∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → τ (p ^ k) ≠ 0) := by
  constructor
  · intro H p hp k _
    exact H (p ^ k) (Nat.one_le_pow k p hp.pos)
  · exact tau_ne_zero_of_prime_powers

/-- Packaged against the repo's `LehmerConjecture` class: the class holds **iff** `τ` is nonzero on
all prime powers. So a future proof of Lehmer needs only the prime-power case. -/
theorem lehmerConjecture_iff_prime_powers [TauMultiplicative] :
    LehmerConjecture ↔ (∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → τ (p ^ k) ≠ 0) :=
  ⟨fun h => (lehmer_iff_prime_powers).mp h.tau_ne_zero,
   fun H => ⟨(lehmer_iff_prime_powers).mpr H⟩⟩

end RamanujanTau
