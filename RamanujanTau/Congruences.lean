import RamanujanTau.Basic
import RamanujanTau.SmallValues
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Int.ModEq

/-! # Ramanujan's congruences for τ

Ramanujan (1916) and others established several congruences. The deepest is:

```
τ(n) ≡ σ₁₁(n)  (mod 691)    for all n ≥ 1
```

where `σ_k(n) = Σ_{d | n} d^k`.

Other congruences include:
* `τ(n) ≡ σ₁₁(n) (mod 2^11)`  if `n ≡ 1 (mod 8)`
* `τ(n) ≡ 0 (mod 5)` if `n ≡ 0 (mod 5)`
* `τ(p) ≡ 1 + p^{11} (mod 2^8)` for `p` odd prime
* `τ(p) ≡ p + p^{10} (mod 7)` for `p ≠ 7`
* `τ(p) ≡ p^{-1} + p^{12} (mod 23^2)` if `p` is a quadratic residue mod 23

The full theory uses Galois representations and Eichler-Shimura. We state the
mod-691 congruence as a hypothesis class.

## Numerical sanity

We verify the mod-691 congruence numerically for small `n`. The σ_11 sum:
* σ₁₁(1) = 1, τ(1) = 1, diff = 0 ✓
* σ₁₁(2) = 1 + 2¹¹ = 2049, τ(2) = -24, diff = 2073 = 3 · 691 ✓
* σ₁₁(3) = 1 + 3¹¹ = 177148, τ(3) = 252, diff = 176896 = 256 · 691 ✓
-/

namespace RamanujanTau

open Finset

/-- The divisor sum `σ_k(n) = Σ_{d | n} d^k` for `k = 11`. -/
def sigma11 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)^11

/-- σ₁₁(1) = 1. -/
theorem sigma11_one : sigma11 1 = 1 := by
  unfold sigma11; decide

/-- σ₁₁(2) = 1 + 2¹¹ = 2049. -/
theorem sigma11_two : sigma11 2 = 2049 := by
  unfold sigma11; decide

/-- σ₁₁(3) = 1 + 3¹¹ = 177148. -/
theorem sigma11_three : sigma11 3 = 177148 := by
  unfold sigma11; decide

/-- σ₁₁(4) = 1 + 2¹¹ + 4¹¹ = 4196353. -/
theorem sigma11_four : sigma11 4 = 4196353 := by
  unfold sigma11; decide

/-! ### Numerical mod-691 sanity checks -/

theorem cong_691_one : τ 1 ≡ sigma11 1 [ZMOD 691] := by
  rw [tau_one, sigma11_one]

theorem cong_691_two : τ 2 ≡ sigma11 2 [ZMOD 691] := by
  rw [tau_two, sigma11_two]
  decide

theorem cong_691_three : τ 3 ≡ sigma11 3 [ZMOD 691] := by
  rw [tau_three, sigma11_three]
  decide

theorem cong_691_four : τ 4 ≡ sigma11 4 [ZMOD 691] := by
  rw [tau_four, sigma11_four]
  decide

/-- **Hypothesis class**: Ramanujan's mod-691 congruence for τ.

`τ(n) ≡ σ₁₁(n) (mod 691)` for every positive `n`. The proof uses the
fact that `691` divides the numerator of the Bernoulli number `B_{12}`,
combined with the structure of the Eisenstein series `E_{12}` and the relation
`E_{12} = E_4³ - 720 · Δ` modulo lower weights. -/
class TauMod691 : Prop where
  congruence : ∀ n : ℕ, n ≥ 1 → τ n ≡ sigma11 n [ZMOD 691]

end RamanujanTau
