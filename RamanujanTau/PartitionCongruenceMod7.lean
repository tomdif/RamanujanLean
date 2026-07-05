/-
# Ramanujan's partition congruence `p(7n+5) ≡ 0 (mod 7)` — the arithmetic heart

Mirror of the `mod 5` heart. Here `1/(q;q)_∞ ≡ (q;q)_∞⁶ / (q⁷;q⁷)_∞ (mod 7)` and
`(q;q)_∞⁶ = ((q;q)_∞³)² = (Σ (−1)ᵐ(2m+1) q^{m(m+1)/2})²`. A coefficient of `q^i` is a sum of terms
`±(2j+1)(2k+1)` over pairs `(j,k)` with `tri(j)+tri(k) = i`. When `i ≡ 5 (mod 7)`, the doubled exponent
`j(j+1)+k(k+1) ≡ 10 ≡ 3 (mod 7)`, and then the Jacobi weight product `(2j+1)(2k+1) ≡ 0 (mod 7)` — the only
residue pattern reaching `tri(j)+tri(k) ≡ 5` is `j ≡ k ≡ 3 (mod 7)`, where both `2j+1 ≡ 0`.
-/
import Mathlib.Data.ZMod.Basic

namespace RamanujanTau.PartitionCongruenceMod7

/-- **Decidable core over `ZMod 7`.** If `a(a+1) + b(b+1) = 3` (i.e. `tri(a)+tri(b) ≡ 5 (mod 7)`, since
`2` is a unit mod 7), then the Jacobi weight product `(2a+1)(2b+1) = 0`. Verified over all `7×7` pairs. -/
theorem weight_prod_zero_of_double_exponent (a b : ZMod 7)
    (h : a * (a + 1) + b * (b + 1) = 3) : (2 * a + 1) * (2 * b + 1) = 0 := by
  revert h; revert a b; decide

/-- **The arithmetic heart of `p(7n+5) ≡ 0 (mod 7)`.** For integers `j, k`, if
`j(j+1) + k(k+1) ≡ 3 (mod 7)` (the doubled form of `tri(j)+tri(k) ≡ 5`), then `(2j+1)(2k+1) ≡ 0 (mod 7)`. -/
theorem jacobi_weight_prod_dvd_of_exponent {j k : ℤ}
    (h : (j * (j + 1) + k * (k + 1)) ≡ 3 [ZMOD 7]) : ((2 * j + 1) * (2 * k + 1)) ≡ 0 [ZMOD 7] := by
  have hcast : ((j : ZMod 7) * ((j : ZMod 7) + 1) + (k : ZMod 7) * ((k : ZMod 7) + 1)) = 3 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
    push_cast at this ⊢; convert this using 1
  have hgoal : (2 * (j : ZMod 7) + 1) * (2 * (k : ZMod 7) + 1) = 0 :=
    weight_prod_zero_of_double_exponent _ _ hcast
  have : (((2 * j + 1) * (2 * k + 1) : ℤ) : ZMod 7) = ((0 : ℤ) : ZMod 7) := by
    push_cast; simpa using hgoal
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

/-- Sanity check: the only residue pattern reaching `tri(a)+tri(b) ≡ 5 (mod 7)` is `a ≡ b ≡ 3`. -/
example : (∀ a b : ZMod 7, a * (a + 1) + b * (b + 1) = 3 → a = 3 ∧ b = 3) := by decide

end RamanujanTau.PartitionCongruenceMod7
