/-
# Ramanujan's partition congruence `p(5n+4) ≡ 0 (mod 5)` — the arithmetic heart

Ramanujan's proof reduces the congruence to a statement about the coefficients of `(q;q)_∞^4`, via

  `Σ p(n) qⁿ = 1/(q;q)_∞ ≡ (q;q)_∞^4 / (q⁵;q⁵)_∞  (mod 5)`      (Frobenius: `(q;q)_∞^5 ≡ (q⁵;q⁵)_∞`),

and `(q⁵;q⁵)_∞` shifts exponents only by multiples of `5`. So `p(5n+4) ≡ 0 (mod 5)` follows once every
coefficient of `q^i` with `i ≡ 4 (mod 5)` in `(q;q)_∞^4` is divisible by `5`. Writing
`(q;q)_∞^4 = (q;q)_∞ · (q;q)_∞^3` and expanding with

  * Euler's pentagonal number theorem  `(q;q)_∞  = Σ_{k∈ℤ} (−1)ᵏ q^{k(3k−1)/2}`,
  * Jacobi's cube identity              `(q;q)_∞³ = Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}`,

each coefficient of `q^i` is a sum of terms `±(2m+1)` over pairs `(k,m)` with
`pent(k) + tri(m) = i`, where `pent(k) = k(3k−1)/2`, `tri(m) = m(m+1)/2`.

**This file proves the arithmetic heart** (`jacobi_weight_dvd_of_exponent`): whenever such a pair hits an
exponent `≡ 4 (mod 5)`, its Jacobi weight `2m+1` is `≡ 0 (mod 5)`. Hence every contributing term vanishes
mod 5 and the whole `q^i` coefficient is `≡ 0`. This is the genuinely number-theoretic content of the
congruence and is **not** in Mathlib.

**Remaining wall** (the two classical `PowerSeries ℤ` inputs, tracked here, not yet in repo/Mathlib):
Euler pentagonal as a power-series product identity (repo has statement side only) and Jacobi's cube
identity (absent). With those + the `char 5` Frobenius step, the heart below closes the congruence.
No `sorry`.
-/
import Mathlib.Data.ZMod.Basic

namespace RamanujanTau.PartitionCongruenceMod5

/-- **Decidable core over `ZMod 5`.** For residues `a = k`, `b = m`, if the *doubled* exponent
`k(3k−1) + m(m+1) = 3` (equivalently `pent(k)+tri(m) ≡ 4`, since `2` is a unit mod 5), then the Jacobi
weight `2m+1 = 0`. Verified by exhausting all `5×5` residue pairs. -/
theorem weight_zero_of_double_exponent (a b : ZMod 5)
    (h : a * (3 * a - 1) + b * (b + 1) = 3) : 2 * b + 1 = 0 := by
  revert h; revert a b; decide

/-- **The arithmetic heart of `p(5n+4) ≡ 0 (mod 5)`.**
For integers `k, m`, if the pentagonal+triangular exponent `pent(k) + tri(m) ≡ 4 (mod 5)` — stated in the
division-free doubled form `k(3k−1) + m(m+1) ≡ 3 (mod 5)`, using that `2·pent(k) = k(3k−1)`,
`2·tri(m) = m(m+1)` and `2·4 ≡ 3 (mod 5)` — then Jacobi's weight `2m+1 ≡ 0 (mod 5)`. So each term of
`(q;q)_∞·(q;q)_∞³` landing in an exponent `≡ 4 (mod 5)` is divisible by `5`. -/
theorem jacobi_weight_dvd_of_exponent {k m : ℤ}
    (h : (k * (3 * k - 1) + m * (m + 1)) ≡ 3 [ZMOD 5]) : (2 * m + 1) ≡ 0 [ZMOD 5] := by
  -- move to `ZMod 5` via the `Int.cast` ring hom, apply the decidable core, move back
  have hcast : ((k : ZMod 5) * (3 * (k : ZMod 5) - 1) + (m : ZMod 5) * ((m : ZMod 5) + 1)) = 3 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
    push_cast at this ⊢; convert this using 1
  have hgoal : (2 * (m : ZMod 5) + 1) = 0 :=
    weight_zero_of_double_exponent _ _ hcast
  have : ((2 * m + 1 : ℤ) : ZMod 5) = ((0 : ℤ) : ZMod 5) := by push_cast; simpa using hgoal
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

/-- Sanity check: the exponent condition really is `pent(k)+tri(m) ≡ 4 (mod 5)` in doubled form, i.e.
the only residue pattern reaching it is `k ≡ 1`, `m ≡ 2 (mod 5)` — the case that zeroes `2m+1`. -/
example : (∀ a b : ZMod 5, a * (3 * a - 1) + b * (b + 1) = 3 → a = 1 ∧ b = 2) := by decide

end RamanujanTau.PartitionCongruenceMod5
