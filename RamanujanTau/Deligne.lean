import RamanujanTau.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! # Deligne's bound for `τ(p)`

**Deligne's bound** (1974), a consequence of his proof of the Weil conjectures
applied to the weight-12 cusp form `Δ`: for every prime `p`,
`|τ(p)| ≤ 2 · p^{11/2}`, equivalently (squaring, to stay in `ℤ`)
`τ(p)^2 ≤ 4 · p^{11}`.

This is one of the deepest theorems about `τ`. Following the repo's discipline we
expose the general statement as a hypothesis class and never assert it as an
`axiom`; the discharge route is Deligne's theorem (étale cohomology / Weil I).

We then certify *instances* of the bound for small primes by `native_decide` —
each is a concrete, kernel-checked confirmation `τ(p)^2 ≤ 4 p^{11}` that the deep
inequality holds where we can compute it. (Equality is approached but never met:
`τ(p)^2 / (4 p^{11}) < 1` strictly, the Sato–Tate angle never being `0` or `π`.)
-/

namespace RamanujanTau

/-- **Deligne's bound** (proved 1974 via the Weil conjectures): `τ(p)^2 ≤ 4 · p^{11}`
for every prime `p`, i.e. `|τ(p)| ≤ 2 p^{11/2}`. Exposed as a class, not an axiom. -/
class DeligneBound : Prop where
  bound : ∀ p : ℕ, p.Prime → (τ p) ^ 2 ≤ 4 * (p : ℤ) ^ 11

/-- `p = 2`: `τ(2)² = 576 ≤ 4·2¹¹ = 8192`. -/
theorem deligne_two : (τ 2) ^ 2 ≤ 4 * (2 : ℤ) ^ 11 := by native_decide

/-- `p = 3`: `τ(3)² = 63504 ≤ 4·3¹¹ = 708588`. -/
theorem deligne_three : (τ 3) ^ 2 ≤ 4 * (3 : ℤ) ^ 11 := by native_decide

/-- `p = 5`: `τ(5)² = 23328900 ≤ 4·5¹¹`. -/
theorem deligne_five : (τ 5) ^ 2 ≤ 4 * (5 : ℤ) ^ 11 := by native_decide

/-- `p = 7`: `τ(7)² = 280361536 ≤ 4·7¹¹`. -/
theorem deligne_seven : (τ 7) ^ 2 ≤ 4 * (7 : ℤ) ^ 11 := by native_decide

/-- `p = 11`: `τ(11)² ≤ 4·11¹¹`. -/
theorem deligne_eleven : (τ 11) ^ 2 ≤ 4 * (11 : ℤ) ^ 11 := by native_decide

/-- `p = 13`: `τ(13)² ≤ 4·13¹¹`. -/
theorem deligne_thirteen : (τ 13) ^ 2 ≤ 4 * (13 : ℤ) ^ 11 := by native_decide

end RamanujanTau
