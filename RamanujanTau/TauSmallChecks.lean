/-
# Kernel-checked small cases of Ramanujan's conjecture (Deligne's bound) and of Lehmer's conjecture

Pure kernel evaluation (`decide +kernel`, no `native_decide`) of the computable `τ` of `Basic.lean`:

* `ramanujan_bound_lt50` — `τ(p)² ≤ 4p¹¹` (i.e. `|τ(p)| ≤ 2p^{11/2}`) for every prime `p < 50`;
* `lehmer_lt30` — `τ(n) ≠ 0` for `1 ≤ n < 30`.

The general statements are Deligne's theorem (1974) and Lehmer's open conjecture.
-/
import RamanujanTau.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace RamanujanTau

set_option maxRecDepth 1000000 in
theorem ramanujan_bound_lt50 : ∀ p < 50, Nat.Prime p → (τ p) ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem lehmer_lt30 : ∀ n < 30, 1 ≤ n → τ n ≠ 0 := by decide +kernel

end RamanujanTau
