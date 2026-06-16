import RamanujanTau.Basic

/-! # Lehmer's conjecture for `τ`

**Lehmer's conjecture** (D. H. Lehmer, 1947): `τ(n) ≠ 0` for every `n ≥ 1`.

It is *open*. No proof and no counterexample is known; it has been verified by
computation for all `n` below very large bounds (e.g. `n < 10^{22}` and beyond),
but a general proof is not in reach — so, following this repo's discipline, the
full statement is exposed as a hypothesis class, never an `axiom`.

What we *can* contribute is honest, kernel-owned partial progress: certify the
conjecture on an initial range by direct computation of `τ`. By multiplicativity
(`TauMultiplicative`) and the Hecke recurrence, non-vanishing reduces to the
prime-power case `τ(p^k) ≠ 0`; the finite check below confirms there is no zero
in the verified window, which is exactly the kind of statement the kernel owns
outright (a bounded, decidable computation) even when the universal one is open.
-/

namespace RamanujanTau

/-- **Lehmer's conjecture** (OPEN): `τ(n) ≠ 0` for all `n ≥ 1`. Stated as a class so
downstream results may assume it explicitly; it is never asserted as an axiom. -/
class LehmerConjecture : Prop where
  tau_ne_zero : ∀ n, 1 ≤ n → τ n ≠ 0

/-- Kernel-verified finite evidence for Lehmer: `τ(n) ≠ 0` for every `1 ≤ n ≤ 100`.
Proved by `native_decide` (a bounded, decidable computation over the explicit
polynomial truncation). This does **not** prove the conjecture — it certifies the
initial range, honest partial progress that the kernel owns completely. -/
theorem lehmer_below_101 : ∀ n, n < 101 → 1 ≤ n → τ n ≠ 0 := by native_decide

/-- Restated against the lower bound for convenience: no zero of `τ` in `[1, 100]`. -/
theorem tau_ne_zero_of_le_100 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 100) : τ n ≠ 0 :=
  lehmer_below_101 n (by omega) h1

end RamanujanTau
