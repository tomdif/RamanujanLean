import RamanujanTau.Basic
import RamanujanTau.SmallValues
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-! # Hecke recurrence

For every prime `p` and `r ≥ 1`:
```
τ(p^{r+1}) = τ(p) · τ(p^r) - p^{11} · τ(p^{r-1})
```

This recurrence — together with multiplicativity — determines `τ` from
its values on primes.

The proof uses the action of Hecke operators `T_p` on the weight-12 cusp form
space and the fact that Δ is a Hecke eigenform with eigenvalue `τ(p)` at `T_p`.
We expose it as a hypothesis class until the Hecke infrastructure is in place.
-/

namespace RamanujanTau

/-- Hypothesis class: the Hecke recurrence at every prime. -/
class TauHeckeRecurrence : Prop where
  /-- For every prime `p` and `r ≥ 1`:
      `τ(p^{r+1}) = τ(p) · τ(p^r) - p^{11} · τ(p^{r-1})`. -/
  hecke : ∀ {p : ℕ}, p.Prime → ∀ r : ℕ,
    τ (p^(r+1)) = τ p * τ (p^r) - (p : ℤ)^11 * τ (p^(r-1))

/-! ## Numerical sanity checks

Verified by direct computation: the recurrence holds at `p = 2, r = 1`
(i.e. `τ(4) = τ(2)² - 2¹¹·τ(1)`) and `p = 2, r = 2` (i.e.
`τ(8) = τ(2)·τ(4) - 2¹¹·τ(2)`). These don't *prove* the recurrence in general
(they're just instances), but they do verify it's the right statement. -/

theorem hecke_check_p2_r1 : τ 4 = τ 2 * τ 2 - (2 : ℤ)^11 * τ 1 := by
  rw [tau_four, tau_two, tau_one]; norm_num

theorem hecke_check_p2_r2 : τ 8 = τ 2 * τ 4 - (2 : ℤ)^11 * τ 2 := by
  rw [tau_eight, tau_two, tau_four]; norm_num

theorem hecke_check_p3_r1 : τ 9 = τ 3 * τ 3 - (3 : ℤ)^11 * τ 1 := by
  rw [tau_nine, tau_three, tau_one]; norm_num

end RamanujanTau
