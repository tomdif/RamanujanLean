/-
# Generic coefficient sequences for the Good machinery

`GoodSeq lam` packages what the off-diagonal analysis of `GoodSecondTerm2` uses about `λ`:
`λ(0) = 0`, a Rankin bound `Σ_{n≤N} λ(n)² ≤ N`, a shifted-convolution bound
`|Σ_{n≤N} λ(n)λ(n+h)| ≤ (N+h)^{20/21} h^{1/21}`, and a shift `c ≥ 0` of the `V`-argument.
(Constants are normalised to `C1 = 1`; general sequences are rescaled.)
-/
import RamanujanTau.GoodSecondTerm2.IBP

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

/-- The normalised constant `1` (kept opaque-ish so that `set` can name it). -/
noncomputable def C1 : ℝ := 1

lemma C1_eq : C1 = 1 := rfl

lemma C1_pos : 0 < C1 := by rw [C1_eq]; norm_num

class GoodSeq (lam : ℕ → ℝ) where
  c : ℝ
  hc : 0 ≤ c
  zero : lam 0 = 0
  rankin : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ C1 * N
  scs : ∀ h N : ℕ, 1 ≤ h → |∑ n ∈ Finset.Icc 1 N, lam n * lam (n + h)| ≤
    C1 * ((N : ℝ) + h) ^ (1 - 1 / 21 : ℝ) * (h : ℝ) ^ (1 / 21 : ℝ)

/-- `Σ_{n ≤ N} λ(n) λ(n+h)` for a generic sequence. -/
noncomputable def shiftSum (lam : ℕ → ℝ) (h N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, lam n * lam (n + h)

end RamanujanTau.TwistedMoment
