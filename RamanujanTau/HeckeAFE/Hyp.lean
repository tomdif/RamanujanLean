/-
# The two-sided shifted-convolution hypothesis needed for the twisted second moment (statement only)

Milestone (2) of `docs/HAFNER_PROPORTION.md` needs, after the AFE, the off-diagonal of
`∫ |L(6+it)|² (h/k)^{it} w(t/T) dt`, which is a sum over `a m − b n = ℓ` (`a = h`, `b = k` up to
the roles of the two AFE sums).  The repo's `SubconvexityCond.ShiftedConvolutionBound` is the
one-sided case `a = b = 1`.  This file only *states* the two-sided hypothesis; it is **not used**
by any theorem yet (see `docs/HECKE_AFE.md`, §Goal 2).
-/
import RamanujanTau.SubconvexityCond.Defs

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE

open Finset RamanujanTau.SubconvexityCond

/-- Two-sided sharp shifted sum `Σ_{1 ≤ m,n ≤ N, a m − b n = ℓ} λ(m) λ(n)`, `λ(n) = τ(n) n^{−11/2}`. -/
noncomputable def shiftSum2 (a b : ℕ) (ℓ : ℤ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if (a : ℤ) * m - b * n = ℓ then lam m * lam n else 0

/-- **Two-sided shifted-convolution hypothesis `SCS2(η, B)`**: for all `a, b ≥ 1`, `ℓ ≠ 0`, `N`,
`|Σ_{m,n ≤ N, am − bn = ℓ} λ(m)λ(n)| ≤ C (N + |ℓ|)^{1−η} (ab)^B`.
Classical for some `η > 0` (Kloosterman / spectral methods: Jutila, Blomer 2004,
Blomer–Harcos 2008 give `η` close to `1/2 − θ` with polynomial dependence on `a, b`). -/
def SCS2 (η B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
    |shiftSum2 a b ℓ N| ≤ C * ((N : ℝ) + |(ℓ : ℝ)|) ^ (1 - η) * ((a * b : ℕ) : ℝ) ^ B

/-- `SCS2` is monotone: smaller saving `η` (for `N + |ℓ| ≥ 1`) and larger `B` are weaker. -/
theorem SCS2.mono {η η' B B' : ℝ} (h : SCS2 η B) (hη : η' ≤ η) (hB : B ≤ B') : SCS2 η' B' := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun a b ℓ N ha hb hℓ => (hC a b ℓ N ha hb hℓ).trans ?_⟩
  have hℓ1 : (1:ℝ) ≤ |(ℓ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hℓ
  have h1 : (1:ℝ) ≤ (N : ℝ) + |(ℓ : ℝ)| := by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hab' : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hab : (1:ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast hab'
  have e1 := Real.rpow_le_rpow_of_exponent_le h1 (show 1 - η ≤ 1 - η' by linarith)
  have e2 := Real.rpow_le_rpow_of_exponent_le hab hB
  have hp : 0 ≤ ((a * b : ℕ) : ℝ) ^ B := by positivity
  calc C * ((N : ℝ) + |(ℓ : ℝ)|) ^ (1 - η) * ((a * b : ℕ) : ℝ) ^ B
      ≤ C * ((N : ℝ) + |(ℓ : ℝ)|) ^ (1 - η') * ((a * b : ℕ) : ℝ) ^ B := by gcongr
    _ ≤ _ := by gcongr

end RamanujanTau.HeckeAFE
