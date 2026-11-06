/-
# `QFHyp`: the arithmetic quadratic-form hypothesis for Hafner's (MV2)

Purely arithmetic: only Selberg's coefficients `b = βSel y`, `λ`, the local factors `ρ`, the
Rankin–Selberg Laurent data `r₀ = c0`, `γ_R = gammaD`, and `y`. No `V`, no integrals, no `L`-values.

Local factors at `s = 1` (`λ = SubconvexityCond.lam`):

    D_p = Σ_j λ(p^j)² p^{−j},   N_p(a) = Σ_j λ(p^{j+a}) λ(p^j) p^{−j},   ρ_p(a) = N_p(a)/D_p,

and `ρ'_p(a) = d/ds|_{s=1}` of `N_p(a,s)/D_p(s)`. These are the Euler factors of
`Σ_r λ(h₁r)λ(k₁r) r^{−s} = R(s) ρ(h₁,s) ρ(k₁,s)` for coprime `h₁, k₁`, where `R(s) = Σ λ(n)² n^{−s}`.
`ρ(m) = Π_{p^a ∥ m} ρ_p(a)` and `ρ₁(m) = d/ds ρ(m,s)|_{s=1}`, the product rule written out.

With `c(h) = Σ_{n₁n₂=h} b(n₁)b(n₂)`, `g = (h,k)`, `h₁ = h/g`, `k₁ = k/g`:

    Q⁰(y) = Σ_{h,k ≤ y²} c(h)c(k)/[h,k] · ρ(h₁)ρ(k₁),
    Q¹(y) = Σ_{h,k ≤ y²} c(h)c(k)/[h,k] · ( ρ(h₁)ρ(k₁)(γ_R/r₀ − ½ log(h₁k₁)) + ρ₁(h₁)ρ(k₁) + ρ(h₁)ρ₁(k₁) ).

The diagonal of `∫^X |LM²|²` is `≈ r₀ ∫^X (Q⁰ log(t/2π) + Q¹) dt` (`docs/HAFNER_MV2.md`, 2026-11-06 section).

**`QFHyp`**: `Q⁰(y) ≪ 1/log y` and `Q¹(y) ≪ 1` for all large `y`.
-/
import RamanujanTau.HafnerMV2.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge

open Finset

/-- `λ(n) = τ(n) n^{−11/2}`. -/
noncomputable abbrev lam : ℕ → ℝ := RamanujanTau.SubconvexityCond.lam

/-- `D_p = Σ_j λ(p^j)² p^{−j}` (the Euler factor of `R(s)` at `s = 1`). -/
noncomputable def Dp (p : ℕ) : ℝ := ∑' j : ℕ, lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ))

/-- `N_p(a) = Σ_j λ(p^{j+a}) λ(p^j) p^{−j}`. -/
noncomputable def Np (p a : ℕ) : ℝ := ∑' j : ℕ, lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ))

/-- `D_p'(1) = −Σ_j j log p · λ(p^j)² p^{−j}`. -/
noncomputable def Dp' (p : ℕ) : ℝ :=
  -∑' j : ℕ, (j : ℝ) * Real.log p * lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ))

/-- `N_p'(a,1) = −Σ_j j log p · λ(p^{j+a}) λ(p^j) p^{−j}`. -/
noncomputable def Np' (p a : ℕ) : ℝ :=
  -∑' j : ℕ, (j : ℝ) * Real.log p * lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ))

/-- `ρ_p(a) = N_p(a)/D_p`. -/
noncomputable def rhoP (p a : ℕ) : ℝ := Np p a / Dp p

/-- `ρ_p'(a) = (N_p' D_p − N_p D_p')/D_p²` (derivative at `s = 1`). -/
noncomputable def rhoP' (p a : ℕ) : ℝ := (Np' p a * Dp p - Np p a * Dp' p) / Dp p ^ 2

/-- `ρ(m) = Π_{p^a ∥ m} ρ_p(a)`. -/
noncomputable def rho (m : ℕ) : ℝ := ∏ p ∈ m.primeFactors, rhoP p (m.factorization p)

/-- `ρ₁(m) = d/ds ρ(m,s)|_{s=1}`. -/
noncomputable def rho1 (m : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors, rhoP' p (m.factorization p) * ∏ q ∈ m.primeFactors.erase p, rhoP q (m.factorization q)

/-- `r₀ = Res_{s=1} R(s)` (the repo's `c0`). -/
noncomputable def r0 : ℝ := RamanujanTau.GoodSecondTerm.c0

/-- `γ_R/r₀`, with `R(s) = r₀/(s−1) + γ_R + O(s−1)` and `γ_R = gammaD`. -/
noncomputable def gamR : ℝ := RamanujanTau.GoodSecondTerm.gammaD / r0

/-- `c = b ∗ b` for `b = βSel y`. -/
noncomputable def cS (y h : ℕ) : ℝ := ∑ n ∈ h.divisors, HafnerMV2.βSel y n * HafnerMV2.βSel y (h / n)

/-- The main quadratic form `Q⁰(y)`. -/
noncomputable def Q0 (y : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 (y ^ 2), ∑ k ∈ Icc 1 (y ^ 2),
    cS y h * cS y k / (Nat.lcm h k : ℝ) * (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k))

/-- The companion form `Q¹(y)`. -/
noncomputable def Q1 (y : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 (y ^ 2), ∑ k ∈ Icc 1 (y ^ 2),
    cS y h * cS y k / (Nat.lcm h k : ℝ) *
      (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) *
          (gamR - 1 / 2 * Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) +
        rho1 (h / Nat.gcd h k) * rho (k / Nat.gcd h k) + rho (h / Nat.gcd h k) * rho1 (k / Nat.gcd h k))

/-- **The arithmetic quadratic-form hypothesis** (target of the Selberg–Delange route):
`Q⁰(y) ≪ 1/log y` and `Q¹(y) ≪ 1`. -/
def QFHyp : Prop :=
  ∃ B y₀ : ℝ, ∀ y : ℕ, y₀ ≤ y → |Q0 y| ≤ B / Real.log y ∧ |Q1 y| ≤ B

end RamanujanTau.HafnerBridge
