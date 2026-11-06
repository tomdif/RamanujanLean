/-
# `SKQFHyp`: the arithmetic hypothesis behind Selberg's key lemma for `L(Δ,s)`

Purely arithmetic, in the style of `HafnerBridge.QFHyp`: only Selberg's coefficients
`β = βSel y`, `λ`, the local Rankin–Selberg factors `ρ_p(a, s)` at `s = 1 − iv`, the Laurent data
`r₀ = c0`, `γ_R = gammaD` of `R(s) = Σ λ(n)² n^{−s}` at `s = 1`, and real parameters `v, L, h`.
No integrals over `t`, no `Γ`, no `L`-values.

For a quadruple `(a,b,c,d) ∈ [1,y]⁴` put `P = ac`, `Q = bd`, `g = (P,Q)`, `P₁ = P/g`, `Q₁ = Q/g`,

    κ(a,b,c,d) = β(a)β(b)β(c)β(d)/[P,Q],      e_v(a,b,c,d) = (P₁ d / c)^{iv},

and (complex local factors, `D_p(s) = Σ_j λ(p^j)² p^{−js}`, `N_p(a,s) = Σ_j λ(p^{j+a})λ(p^j)p^{−js}`)

    ρ(m, s) = Π_{p^a ∥ m} N_p(a,s)/D_p(s),
    𝒮(v)   = Σ κ e_v ρ(P₁, 1−iv) ρ(Q₁, 1−iv),
    𝒮⁰(v)  = Σ κ e_v (P₁Q₁)^{−iv/2} ρ(P₁) ρ(Q₁),
    𝒜(v,L) = (r₀/(iv)) (e^{−v²/4} 𝒮⁰(v) − e^{−ivL} 𝒮(v)) + γ_R e^{−ivL} 𝒮(v).

`𝒜` is (paper derivation, `docs/SELBERG_KEY.md` §3) the residue part of the diagonal
`Expand.DiagLag(u, v)` at `L = log(u/2π)`: the pole of `D_{P₁,Q₁}(1−iv+2z) = R·ρ·ρ` at `z = iv/2`
gives the `𝒮⁰` term, the residue at `z = 0` gives `e^{−ivL} R(1−iv) ρρ`, and `R(1−iv)` is replaced
by its Laurent polynomial `−r₀/(iv) + γ_R` (remainder `O(v)·𝒮`, controlled by clause (i)).
At `v = 0`, `𝒮⁰(0) = 𝒮(0) = Q⁰(y)` of `QFHyp`, so the bracket vanishes and `𝒜` is regular.

**`SKQFHyp θ`** (Selberg's arithmetic lemma for `Δ`, with `y = ⌊T^θ⌋`, `h = K/log T`):
(i) `|𝒮(v)| ≤ B` for `|v| ≤ h`; (ii) `|∫_{−h}^{h} (h − |v|) Re 𝒜(v, L) dv| ≤ (D/√K) h²`
uniformly for `L ∈ [log(T/4π), log T]`.  The `1/√K` comes from the square-root branch point
of `R(1+s)^{−1/2}` (Selberg–Delange, `κ = −1/2`), exactly as the `1/log y` in `QFHyp`.
**Status: statement only** (not used in a proof; the analytic step `SKSplitHyp ⇐ SKQFHyp` is
paper-level, `docs/SELBERG_KEY.md` §§3–4).
-/
import RamanujanTau.SelbergKey.Reduce

set_option autoImplicit false

namespace RamanujanTau.SelbergKey

open Complex Finset
open scoped Real

/-- `λ(n) = τ(n) n^{−11/2}`. -/
noncomputable abbrev lamK : ℕ → ℝ := HafnerBridge.lam

/-- `D_p(s) = Σ_j λ(p^j)² p^{−js}`. -/
noncomputable def DpC (p : ℕ) (s : ℂ) : ℂ :=
  ∑' j : ℕ, ((lamK (p ^ j) ^ 2 : ℝ) : ℂ) * (p : ℂ) ^ (-((j : ℂ) * s))

/-- `N_p(a,s) = Σ_j λ(p^{j+a}) λ(p^j) p^{−js}`. -/
noncomputable def NpC (p a : ℕ) (s : ℂ) : ℂ :=
  ∑' j : ℕ, ((lamK (p ^ (j + a)) * lamK (p ^ j) : ℝ) : ℂ) * (p : ℂ) ^ (-((j : ℂ) * s))

/-- `ρ(m, s) = Π_{p^a ∥ m} N_p(a,s)/D_p(s)`. -/
noncomputable def rhoC (m : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ m.primeFactors, NpC p (m.factorization p) s / DpC p s

/-- `P₁ = ac/(ac,bd)`. -/
def P1 (a b c d : ℕ) : ℕ := a * c / Nat.gcd (a * c) (b * d)

/-- `Q₁ = bd/(ac,bd)`. -/
def Q1 (a b c d : ℕ) : ℕ := b * d / Nat.gcd (a * c) (b * d)

/-- `κ(a,b,c,d) = β(a)β(b)β(c)β(d)/[ac,bd]` for `β = βSel y`. -/
noncomputable def kap (y a b c d : ℕ) : ℝ :=
  HafnerMV2.βSel y a * HafnerMV2.βSel y b * HafnerMV2.βSel y c * HafnerMV2.βSel y d /
    (Nat.lcm (a * c) (b * d) : ℝ)

/-- `e_v(a,b,c,d) = (P₁ d/c)^{iv}`. -/
noncomputable def ev (a b c d : ℕ) (v : ℝ) : ℂ :=
  cexp ((v : ℂ) * I * ((Real.log (P1 a b c d) + Real.log d - Real.log c : ℝ) : ℂ))

/-- Sum over `[1,y]⁴`. -/
noncomputable def sum4 (y : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ a ∈ Icc 1 y, ∑ b ∈ Icc 1 y, ∑ c ∈ Icc 1 y, ∑ d ∈ Icc 1 y, f a b c d

/-- `𝒮(v) = Σ κ e_v ρ(P₁, 1−iv) ρ(Q₁, 1−iv)`. -/
noncomputable def Sv (y : ℕ) (v : ℝ) : ℂ :=
  sum4 y fun a b c d => (kap y a b c d : ℂ) * ev a b c d v *
    rhoC (P1 a b c d) (1 - v * I) * rhoC (Q1 a b c d) (1 - v * I)

/-- `𝒮⁰(v) = Σ κ e_v (P₁Q₁)^{−iv/2} ρ(P₁) ρ(Q₁)` (real `ρ` at `s = 1`, `HafnerBridge.rho`). -/
noncomputable def S0v (y : ℕ) (v : ℝ) : ℂ :=
  sum4 y fun a b c d => (kap y a b c d : ℂ) * ev a b c d v *
    cexp (-((v : ℂ) * I * ((Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2 : ℝ) : ℂ))) *
    ((HafnerBridge.rho (P1 a b c d) * HafnerBridge.rho (Q1 a b c d) : ℝ) : ℂ)

/-- `𝒜(v,L) = (r₀/(iv))(e^{−v²/4}𝒮⁰ − e^{−ivL}𝒮) + γ_R e^{−ivL}𝒮`. -/
noncomputable def Av (y : ℕ) (v L : ℝ) : ℂ :=
  (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I) *
      (((Real.exp (-(v ^ 2 / 4)) : ℝ) : ℂ) * S0v y v - cexp (-((v * L : ℝ) : ℂ) * I) * Sv y v) +
    (GoodSecondTerm.gammaD : ℂ) * cexp (-((v * L : ℝ) : ℂ) * I) * Sv y v

/-- **Selberg's arithmetic lemma for `Δ`** (named hypothesis; statement only). -/
def SKQFHyp (θ : ℝ) : Prop :=
  ∃ B D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ v ∈ Set.Icc (-(K / Real.log T)) (K / Real.log T), ‖Sv ⌊T ^ θ⌋₊ v‖ ≤ B) ∧
    ∀ L ∈ Set.Icc (Real.log (T / (4 * π))) (Real.log T),
      |∫ v in (-(K / Real.log T))..(K / Real.log T),
          (K / Real.log T - |v|) * (Av ⌊T ^ θ⌋₊ v L).re| ≤ D / Real.sqrt K * (K / Real.log T) ^ 2

/-- Sanity: the trivial mollifier (`y = 1`) has `𝒜(v, L) = r₀ (e^{−v²/4} − e^{−ivL})/(iv) + γ_R e^{−ivL}`,
whose real part is `r₀ sin(vL)/v + γ_R cos(vL)`; the `v`-integral is `≈ π r₀ h`, **not** `≪ h²/√K`:
mollification is necessary (cf. `HAFNER_PROPORTION.md` §3).  Here we record the `y = 1` value of
`κ` (`β(1) = 1`). -/
lemma kap_one_one : kap 1 1 1 1 1 = 1 := by
  simp [kap, HafnerMV2.βSel, SelbergCoeffs.alpha_one]

end RamanujanTau.SelbergKey
