# Hafner's (MV2) from the twisted second moment (2026-11-06)

**Status.** The implication (MV2) ⇐ `DiagHyp` is proved in Lean: axiom-clean, unconditional apart
from the named hypothesis. The further step `DiagHyp` ⇐ `QFHyp`, i.e. the Laurent / leading-coefficient
evaluation of `MainTw`, is **not done**.

    nice -n 10 lake build RamanujanTau.HafnerMV2.Main      # exit 0

* Every `#print axioms` (5 names) gives `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom`.
* 4 new files, about 450 lines. No committed file was modified.

## Headline

```lean
theorem mv2_of_diag {θ : ℝ} (hθ0 : 0 < θ) (hθ : 136 * θ ≤ 1 / 600) (hD : DiagHyp θ) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T
```

The left side is exactly the (MV2) conjunct of `SelbergCoeffs.SelbergMollHyp` and
`HafnerProportion.SelbergHyp`. The mollifier is `bSel`, i.e. `b = α(1 − log n/log y)` with `y = ⌊T^θ⌋`.
The admissible range is `θ ≤ 1/81600`.

```lean
def DiagHyp (θ : ℝ) : Prop :=
  ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ X ∈ Icc (T / 2) (3 * T),
    ‖DiagSum (βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ X (X ^ (299 / 300 : ℝ))‖ ≤ B * T
```

* `DiagSum β y X H = Σ_{p,q∈[1,y]²} κ(p,q)·MainTw(h_p, h_q, X, H)`.
* `h_p = p₁p₂` and `κ = ½β(p₁)β(p₂)β(q₁)β(q₂)(h_p h_q)^{−1/2}`.
* `MainTw` is the smoothed diagonal of `TwistedMoment`, so `DiagSum` is the full diagonal (`kM = hN`)
  contribution to the mollified mean square up to height `X`.
* It mentions no `L`-values. It does contain the explicit smoothing integrals `P̃` of the fixed weight `V`.

## Method

1. **Expansion** (`Expand.normSq_Mc_sq`).
   * On the line, `M(6+iu)² = Σ_{p} β(p₁)β(p₂) h_p^{−1/2} h_p^{−iu}`. This uses `cpow_line`:
     `n^{11/2−(6+iu)} = n^{−1/2} e^{−iu log n}`.
   * Hence `|M²|² = Σ_{p,q} κ(p,q)((h_p/h_q)^{iu} + (h_q/h_p)^{iu})`, using real coefficients and
     symmetrising in `(p, q)`.
2. **Averaging** (`Av_LM2`). The `u`-average `Av` commutes with finite sums (`Av_sum`), so
   `Av(|LM²|²) = Σ κ·TwAv(h_p, h_q)`.
3. **Twisted moment** (`avg_err`).
   * Apply `TwistedMoment.twisted_moment` to each pair, using `|κ| ≤ ½` (from `|bSel(n)| ≤ √n`,
     unconditional) and `h_p h_q ≤ y⁴`.
   * Over the `y⁴` pairs this gives `‖Av − DiagSum‖ ≤ (C/2) y^{136} X^{599/600}`.
4. **Sharp cutoff** (`sharp_le`).
   * For `G ≥ 0`, `I(u) = ∫_{16}^u G` is monotone. So
     `∫_T^{3T} G ≤ Av_{[3T, 3T+H₃]} − Av_{[T/2, T/2+H₁]}`, with `H = X^{299/300}` and `T/2 + H₁ ≤ T`.
5. **Assembly** (`mv2_of_diag`).
   * `∫_T^{3T}|LM²|² ≤ ‖DiagSum(3T)‖ + ‖DiagSum(T/2)‖ + C y^{136}(3T)^{599/600} ≤ (2B + 3C) T`.
   * This uses `y^{136} ≤ T^{136θ}` and `136θ + 599/600 ≤ 1`.
   * It needs `T ≥ 2^{301}`, so that `T/2 ≥ 2^{300}`.

## Gaps

1. **`DiagHyp` ⇐ QF is not formalised.** This is the leading-coefficient evaluation the coordinator asked for.
   * For the pair `(h_p, h_q) = (h, k)`, `g = (h,k)`, `h₁ = h/g`, `k₁ = k/g`:
     `MainTw = (2/√(hk))·g·Σ_r λ(h₁r)λ(k₁r) r^{−1} P̃(log(h₁k₁r²), 0, X, H)`.
   * Evaluating it needs, uniformly in `h₁k₁ ≤ y⁴` with polynomial loss:
     * (a) `Σ_{r≤x} λ(h₁r)λ(k₁r) = r₀ ρ(h₁)ρ(k₁) x + O(x^{1−η}(h₁k₁)^A)`, via `D_{h,k}(s) = R(s)ρ(h₁)ρ(k₁)`.
       This is Hecke multiplicativity: factor `r = r₁r₂` with `r₁ | (h₁k₁)^∞` and `(r₂, h₁k₁) = 1`. It also
       needs the coprime-restricted Rankin asymptotic. Convergence of `ρ_p` without Deligne uses
       `|λ(p^j)| ≪ p^{11j/40}` (`TauPNTUncond.weil_uu`).
     * (b) the derivative `ρ'/ρ`, giving the `log` companions.
     * (c) the `V`-smoothing: Mellin transform of `V`, double pole at `w = 0`, giving
       `X(log X + const + ρ'/ρ terms)`.
   * Then `DiagSum(X) = 2r₀ ∫^X Q_t dt + O(X^{1−η'})`, with `Q_t` the form of `docs/SELBERG_COEFFS.md` §3:
     `Q_t = Σ_{h,k≤y²} c(h)c(k)/[h,k]·ρ(h₁)ρ(k₁)[log(t/2π) − ½log(h₁k₁) + γ_Δ + (ρ'/ρ)(h₁) + (ρ'/ρ)(k₁)]`,
     where `c = b ∗ b`.
   * Hence **`QFHyp`** — `Q⁰(c) = Σ c(h)c(k)ρ(h₁)ρ(k₁)/[h,k] ≪ 1/log y` plus the companion forms `≪ 1`
     (`SELBERG_COEFFS` §3, `SELBERG_DELANGE` §4) — implies `DiagHyp`.
   * `QFHyp` is **not stated in Lean** here. Stating it needs `ρ` and `ρ'` as definitions, and the
     bridge (a)–(c) is the missing piece, estimated at 1.5–3k lines.
   * The Selberg–Delange agent should target the §3 form. `DiagHyp` is the interface on this side.
2. The (SK) conjunct of `SelbergMollHyp` is untouched.
3. `θ ≤ 1/81600` is far from optimal. It is inherited from `(hk)^{33}` and `1/600`.
