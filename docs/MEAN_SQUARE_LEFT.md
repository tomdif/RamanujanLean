# Mean square of L(Δ,s) left of the critical line (and the full picture)

Directory: `RamanujanTau/MeanSquareLeft/` (GammaAsymp, Abel, Left, Main).
Build: `nice -n 10 lake build RamanujanTau.MeanSquareLeft.Main` exits 0. Every headline
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide` or new axioms.
Evidence level: **(1) Lean, axiom-clean, unconditional.**

## Headline

```lean
theorem mean_square_tauL_left {σ : ℝ} (hσ : σ < 6) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) /
      T ^ (25 - 4 * σ)) atTop (𝓝 (Cleft σ))

Cleft σ = (2π)^(4σ−24) · RS(2(12−σ)) / (25 − 4σ),   RS β = ∑' n, τ(n)² n^(−β)
```

`Cleft_pos : σ < 6 → 0 < Cleft σ` (since `RS β ≥ τ(1)² = 1`, `one_le_RS`).

**Correction to the requested normalisation.** The brief asked for `T^{13−2σ}` and
`C(σ) = (2π)^{2σ−12} RS/(13−2σ)`. That is the square root of the right factor: by the functional
equation `|χ(σ+it)| ~ (t/2π)^{12−2σ}`, so the weight in the mean square is
`|χ|² ~ (t/2π)^{24−4σ}`. The proved exponent is `25 − 4σ` (equal to 1 at σ = 6, which matches the
`T log T` growth on the critical line up to the logarithm). Since `Cleft σ > 0`, the `T^{13−2σ}`
version is false: the quotient tends to +∞.

## The complete picture (`mean_square_tauL_every_line`)

| line   | asymptotic                                                     | Lean                                                   |
|--------|----------------------------------------------------------------|--------------------------------------------------------|
| σ > 6  | ∫₀ᵀ \|L(σ+it)\|² ~ RS(2σ) · T                                   | `MeanSquareFull.mean_square_tauL_full`                 |
| σ = 6  | ∫₀ᵀ \|L(6+it)\|² ~ 2c · T log T (c = Rankin's constant)         | `CriticalMeanSquareAsymp.critical_mean_square_asymptotic` |
| σ < 6  | ∫₀ᵀ \|L(σ+it)\|² ~ (2π)^{4σ−24} RS(24−2σ)/(25−4σ) · T^{25−4σ}   | `MeanSquareLeft.mean_square_tauL_left`                 |

The theorem `mean_square_tauL_every_line` states all three as one conjunction. The strip
`11/2 ≤ σ < 6` is `mean_square_tauL_left_strip`, a special case.

## Proof outline

1. **Functional equation in norm form** (`norm_tauL_fe`, any σ < 12, any t):
   `|L(σ+it)| = (2π)^{2σ−12} · |Γ(12−σ+it)| / |Γ(σ+it)| · |L(12−σ+it)|`
   (Hecke FE `Λ(12−s) = Λ(s)`, `Γ(conj z) = conj Γ(z)`, `tauL_conj`).
2. **Vertical Gamma-ratio asymptotic** (`GammaAsymp.tendsto_Qr`): for real `a ≤ b`,
   `|Γ(b+it)| / (|Γ(a+it)| t^{b−a}) → 1` as t → +∞. Mathlib has no complex Stirling formula, so this
   is proved from scratch:
   * `norm_Gamma_mul_rpow_le_sharp` / `norm_Gamma_add_le_sharp`: the Gauss-product argument of
     `Stirling/GammaRatio.lean` with the telescoped defect kept. For `Re z ≥ 1`, `0 ≤ θ ≤ 1`:
     `E⁻¹ |z|^θ |Γ(z)| ≤ |Γ(z+θ)| ≤ E |z|^θ |Γ(z)|`, `E = exp(5/(Re z − ½))`. The old version had the
     fixed constant `e¹⁰`.
   * `Qr` is multiplicative, and `Qr c (c+1) t = |c+it|/t → 1`, so `Qr c (c+n) → 1` for n ∈ ℕ.
   * Write `b − a = m + r` with `0 ≤ r < 1` and shift both arguments by n:
     `Qr a b · Qr b (b+n) = Qr a (a+n) · Qr (a+n) (a+n+r) · Qr (a+n+r) (b+n)`.
     The fractional factor lies within the factor `E_n^{±1}` of `(|a+n+it|/t)^r`, where
     `E_n = exp(5/(a+n−½)) → 1` as n → ∞. Taking `tendsto_order` with n chosen per ε closes the
     argument.
   Consequence (`tendsto_chi_sq`): `|χ(σ+it)|² / t^{24−4σ} → (2π)^{4σ−24}` for σ ≤ 6.
3. **Abelian lemma** (`Abel.abel_mean`): if `g ≥ 0` is continuous with `(1/T)∫₀ᵀ g → A`, F is
   continuous with `F = g·h` on [1,∞), and `h(t)/t^α → c` (α > 0), then
   `(∫₀ᵀ F)/T^{α+1} → cA/(α+1)`. It rests on two lemmas:
   * `tendsto_weighted`: if `(∫₁ᵀ w)/T^b → W` with w ≥ 0, and ψ → c, then `(∫₁ᵀ wψ)/T^b → cW`.
   * `abel_rpow`: integration by parts gives `∫₁ᵀ g t^α = T^α G(T) − G(1) − α∫₁ᵀ t^{α−1}G`, and
     `t^{α−1}G(t) = t^α (G(t)/t)`.
4. **Assembly:** take `g(t) = |L(12−σ+it)|²`, whose mean value is `RS(2(12−σ))` by
   `mean_square_tauL_full` because 12 − σ > 6. Take `h = |χ|²` and `α = 24 − 4σ > 0`.

## Gaps / not done

* No error term: the result is the leading asymptotic only, with no `O(T^{25−4σ−δ})` bound.
* t → −∞ is not stated separately. It follows from `|L(σ−it)| = |L(σ+it)|`
  (`MeanSquareFull.norm_tauL_neg`), but the symmetric-interval version is not written out.
* The Gamma asymptotic is the modulus ratio only. There is no phase and no full complex Stirling.

## Literature

The left-of-centre mean value follows from the right-of-centre one through the functional
equation. This is classical: for ζ(s) see Titchmarsh, *Theory of the Riemann zeta-function*, §7.
For degree-2 L-functions the same argument applies to Carlson–Potter type mean values.
