# The Riemann–von Mangoldt formula for L(Δ,s)

Lean: `RamanujanTau/ZeroCountRvM/*.lean`, namespace `RamanujanTau.ZeroCountRvM`.
Build: `nice -n 10 lake build RamanujanTau.ZeroCountRvM.Main` exits 0. The module is not
imported from `RamanujanTau.lean`.

**Evidence level (1).** The results are in Lean and axiom-clean. Every headline prints
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `native_decide`, no new
`axiom` and no named hypothesis.

## Headline statements

`zeroCount T = N(T)` is the existing definition from `RamanujanTau/ZeroCount`: the number of zeros
of `L(Δ,s) = Σ τ(n) n^{-s}` with `0 < Im ≤ T`, counted with multiplicity. All of these zeros lie
in `11/2 < Re < 13/2`.

```lean
-- RvM.lean
theorem riemann_von_mangoldt : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    |(zeroCount T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T
theorem zeroCount_ge_T_log_T : ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    T / (2 * π) * Real.log T ≤ zeroCount T
theorem rvm_nonordinate : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    (∀ u : ℂ, tauL u = 0 → 11 / 2 < u.re → u.re < 13 / 2 → u.im ≠ T) →
    |π * (zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π))| ≤ C * Real.log (T + 5)
```

So `N(T) = (T/π) log(T/(2πe)) + O(log T)`. This is outcome (A) of the brief, the full asymptotic
of Iwaniec–Kowalski Thm 5.8. For degree 2 and conductor 1 the main term is
`(1/π)(Im log Γ(6+iT) − T log 2π)`, and `Im log Γ(6+iT) = T log T − T + O(log T)`.

## Infrastructure proved here, reusable beyond this module

| file | statement |
|---|---|
| `RectInv` | `rectInt_inv_of_mem`: `∮_{∂R} dz/(z−u) = 2πi` for `u` in the open rectangle; `rectInt_inv_of_not_mem`: the integral is `0` for `u` outside the closed rectangle |
| `ArgPrinciple` | `arg_principle_rect`: **argument principle on rectangles** for an entire `F ≢ 0` with no boundary zeros, `∮ F'/F = 2πi Σ_{ρ inside} ord_ρ F` |
| `LogGamma` | `Gamma_eq_exp_LG`: Weierstrass `log Γ` on `Re s > 0`; `digamma_eq_series`: `ψ(s) = −γ − 1/s + Σ (1/(j+1) − 1/(s+j+1))` |
| `DigammaAsymp` | `digamma_eq_log_add`: `ψ(s) = log s + Σ_j (log(1+1/(s+j)) − 1/(s+j))`; `norm_digamma_six_sub_log_le`: `‖ψ(6+iy) − log(6+iy)‖ ≤ 40/(5+|y|)`; `integral_re_digamma_six`: `|∫₀ᵀ Re ψ(6+iy) dy − (T log T − T)| ≤ 40 log(T+5) + 30` |
| `ArgCount` | `abs_im_integral_logDeriv_le`: `|Im ∫ₐᵇ f'/f| ≤ π(#S + 1)` when every zero of `Re f` lies in the finite set `S` |
| `Backlund` | `backlund`: `|Im ∫₆^{σ₁} L'/L(x+iT) dx| ≤ C log(|T|+2)` |
| `Symmetry` | `pi_count_eq`: `π · Σ_{ρ ∈ R} ord_ρ Λ = Re ∫₀ᵀ φ(σ₁+iy) dy − Im ∫₆^{σ₁} φ(x+iT) dx` with `φ = Λ'/Λ` |
| `Decomp` | `phi_eq`: `φ = −log 2π + ψ + L'/L`; `gamma_cauchy`; `sum_order_eq_zeroCount` |

## Proof

1. **Argument principle.** Apply it to `Λ = heckeLambda`, which is entire, on
   `R = [12−σ₁, σ₁] × [0, T]`. Here `σ₁ ≥ 7` is the line where `Re L(σ₁+iy) ≥ 1/2`
   (`HardyCount.re_tauL_right_ge`), and `T` is not an ordinate.
   - The bottom edge sits on the real axis, where `Λ > 0` (`heckeLambda_pos`).
   - The side edges lie outside the strip.
   - The argument principle itself is proved from Mathlib's `MeromorphicOn.extract_zeros_poles`.
     It gives `F = ∏(z−u)^{ord_u} · g` near the boundary, with `g` zero-free. Cauchy's theorem
     (`integral_boundary_rect_eq_zero_of_differentiableOn`) kills `∮ g'/g`. Each `∮ 1/(z−u)` is
     evaluated side by side with a branch `log(e(z−u))`, `e ∈ {±1, ±I}`.
2. **Symmetry.** The relations `Λ(12−s) = Λ(s)` and `Λ(s̄) = conj Λ(s)` give `φ(12−s) = −φ(s)`
   and `φ(s̄) = conj φ(s)`. Consequently the bottom edge contributes `0`, the left edge contributes
   `−conj` of the right edge, and the left half of the top edge contributes `−conj` of its right
   half. Together this gives `πN(T) = Re V − Im H`.
3. **Decomposition.** On `Re s > 0`, `Λ = (2π)^{−s} Γ(s) L(s)`. Cauchy's theorem for `ψ` on
   `[6,σ₁] × [0,T]` (with `ψ` real on the real axis) moves the whole Gamma contribution to
   `∫₀ᵀ Re ψ(6+iy) dy`.
4. **Stirling for arg Γ.** Build `LG = −γs − log s + Σ (s/(j+1) − log(1+s/(j+1)))`. Show
   `exp LG = Γ` from Mathlib's `GammaSeq_tendsto_Gamma`. Differentiate termwise with
   `hasSum_deriv_of_summable_norm`. Compare the digamma partial sums with the telescoping
   `Σ log(1+1/(s+j)) = log(s+N) − log s`. Then `|Re ψ(6+iy) − ½ log(36+y²)| ≤ 40/(5+|y|)`, and
   `½ log(36+y²)` has the explicit antiderivative `(y/2)log(36+y²) − y + 6 arctan(y/6)`.
5. **L'/L terms.**
   - On the vertical edge `Re L ≥ 1/2`, so `log L` is a primitive there. This contribution is
     `≤ π`.
   - On the top edge `[6, σ₁]`, use **Backlund's method**. The function
     `g(z) = (L(z+iT) + L(z−iT))/2` is entire and satisfies `g(x) = Re L(x+iT)`.
   - Jensen's inequality (Mathlib `AnalyticOnNhd.sum_divisor_le`, on the discs
     `|z−σ₁| ≤ σ₁−6 < σ₁−5`) bounds the zeros of `Re L(x+iT)` by `O(log T)`.
   - `ArgCount` uses those zeros to split `[6,σ₁]` into pieces where `±L` has `Re ≥ 0`. On each
     piece the argument changes by at most `π`.
6. **General T.** Pick a non-ordinate `T' ∈ (T, T+1)`; the ordinates in the window are finite by
   `zeroSet_finite`. Then use `N(T) ≤ N(T') ≤ N(T+1) ≤ N(T) + O(log T)` (`zeroCount_window`).
   The main term changes by `O(log T)` between `T` and `T'`.

## What is not proved (gaps)

- The constant `C` is existential and ineffective. It inherits `σ₁` (an existential line with
  `Re L ≥ 1/2`), the convexity constant from `HeckeConvex`, the Euler-product constant and the
  window constant.
- There is no `S(T)` refinement: no `S(T) = O(log T / log log T)` and no mean values of `S(T)`.
- The asymptotic ratio `N(T) / ((T/π) log T) → 1` is not stated as a `Tendsto`. It is immediate
  from `riemann_von_mangoldt`.

## Literature

- Iwaniec–Kowalski, *Analytic Number Theory*, Thm 5.8.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §9.2–9.4: the argument principle and
  Backlund's lemma.
- Whittaker–Watson §12.1–12.3: the Weierstrass product and the digamma series.
