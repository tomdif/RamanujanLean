# A quantitative Hardy theorem for L(Δ,s): N₀(T) ≫_ε T^{1/2−ε}

> **Current status (2026-11-12).** `HardyCountHafner.tauL_critical_zeros_linear` proves `N₀(T) ≫ T` unconditionally; see [HARDY_COUNT_HAFNER](HARDY_COUNT_HAFNER.md). The stronger positive-proportion bound remains conditional on Deligne; see [HAFNER_PROPORTION](HAFNER_PROPORTION.md).
> The earlier checkpoints and gap lists below describe the development at that stage.

Module: `RamanujanTau/HardyCount/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on `propext`,
`Classical.choice` and `Quot.sound`. There are no named hypotheses, no `sorry` and no
`native_decide`.

Build: `nice -n 10 lake build RamanujanTau.HardyCount.Main` (exit 0). The `#print axioms` lines
are at the end of `Main.lean`.

## Headlines (`namespace RamanujanTau.HardyCount`)

```lean
-- zeros in short intervals: the gaps between ordinates are ≪_ε t^{1/2+ε}
theorem tauL_critical_zero_gaps {ε : ℝ} (hε : 0 < ε) :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 ≤ T₀ ∧ ∀ t₀ : ℝ, T₀ ≤ t₀ →
      ∃ t ∈ Icc (t₀ - K * t₀ ^ (1 / 2 + ε)) (t₀ + K * t₀ ^ (1 / 2 + ε)),
        tauL (6 + t * I) = 0

-- counting: N₀(T) ≫_ε T^{1/2−ε}
theorem tauL_critical_zeros_count {ε : ℝ} (hε : 0 < ε) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 / 2 - ε) ≤ S.card

theorem heckeLambda_critical_zeros_count -- the same count for Λ(Δ, 6+it)
theorem tauL_critical_zeros_count_quarter -- the instance ε = 1/4: |S| ≥ c T^{1/4}
```

`tauL` is the entire continuation of `L(Δ,s) = Σ τ(n) n^{-s}`, and `heckeLambda` is
`Λ(s) = (2π)^{-s} Γ(s) L(Δ,s)`. The count is the number of distinct ordinates
`t ∈ (0,T]` with `L(Δ, 6+it) = 0`, with multiplicity ignored.

Supporting results: `tri_inversion` and `integral_triHat` (Fourier pair for the triangle),
`abs_integral_Zr_exp_tri_le` (the window bound), `norm_integral_tauL_ge` (the contour lower bound),
`Zr_zero_near` (the gap theorem for `Z`).

## Proof

Write `Z(t) = Λ(6+it)`, which is real and even (`HardyZeros`). Fix `t₀` and `h`, and suppose
`Z` has no zero on `[t₀−h, t₀+h]`.

1. **Triangle window** (`Triangle.lean`). Let `tri_h(v) = max(0, h−|v|)`. Its Fourier transform is
   `𝓕tri_h(ξ) = 2∫₀ʰ cos(2πξv)(h−v)dv = 2(1−cos 2πξh)/(2πξ)²`. This is nonnegative and bounded
   by `(4h²+2)/(1+ξ²)`. Mathlib's Fourier inversion then gives
   `tri_h(v) = ∫ 𝓕tri_h(ξ) e^{2πiξv} dξ`, and in particular `∫ 𝓕tri_h = h`.
2. **Window bound** (`Window.lean`). Let `0 ≤ α < π/2`. By Fubini,
   `∫ Z(t)e^{αt}tri_h(t−t₀)dt = ∫ 𝓕tri_h(ξ) e^{−2πiξt₀} Φ(−2πξ+iα) dξ`. Here
   `Φ(w) = ∫ Z(t)e^{−itw}dt = 2π e^{6w}Δ(ie^w)` on the strip (`HardyZeros.Phi_eq_strip`).
   Set `z = ie^w`, so `Im z = e^{Re w}cos α`. Then `|e^{6w}Δ(z)| = (Im z)⁶|Δ(z)|/cos⁶α ≤ M/cos⁶α`,
   where `M = sup (Im τ)⁶|Δ(τ)|` (Mathlib `CuspFormClass.exists_bound`). Since `𝓕tri ≥ 0`,
   `|∫ Z e^{αt} tri_h(t−t₀)| ≤ 2πMh/cos⁶α`.
3. **Sign.** `Z` has no zeros on the window, so by the intermediate value theorem it has one sign
   there, and the left side equals `∫|Z|e^{αt}tri_h(t−t₀)`. Take `α = π/2 − 1/t₀`. Then
   `cos α = sin(1/t₀) ≥ 2/(πt₀)`, so the upper bound is `≤ 2πMh(πt₀/2)⁶`.
4. **Lower bound.** On `|t−t₀| ≤ h/2`, the window satisfies `tri_h ≥ h/2` and
   `e^{αt} ≥ e^{πt/2}e^{−2}`. The Stirling lower bound (`Stirling.stirling_le_norm_Gamma`) gives
   `|Z(t)|e^{πt/2} ≥ c_Z t^{11/2}|L(Δ,6+it)|` (`Zr_lower`). Hence
   `∫|Z|e^{αt}tri_h ≥ (h/2)e^{−2}c_Z(t₀/2)^{11/2} |∫_{t₀−h/2}^{t₀+h/2} L(Δ,6+it)dt|`.
5. **Contour** (`Contour.lean`). On a line `Re s = σ₁`, with `σ₁` large, we have
   `Σ_{n≥2}|τ(n)|n^{−σ₁} ≤ 1/2`, so `Re L ≥ 1/2` there. Convexity holds uniformly for `σ ≥ 6`:
   `|L(σ+it)| ≤ C(1+|t|)^{1/2+ε}` (from `HeckeConvex.fC_bound`, `tauL_line`, `tauL_bounded_of_gt`).
   Cauchy's theorem on the rectangle `[6,σ₁]×[a,b]` (Mathlib
   `integral_boundary_rect_eq_zero_of_differentiableOn`) then gives
   `|∫ₐᵇ L(Δ,6+it)dt| ≥ (b−a)/2 − K₁(1+b)^{1/2+ε}`.
6. **Compare.** Steps 3–5 give `h/2 − K₁(3t₀)^{1/2+ε} ≤ C t₀^{1/2}`. This is false for
   `h = K t₀^{1/2+ε}` with `K` large, which proves `Zr_zero_near`. The windows are disjoint, with
   centres `T/2 + 3wj` (`w = K T^{1/2+ε}`, `j < ⌊T/6w⌋`), so `(0,T]` contains
   `≥ T^{1/2−ε}/(12K)` distinct zeros.

This method needs no finite differences: compare the qualitative `HardyZeros/Abstract.lean`. It
is localized, because the window bound holds for every centre, so every short interval contains a
zero. That is stronger than an average statement.

## Where the exponent 1/2 comes from, and what ≫ T would need

There are two losses, each of size `t^{1/2}`:

* **Upper side.** Step 2 uses only the sup-norm bound `(Im τ)⁶|Δ| ≤ M`. Hardy–Littlewood's
  `≫ T` uses an **L²/Parseval average over t₀**: `∫ |∫ Z e^{αt} tri_h(t−t₀)dt|² dt₀ ≪ h t₀¹²`,
  which corresponds to `h^{1/2} t₀⁶` per window instead of `h t₀⁶`. That gives a bound for most
  windows but not for all of them. Plancherel exists in Mathlib only on `L²` as an abstract
  isometry. It is not linked to the integral Fourier transform of `L¹∩L²` functions, so this step
  would need either that link or a direct Fejér-kernel autocorrelation computation.
* **Lower side.** Step 5 bounds the horizontal sides of the rectangle pointwise by convexity, which
  costs `(1+t)^{1/2+ε}`. For `≫ T` one needs these sides to be `O(1)` on average over `t₀`, that
  is, mean-square bounds `∫_T^{2T} |∫_6^{σ₁} L(σ+it)dσ|² dt ≪ T`. Those need mean values of
  `L(Δ,σ+it)` that are uniform as `σ → 6⁺`. The repository's `MeanSquareFull` gives the
  Carlson–Potter limit for each fixed `σ > 6`, but not uniformly in `σ`.

Each improvement alone leaves the exponent at 1/2, because the other loss remains. Both together
would give Hafner's `N₀(T) ≫ T` (Hafner 1983). Positive proportion (Hafner 1987, after Selberg)
would additionally need mollifiers.

## Files

- `RamanujanTau/HardyCount/Triangle.lean`: `tri`, `triHat`, `fourier_triC`, `tri_inversion`,
  `integral_triHat` (imports only Mathlib)
- `RamanujanTau/HardyCount/Window.lean`: `exists_Delta_bound`, `norm_Gc_le`,
  `integral_Zc_exp_tri`, `abs_integral_Zr_exp_tri_le`
- `RamanujanTau/HardyCount/Contour.lean`: `re_tauL_right_ge`, `tauL_right_half_bound`,
  `norm_integral_tauL_ge`
- `RamanujanTau/HardyCount/Gaps.lean`: `const_sign`, `abs_integral_eq_of_sign`, `Zr_lower`,
  `Zr_zero_near`
- `RamanujanTau/HardyCount/Main.lean`: gap and counting headlines

## Literature

- G. H. Hardy, J. E. Littlewood, *The zeros of Riemann's zeta-function on the critical line*,
  Math. Z. 10 (1921): `N₀(T) ≫ T` for ζ, and every interval `[T, T+T^{1/4+ε}]` contains a zero.
- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983): `N₀(T) ≫ T` for holomorphic cusp forms. Hafner, Invent. Math. 1987, gives
  positive proportion for Maass forms.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §§10.5–10.7. The present argument is
  the "every window" variant of Hardy's method with a Fejér window.
