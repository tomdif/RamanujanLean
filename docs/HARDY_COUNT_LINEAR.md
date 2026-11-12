# Critical zeros of L(Δ,s): N₀(T) ≫ T / log log T

> **Current status (2026-11-12).** `HardyCountHafner.tauL_critical_zeros_linear` proves `N₀(T) ≫ T` unconditionally; see [HARDY_COUNT_HAFNER](HARDY_COUNT_HAFNER.md). The stronger positive-proportion bound remains conditional on Deligne; see [HAFNER_PROPORTION](HAFNER_PROPORTION.md).
> The earlier checkpoints and gap lists below describe the development at that stage.

Module: `RamanujanTau/HardyCountLinear/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on `propext`,
`Classical.choice` and `Quot.sound`. There are no named hypotheses, no `sorry` and no
`native_decide`.

Build: `nice -n 10 lake build RamanujanTau.HardyCountLinear.Main` (exit 0). The `#print axioms`
lines are at the end of `Main.lean`.

This improves the count `N₀(T) ≫_ε T^{1/2−ε}` (`docs/HARDY_COUNT.md`) to within a `log log T`
factor of Hafner's `N₀(T) ≫ T`.

## Headlines (`namespace RamanujanTau.HardyCountLinear`)

```lean
theorem tauL_critical_zeros_loglog : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧
      c * T / Real.log (Real.log T) ≤ S.card

theorem heckeLambda_critical_zeros_loglog -- the same count for Λ(Δ, 6+it)

theorem tauL_critical_zeros_one_sub_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ^ (1 - ε) ≤ S.card
```

`S` is a set of distinct ordinates, so multiplicity is ignored.

## Proof

Write `Z(t) = Λ(6+it)`, put `α = π/2 − 1/T`, and let
`Iw(t₀) = ∫ Z(t) e^{αt} tri_R(t − t₀) dt`.

1. **Upper side, averaged over centres** (`Mean.lean`, `Windows.mean_sq_Iw`). The Fourier
   identity from `HardyCount.integral_Zc_exp_tri` gives `Iw(t₀) = ∫ g(ξ) e^{−2πiξt₀} dξ`, where
   `g = triHat_R · Φ(−2πξ+iα)` and `|g| ≤ S·triHat_R` with `S = 2πM/cos⁶α ≪ T⁶`. To bound the
   average we do not use Plancherel. Instead a Schur test with the weight `tri_T(t₀ − 3T/2)`
   applies: expand `|Iw|²`, use Fubini twice, and note that the weight's Fourier transform has
   modulus `triHat_T`. This gives
   `∫_T^{2T} Iw² ≤ 4 S² R³`. The sup bound gives `S² R⁴` per window, so the average saves a
   factor `R`. This is the first `t^{1/2}` loss of `HardyCount`, now removed.
2. **Lower side, pointwise, with a double-exponential kernel** (`Kernel.lean`). We do not average
   the horizontal sides. We take the entire kernel `ψ(z) = exp(−exp(z²))` and apply Cauchy to
   `(L(Δ,s) − 1)·ψ((s−6−it₀)/(ih))` on the rectangle `[6,σ₁]×[t₀−κh, t₀+κh]`. Here
   `‖L(σ₁+iy) − 1‖ ≤ e^{−3}/(8π)`. On thin strips we have `|ψ(x+iy)| ≤ exp(−e^{x²}/4)`. The
   horizontal sides are bounded by convexity, which gives `≪ T`, and are then killed by
   `exp(−e^{κ²}/4)`. That needs only `e^{κ²} = (log T)²`, that is `κ = √(2 log log T)`. The result is
   `h e^{−3} ≤ ∫_{t₀−κh}^{t₀+κh} |L(Δ,6+it)| dt` for every `t₀ ∈ [T,2T]`, provided `2κβ ≤ h`.
3. **Sign** (`Windows.Iw_lower`). Suppose `Z` has no zero within `R = 2κh` of `t₀`. Then
   `|Iw(t₀)| = ∫|Z| e^{αt} tri_R ≥ κh · e^{−3} c_Z (T/2)^{11/2} · h e^{−3}`. This uses Stirling
   through `HardyCount.Zr_lower`.
4. **Balance** (`Main.core_count`). The powers of `T` cancel exactly. Chebyshev then needs only
   `h ≥ Dκ`. Take `h = Hκ` and `R = 2κh ≍ log log T`. By `Count.many_zeros_of_mean_sq` (Chebyshev
   plus covering by the windows `[γ−R, γ+R]`), at most `T/2` of `[T,2T]` is free of zeros at
   distance `R`. So there are `≥ T/(4R) = T/(16 H log log T)` distinct zeros in `[T/2, 3T]`.

## Gaps: why not N₀(T) ≫ T

The remaining factor is the window length `R ≍ log log T`. It comes from killing the horizontal
sides pointwise. Pointwise they are only `≪ T` (convexity), and a kernel that is bounded and
analytic in a strip of fixed width can decay at most doubly exponentially. So `κ² ≍ log log T`
is optimal for this route. Without the double exponential (a Gaussian kernel) the same argument
gives `T/log T`.

Getting `≫ T` (Hafner 1983, the analogue of Hardy–Littlewood 1921) needs the classical
**averaged** horizontal sides:
`∫_T^{2T} |∫_6^{σ₁} L(σ+it) dσ|² dt ≪ T`. That in turn needs an approximate formula
`L(Δ,σ+it) = Σ_{n≤t} τ(n) n^{−s} + small` that is uniform as `σ → 6⁺` (an approximate
functional equation), together with `mv_poly` and Rankin–Selberg partial sums. The repo's
`MeanSquare/approx_tauL` (Riesz-smoothed Perron) and `MeanSquareFull` (fixed-σ limits, `σ > 6`)
do not give this uniformity. With that input, steps 1, 3 and 4 above carry over unchanged: the
upper side is already the averaged one, and it gives `R = O(1)`.

## Files

- `RamanujanTau/HardyCountLinear/Mean.lean`: `ph`, `fI`, `continuous_triHat`,
  `norm_integral_tri_ph_le`, and `integral_tri_norm_fI_sq_le` (the Schur/Fubini mean-square
  bound). It imports only `HardyCount.Triangle`.
- `RamanujanTau/HardyCountLinear/Kernel.lean`: `norm_tauL_sub_one_le`, `kerC`, `norm_kerC_le`,
  `exp_neg_exp_sq_le`, `main_term`, `kernel_lower`
- `RamanujanTau/HardyCountLinear/Windows.lean`: `Iw`, `gw`, `Iw_eq_fI`, `mean_sq_Iw`, `Iw_lower`
- `RamanujanTau/HardyCountLinear/Count.lean`: `many_zeros_of_mean_sq` (abstract
  Chebyshev/covering; Mathlib only)
- `RamanujanTau/HardyCountLinear/Main.lean`: `core_count` and the headlines

Reused: `HardyCount` (`tri`, `triHat`, `fourier_triC`, `integral_triHat`, `integral_Zc_exp_tri`,
`exists_Delta_bound`, `norm_Gc_le`, `tauL_right_half_bound`, `const_sign`,
`abs_integral_eq_of_sign`, `Zr_lower`, `cZ`, `tauL_zero_of_Zr_zero`) and `HardyZeros`
(`Phi_eq_strip`, `differentiableOn_Phi`, `Zr_integrable`).

## Literature

- G. H. Hardy, J. E. Littlewood, Math. Z. 10 (1921): `N₀(T) ≫ T` for ζ.
- J. L. Hafner, Math. Ann. 264 (1983): `N₀(T) ≫ T` for holomorphic cusp forms.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §§10.5–10.7. Our step 1 is the
  mean-square half of §10.7. Our step 2 replaces the approximate-formula half with an analytic
  kernel, at a cost of `log log T`.
