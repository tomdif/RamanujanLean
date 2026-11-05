# Hafner's theorem for L(Δ,s): N₀(T) ≫ T

Module: `RamanujanTau/HardyCountHafner/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on `propext`,
`Classical.choice` and `Quot.sound`. There are no named hypotheses, no `sorry` and no
`native_decide`.

Build: `nice -n 10 lake build RamanujanTau.HardyCountHafner.Main` (exit 0). The `#print axioms`
lines are at the end of `Main.lean`.

This removes the `log log T` loss from `HardyCountLinear` (`docs/HARDY_COUNT_LINEAR.md`). The
result is J. L. Hafner's theorem (Math. Ann. 264, 1983) for Δ, the analogue of
Hardy–Littlewood (1921) for ζ.

## Headlines (`namespace RamanujanTau.HardyCountHafner`)

```lean
theorem tauL_critical_zeros_linear : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
    (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) ∧ c * T ≤ S.card

theorem heckeLambda_critical_zeros_linear -- the same count for Λ(Δ, 6+it)

/-- uniform mean square near the critical line (new analytic input) -/
theorem mean_square_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (((6 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C * T / x

/-- averaged horizontal contour sides -/
theorem horizontal_mean {σ₁ : ℝ} (h7 : 7 ≤ σ₁) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), Fh σ₁ t ≤ C * T
-- Fh σ₁ t = ∫ σ in 6..σ₁, ‖tauL (σ + t * I)‖
```

`S` is a set of distinct ordinates, so multiplicity is ignored. The constant `C` in
`mean_square_uniform` does not depend on `x`. That uniformity is exactly what the fixed-σ
Carlson–Potter limit (`MeanSquareFull`) lacks. The order `T/x` is sharp for `x ≥ 1/log T`.

## Which averaged estimate is needed

In `HardyCountLinear` the window length is `R ≍ κ²`. The only place `κ` enters is that the
horizontal sides of the contour must be small for the window around `t₀`. Steps 1 and 3 of that
proof (the Schur mean square of `Iw`, and the sign argument) already balance with `R` a large
constant. So what is needed is this:

* for all `t₀ ∈ [T,2T]` outside a set of measure `≤ T/4`, the window
  `[t₀−r, t₀+r]` satisfies `∫_{t₀−r}^{t₀+r} |L(6+it)| dt ≥ r`, where `r` is a constant.

The rectangle `[6,σ₁]×[t₀−r,t₀+r]` with no kernel (`Window.window_lower`) gives
`∫|L(6+it)| ≥ (3/4)(2r) − F(t₀−r) − F(t₀+r)`, where `F(c) = ∫_6^{σ₁}|L(σ+ic)|dσ`. By Chebyshev,
it is enough to have the **L¹ area bound** `∫_T^{2T} F ≪ T`. This is weaker than the mean-square
bound `∫|∫L dσ|² ≪ T`. Writing `x = σ − 6`, the area bound follows from any uniform estimate

    ∫_T^{2T} |L(6+x+it)|² dt ≤ C T x^{−θ},  θ < 2,

by the pointwise AM–GM inequality `|L| ≤ √x|L|² + 1/√x` and Fubini (`Horizontal.mean_abs_near`).
With `θ = 1` this gives `∫_T^{2T}|L(σ+it)|dt ≤ (C+1) T x^{−1/2}`, and `∫_6^7 x^{−1/2} = 2`.

A `log T` loss would not be enough. Any bound of the form `M(σ) ≤ T^{1+a(x)}` with
`a(x) > 0` would not be enough either. A critical-line bound `∫|L(6+it)|² ≪ T log T` alone
does not suffice. What is needed is the `1/x` decay off the line. In particular, a
`T(log T)^c` uniform bound would only give a window of length `≍ log log log T`.

## Proof of the uniform mean square (no approximate functional equation)

`Fourier.lean`, `Schur.lean`, `MeanSquare.lean`. Fix `σ = 6+x` with `0 < x ≤ 1`,
`β = π/2 − 1/T` and `c = cos β`.

1. **Fourier representation** (`Fourier.Fs_eq_fI`). Here
   `Φ_σ(w) = ∫ Λ(σ+it)e^{−itw}dt` is holomorphic on `|Im w| < π/2`. Mellin inversion on
   `Re s = σ` gives `Φ_σ(u) = 2π e^{σu}Δ(ie^u)`, and the identity theorem extends this to the
   strip. Fourier inversion (`Continuous.fourierInv_fourier_eq`) then gives
   `Λ(σ+it)e^{βt} = ∫ Φ_σ(−2πξ+iβ) e^{−2πiξt} dξ`.
2. **One modular bound** (`exists_Delta_bound_exp`). The quantity `|Δ(τ)|(Im τ)⁶e^{π Im τ}` is
   bounded on ℍ (from `exists_Delta_bound` and the cusp decay). With `v = c e^u` this gives
   `|Φ_σ(u+iβ)| ≤ 2πM c^{−6} e^{xu} e^{−πc e^u}`.
3. **Explicit majorant** (`kf_le`). We have
   `e^{xu}e^{−πce^u} ≤ 3c^{−x}/(1+(x(u+log c))²)`. To the left of `u = −log c` this follows from
   `e^{−a} ≤ 3/(1+a²)`. To the right it follows from `e^{−πe^w} ≤ e^{−π(1+w)}`. The majorant is
   a Lorentzian with sup `≍ c^{−6−x}` and integral `≍ c^{−6−x}/x`.
4. **Schur test** (`Schur.integral_tri_norm_fI_sq_le_gen`, a generalisation of
   `HardyCountLinear.Mean`). It gives `∫ tri_T(t−3T/2)|F|² ≤ (sup k)(∫k) T`, and hence
   `∫_T^{2T}|Λ(σ+it)|²e^{2βt} ≤ (6πM c^{−6−x})²/x` (`mean_sq_Fs`).
5. **Stirling from below** (`Fs_lower`). On `[T,2T]`,
   `|Λ(σ+it)|e^{βt} ≥ c_H T^{11/2+x}|L(σ+it)|`. Then `c = sin(1/T) ≥ 2/(πT)`, and the powers
   `T^{12+2x}` and `T^{11+2x}` cancel to leave `C T/x`.

This is the Plancherel (Hecke–Hafner) route. The mean square of `L` near the line is read off
from `Δ` on a ray close to the real axis, and the bound `|Δ|(Im τ)⁶ ≪ 1` is sharp on average.

## Assembly (`Main.core_count_linear`)

Take `σ₁` with `|L(σ₁+iy)−1| ≤ 1/4` (`HardyCountLinear.norm_tauL_sub_one_le`). Put
`r = 256π¹⁴M²e⁶/c_Z² + 128C + 1`, a constant, and `α = π/2−1/T`.

* Upper bound: `∫_T^{2T} Iw(α,2r,·)² ≤ 4S²(2r)³ ≤ A²T/4`, where `A = r e^{−3}c_Z(T/2)^{11/2}·r`.
  This uses `HardyCountLinear.mean_sq_Iw` unchanged.
* Exceptional set: `E = {t₀ : F(t₀±r) ≥ r/4}`. By Chebyshev and `integral_shift_le`
  (`∫_T^{2T}F(t±r) ≤ 4CT`), we get `|E ∩ [T,2T]| ≤ 32CT/r ≤ T/4`.
* Lower bound: for `t₀ ∉ E`, `window_lower` gives `∫_{t₀−r}^{t₀+r}|L(6+it)| ≥ r`. If `Z` has no
  zero within `2r` of `t₀`, then `HardyCountLinear.Iw_lower` gives `|Iw(t₀)| ≥ A`.
* Count: `Count.many_zeros_of_mean_sq_exc` (Chebyshev, the exceptional set and covering) gives
  `≥ T/(8r)` zeros in `(0,3T]`. Rescaling, `c = 1/(24r)`.

## Files

| file | content |
|---|---|
| `HardyCountHafner/Schur.lean` | `continuous_fI_gen`, `integral_tri_norm_fI_sq_le_gen` |
| `HardyCountHafner/Fourier.lean` | `Zs`, `norm_Zs_le`, `Zs_decay`, `Phis`, `Gs`, `differentiableOn_Phis`, `Phis_eq_real`, `Phis_eq_strip`, `Fs`, `gS`, `fourier_Fs`, `Fs_eq_fI` |
| `HardyCountHafner/MeanSquare.lean` | `exists_Delta_bound_exp`, `norm_Gs_le`, `exp_neg_le_three_div`, `kf_le`, `integral_lorentz`, `mean_sq_Fs`, `cH`, `Fs_lower`, `mean_square_uniform` |
| `HardyCountHafner/Horizontal.lean` | `Fh`, `continuous_Fh`, `mean_abs_near`, `horizontal_mean` |
| `HardyCountHafner/Window.lean` | `window_lower` (rectangle, no kernel) |
| `HardyCountHafner/Count.lean` | `many_zeros_of_mean_sq_exc` |
| `HardyCountHafner/Main.lean` | `vol_ge_le`, `integral_shift_le`, `core_count_linear`, headlines |

Reused: `HardyCountLinear` (`Mean`: `ph`, `fI`, `norm_fI_le`, `norm_integral_tri_ph_le`;
`Windows`: `Iw`, `mean_sq_Iw`, `Iw_lower`; `Kernel.norm_tauL_sub_one_le`; `Main.inv_cos_pow_le`),
`HardyZeros` (`Fourier`, `Cusp`: `Dc_of_im_pos`, `Delta_cusp_bound`, `im_exp_mul_I_pos`, strip
lemmas), `HardyCount` (`Triangle`, `exists_Delta_bound`, `tauL_right_half_bound`, `cZ`,
`tauL_zero_of_Zr_zero`), `Stirling` (`norm_Gamma_le_stirling`, `stirling_le_norm_Gamma`),
`HeckeConvex.tauL_bounded_of_gt`, and Mathlib Fourier inversion and Mellin inversion.

## Not done / possible extensions

* The critical line itself (`x = 0`), that is the Good/Rankin bound `∫_T^{2T}|L(6+it)|² ≪ T log T`.
  The same proof would apply, with the region `e^u ≤ 1/c` treated by `Δ(−1/τ) = τ¹²Δ(τ)`
  (`HardyZeros.Dc_S`) in place of the sup bound. It is not needed for Hafner, and it is not formalized.
* Explicit constants are not optimised, so the `c` in `N₀(T) ≥ cT` is tiny.
* The method should transfer to any level-1 cusp form via `HardyZerosGeneral` / `HeckeConvexGeneral`.

## Literature

- G. H. Hardy, J. E. Littlewood, Math. Z. 10 (1921): `N₀(T) ≫ T` for ζ.
- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983): `N₀(T) ≫ T` for holomorphic cusp forms.
- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29
  (1982): `∫|L(1/2+it)|² ~ cT log T`.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §10.7.
