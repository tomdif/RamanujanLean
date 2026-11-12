# Hafner's theorem for every level-one cusp form with real coefficients: N₀(T) ≫ T

Module: `RamanujanTau/HafnerGeneral/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on `propext`,
`Classical.choice` and `Quot.sound`. There are no named hypotheses, no `sorry`, no
`native_decide` and no `axiom`.

Build: `nice -n 10 lake build RamanujanTau.HafnerGeneral.Main` (exit 0). The `#print axioms`
lines are at the end of `Main.lean`.

This closes gap (2) of `docs/GENERAL_CUSP_MOMENTS.md`. It generalizes `HardyCountHafner`
(`docs/HARDY_COUNT_HAFNER.md`, the case f = Δ) to every nonzero `f ∈ S_k(SL₂(ℤ))` with real
coefficients. The result is J. L. Hafner, Math. Ann. 264 (1983).

## Headlines (`namespace RamanujanTau.HafnerGeneral`)

```lean
theorem fL_critical_zeros_linear {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ fL f ((k : ℂ) / 2 + t * I) = 0) ∧ c * T ≤ S.card

theorem heckeLambda_critical_zeros_linear -- the same count for Λ(f, k/2+it)

/-- sanity check f = Δ -/
theorem fL_discriminant_critical_zeros_linear : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
    (∀ t ∈ S, 0 < t ∧ t ≤ T ∧
      fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I) = 0) ∧
    c * T ≤ S.card

/-- uniform off-line mean square, weight k = 2p+2 (real coefficients not needed) -/
theorem mean_square_uniform (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      ∫ t in Icc T (2 * T), ‖fL f ((((p : ℝ) + 1 + x : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ C * T / x

/-- averaged horizontal sides (real coefficients not needed) -/
theorem horizontal_mean (f) (hk : 12 ≤ 2 * p + 2) {σ₁ : ℝ} (h7 : (p : ℝ) + 2 ≤ σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ∫ t in Icc T (2 * T), Fh (fL f) ((p : ℝ) + 1) σ₁ t ≤ C * T
-- Fh g a b t = ∫ σ in a..b, ‖g (σ + t * I)‖

/-- normalisation at the far right (f ≠ 0 only) -/
theorem exists_normalized (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) {σa : ℝ}
    (hσa : ((k : ℝ) + 1) / 2 < σa) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ ∃ σ₁ : ℝ, σa ≤ σ₁ ∧ ∀ y : ℝ,
      ‖(n₀ : ℂ) ^ ((σ₁ : ℂ) + y * I) / coef f n₀ * fL f ((σ₁ : ℂ) + y * I) - 1‖ ≤ ρ
```

`S` is a set of distinct ordinates, so multiplicity is ignored. The Δ corollary is stated for
`HeckeConvexGeneral.fL Δ`. The direct `HeckeL.tauL` statement is
`HardyCountHafner.tauL_critical_zeros_linear`.

## What changed relative to the Δ proof

The Δ proof is `HardyCountHafner` plus `HardyCountLinear.{Windows,Kernel,Main}` and
`HardyCount.{Window,Contour}`. Its Δ-specific parts were replaced as follows. Internally the
weight is `k = 2p + 2` and `κ = k/2 = p + 1`. The headline reduces to this case by
`GeneralCuspMoments.exists_weight_eq`, since odd `k` and `k < 12` force `f = 0`.

1. **Fourier identity at σ = κ + x** (`Fourier.lean`). `Phis f σ w = ∫ Λ(f,σ+it)e^{−itw} dt`
   equals `2π e^{σw} f(ie^w)` on the strip (`Phis_eq_strip`, by Mellin inversion on `Re s = σ`
   and the identity theorem), for every `κ ≤ σ ≤ κ+1`. Decay comes from Stirling's upper bound
   and `|L(f,σ+it)| ≤ C(1+|t|)` (`fL_linear_growth`). For `σ ≤ (k+1)/2` this growth bound uses
   `fL_convexity_strip`, and for `σ > (k+1)/2` it uses `fL_bounded_of_gt`. Fourier inversion is
   `Fs_eq_fI`.
2. **Uniform off-line mean square** (`MeanSquare.lean`). This needs Stirling from below at a
   general σ. The `|Γ|²` product formula `GeneralCuspMoments.Gamma.norm_Gamma_sq` is exact only
   at half-integer shifts and does not apply off the line. It is not needed, because
   `Stirling.stirling_le_norm_Gamma` holds for every `σ ≥ 3/2`. The modular input is
   `GeneralCuspMoments.exists_cusp_bound` (`|f(z)| y^{p+1} ≤ M e^{−πy}`), which replaces
   `exists_Delta_bound_exp`. The Lorentzian majorant `kf_le`, `integral_lorentz` and the Schur
   bound `integral_tri_norm_fI_sq_le_gen` are reused unchanged from `HardyCountHafner`. The
   powers `T^{2p+2+2x}` and `T^{2p+1+2x}` cancel, giving `C·T/x`.
3. **Horizontal sides** (`Horizontal.lean`). `Fh` is defined for any continuous `g`. The
   AM–GM/Fubini argument covers `σ ∈ (κ, κ+1]`. For `σ ≥ κ+1 > (k+1)/2` the bound is absolute
   convergence. The repository only has absolute convergence for `σ > (k+1)/2` (Rankin–Selberg
   partial sums), which is why the split point is `κ+1` rather than something nearer the line.
4. **|L − 1| ≤ 1/4 far right: new normalisation** (`Window.lean`). For a general `f`, `a_f(1)`
   can vanish, so `L(f,s) → 1` fails. Let `n₀` be the first index with `a_f(n₀) ≠ 0`. Then
   `g(s) = n₀^s a_f(n₀)^{−1} L(f,s)` is entire and `|g(σ₁+iy) − 1| ≤ 1/4` for `σ₁` large
   (`exists_normalized`, with ratio `(n₀/(n₀+1))^K`). The rectangle lemma
   `window_lower_gen` is stated for any entire `g`. Since
   `|g(σ+it)| = n₀^σ|a_f(n₀)|^{−1}|L(f,σ+it)|`, only constants change: the horizontal sides of `g`
   are at most `n₀^{σ₁}/|a_f(n₀)|` times those of `L` (`Fh_le_of_le`), and
   `∫|L(κ+it)| = ρ₀ ∫|g(κ+it)|` with `ρ₀ = |a_f(n₀)|/n₀^κ`.
5. **The window kernel `Iw`** (`Windows.lean`). It is built on a real `Y` with `Z = Y·c` and
   `‖c‖ = 1` (`Rep`). For `k ≡ 0 mod 4`, `c = 1` and `Y = Re Z`. For `k ≡ 2 mod 4`, `c = i` and
   `Y = Im Z`, which is odd (`exists_rep`, from `HardyZerosGeneral.Zc_conj`). Then
   `|Iw| = ‖fI gw‖`, so the Schur mean square `mean_sq_Iw` (`S = 2πM/cos^{p+1}α`) and the sign
   bound `Iw_lower` (Stirling at σ = κ, `cZ p = (√π/3)e^{−10}(2π)^{−(p+1)}`) go through for
   either root number.
6. **Assembly** (`Core.lean`, `core_count_linear`). The window radius is the constant
   `r = 256π^{2p+4}M²e⁶/(c_Z²ρ₀²) + 128C + 1`, the exceptional set is handled by Chebyshev
   exactly as for Δ, and `HardyCountHafner.many_zeros_of_mean_sq_exc` gives `≥ T/(8r)` zeros of
   `Y` in `(0,3T]`. After rescaling, `c = 1/(24r)`.

The realness hypothesis enters only in step 5, through the choice of `Y`. Steps 1–4 and the
mean-square bound hold for every `f`.

## Files

| file | lines | content |
|---|---|---|
| `Fourier.lean` | 333 | `fL_linear_growth`, `Zs`, `norm_Zs_le`, `Zs_decay`, `Phis`, `Gs`, `differentiableOn_Phis`, `Phis_eq_real`, `Phis_eq_strip`, `Fs`, `gS`, `fourier_Fs`, `Fs_eq_fI` |
| `MeanSquare.lean` | 317 | `norm_Gs_le`, `mean_sq_Fs`, `cH`, `Fs_lower`, `rpow_half_sq`, `mean_square_uniform` |
| `Horizontal.lean` | 174 | `Fh` (any `g`), `continuous_Fh`, `Fh_le_of_le`, `mean_abs_near`, `horizontal_mean` |
| `Window.lean` | 180 | `window_lower_gen`, `exists_coef_ne_zero`, `exists_normalized` |
| `Windows.lean` | 393 | `integral_Zc_exp_tri` (general), `Iw`, `gw`, `norm_gw_le`, `Rep`, `Iw_eq_fI`, `mean_sq_Iw`, `cZ`, `Zc_lower`, `Iw_lower` |
| `Core.lean` | 271 | `vol_ge_le`, `integral_shift_le` (any `F`), `inv_cos_pow_le` (any power), `gN`, `norm_gN`, `core_count_linear` |
| `Main.lean` | 131 | `exists_rep`, headlines, Δ corollary, `#print axioms` |

Reused unchanged (imported, not edited): `HardyZerosGeneral` (`Zc`, `Phi`, `Gc`, `Fc`,
`Phi_eq_strip`, `Zc_conj`, `integrable_heckeLambda_line`, `strip` lemmas,
`discriminant_ne_zero'`), `HeckeConvexGeneral` (`fL`, `fL_entire`, `fL_eq_LSeries`,
`heckeLambda_eq_fL`, `fL_convexity_strip`, `fL_bounded_of_gt`, `LSeriesSummable_coef`,
`heckePair`, `coef_discriminant`), `GeneralCuspMoments` (`exists_cusp_bound`, `norm_Gc_le`,
`exists_weight_eq`, `crit_point`), `RankinSelbergGeneral.exists_coeff_ne_zero`,
`HardyCountHafner` (`kf_le`, `integral_lorentz`, `integral_tri_norm_fI_sq_le_gen`,
`many_zeros_of_mean_sq_exc`), `HardyCountLinear.Mean` (`fI`, `ph`, `norm_fI_le`,
`continuous_fI`, `integral_tri_norm_fI_sq_le`), `HardyCount` (`tri`, `triHat`,
`tri_inversion`, `const_sign`, `abs_integral_eq_of_sign`) and `Stirling`.

## Gaps / not done

* **Real coefficients are a hypothesis.** For a general `f` with complex coefficients, `Z` is
  not a fixed phase times a real function, and Hardy's sign argument does not apply. This is
  the same scope as `HardyZerosGeneral`, and Hecke eigenforms are covered.
* The constant `c` is ineffective in practice and far from optimal.
* Multiplicities are ignored, so distinct ordinates are counted.
* `HafnerGeneral.Main` is included in the root import graph and the current theorem catalog.

## Literature

- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983) 21–37.
- G. H. Hardy, J. E. Littlewood, Math. Z. 10 (1921): `N₀(T) ≫ T` for ζ.
- A. Good, Mathematika 29 (1982): `∫|L(f,k/2+it)|² ~ c_f T log T`.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §10.7.
