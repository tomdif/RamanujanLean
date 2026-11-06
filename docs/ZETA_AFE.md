# An approximate functional equation for |ζ(1/2+it)|², and Ingham's theorem

Lean: `RamanujanTau/ZetaAFE/` (12 files, about 2670 lines). Build with
`nice -n 10 lake build RamanujanTau.ZetaAFE.Main`, which exits 0. There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. `#print axioms` on all 13 listed results
gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1)** for everything in §1.
The directory is not imported by `RamanujanTau.lean`.

## 1. Statements (namespace `RamanujanTau.ZetaAFE`)

```lean
-- Ingham (1926), with error O_ε(T^{1/2+ε})
theorem zeta_mean_square_ingham {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 8 ≤ T →
      |(∫ t in (0:ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2) -
        (T * Real.log (T / (2 * Real.pi)) + (2 * Real.eulerMascheroniConstant - 1) * T)| ≤
        C * T ^ (1 / 2 + ε)

theorem zeta_mean_square_ingham_littleo :
    Tendsto (fun T => ((∫ t in 0..T, ‖ζ(1/2+tI)‖²) - (T log(T/2π) + (2γ−1)T)) / T) atTop (𝓝 0)

-- the same with any exponent c ∈ (1/2, 1]   (zsq t = ‖ζ(1/2+tI)‖², ellT T = log(T/2π))
theorem ingham_rpow {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ C, ∀ T, 8 ≤ T → |(∫ t in 0..T, zsq t) - (T * ellT T + (2γ - 1) * T)| ≤ C * T ^ c

-- smoothed AFE with explicit main term
theorem zeta_afe {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ t, 8 ≤ t →
      ‖(‖ζ(1/2+tI)‖² : ℂ) - ∑' p : ℕ × ℕ, bterm t (Real.log (t / (2π))) p‖ ≤ C * t ^ (c - 1)
theorem bterm_eq (t ℓ) (p) : bterm t ℓ p =
    ((m n)^{-1/2} : ℝ) * cexp (t I (log n − log m)) * V (log (m n) − ℓ)      -- m = p.1+1, n = p.2+1

-- exact AFE (the contour identity, before any Γ-estimate)
theorem afe_exact {t c} (hc : 1/2 < c) (hc1 : c ≤ 1) (hRc : Continuous fun y => Rt t (c + y I))
    (hR : ∀ y, ‖Rt t (c + y I)‖ ≤ KR * exp (y²/2)) :
    π * ‖ζ(1/2+tI)‖² = ∑' p : ℕ × ℕ, ∫ y, afeTerm t c p y
```

Here `V(L) = ∫_{u>L} e^{−u²/4}/√π du = erfc(L/2)` (so `V(−∞) = 2`, `V(0) = 1`, `V(+∞) = 0`), and
written out,

    |ζ(1/2+it)|² = Σ_{m,n≥1} (mn)^{−1/2} (n/m)^{it} erfc( log(mn/τ)/2 ) + O_c(t^{c−1}),   τ = t/2π.

The hypotheses of `afe_exact` are discharged by `continuous_Rt_line` and `gamma_ratio_line`.

Reusable byproducts (all level 1):

| theorem | statement |
|---|---|
| `line_gauss` | `∫_ℝ e^{(c+iy)²−(c+iy)L}/(c+iy) dy = π V(L)` for `c > 0` |
| `afe_line` | for entire even `F` with `‖F(x+iy)‖ ≤ K e^{y²/2}` on `|x| ≤ c`: `∫_ℝ F(c+iy) e^{(c+iy)²}/(c+iy) dy = π F(0)` |
| `Xi_one_sub`, `Xi_eq_zeta`, `norm_Lambda0_le` | `Ξ(s) = s(1−s)Λ₀(s) − 1` is entire, `Ξ(1−s) = Ξ(s)`, `Ξ = s(1−s)Γ_ℝ(s)ζ(s)` on `Re s > 0`; `‖Λ₀(s)‖ ≤ B₀` on `−1 ≤ Re s ≤ 2` |
| `norm_digamma_sub_log_le` | `‖ψ(s) − log s‖ ≤ 40/(Re s + |Im s| − 1)` (`Re s > 0`) |
| `norm_E_le`, `Rt_decomp` | `R_t(z)(t/2π)^{−z} = Q_t(z) e^{E_t(z)}`, `‖E_t(c+iy)‖ ≤ 200(1+|y|)²/t` for `|y| ≤ t/4`, `t ≥ 8` |
| `gamma_ratio_line` | `‖R_t(c+iy)(t/2π)^{−c−iy} − 1‖ ≤ K e^{y²/2}/t` for all `y`, `t ≥ 8` |
| `abs_Hv_sub_le` | `|H_{⌈e^v−1⌉} − v − γ| ≤ (2+|v|)e^{−v}` for all real `v` |
| `abs_Dsum_sub_le` | `|Σ_n V(2 log n − ℓ)/n − ℓ − 2γ| ≤ A (1+|ℓ|) e^{−ℓ/2}` |
| `norm_integral_osc_le` | first-derivative test for an increasing weight: `|∫_a^T e^{itλ} V(Λ − log(t/2π)) dt| ≤ 2V(Λ − log(T/2π))/|λ|` |
| `norm_integral_bterm_off` | off-diagonal pair bound `≤ 4 (T/2π)^c φ(m,n)`, with `Σ φ = 2 Z_{1/2+c}²` (`tsum_phiO`) |

## 2. Choice of AFE, and the proof

**Which AFE.** Neither of the two suggested forms is used: the smoothed AFE for `ζ(s)` and the
Hardy–Littlewood sharp-cut AFE both bring in the factor `χ(1/2+it)`. Its cross terms
`χ·Σ m^{−s} Σ n^{−s}` need the phase of `χ` (Riemann–Siegel θ) to second order, plus a
stationary-phase or second-derivative test. The AFE used here is for the product `ζ(s)ζ(1−s)`
itself:

    Φ_t(z) = Ξ(1/2+z+it) Ξ(1/2+z−it),     Ξ(s) = s(1−s)Λ(s)   (entire).

Since `Ξ(1−s) = Ξ(s)`, `Φ_t` is **even** in `z`. That one symmetry plays the role of the functional
equation, and **no χ appears anywhere**. With the weight `e^{z²}/z`:

1. `afe_line`: `h(z) = (Φ(z) − Φ(0)) e^{z²}/z` (via `dslope`) is entire and odd on the lines
   `Re z = ±c`. Cauchy on `[−c,c]×[−Y,Y]` with `Y → ∞` gives `∫_{(c)} h = 0`, and
   `∫_{(c)} e^{z²}/z = π` (`line_gauss` at `L = 0`). The growth bound `|Ξ| ≪ |s|²` on the strip
   comes from Riemann's formula `Λ₀(s) = (M(s/2) + M((1−s)/2))/2` (`GORZXi.completedRiemannZeta₀_eq`),
   with `M` the Mellin transform of a function supported on `t > 1`.
2. On `Re z = c ∈ (1/2, 1]`, expand `ζ(s₊)ζ(s₋)` as a double Dirichlet series and interchange it
   with the integral (`afe_exact`). Divide by `G₀ = g(1/2+it)g(1/2−it)`, where `g(s) = s(1−s)Γ_ℝ(s)`,
   using `ζ(s̄) = conj ζ(s)` (`ZetaMeanSquare.riemannZeta_conj`).
3. **Γ-ratio** (`gamma_ratio_line`). Write `R_t(z) = g(s₊)g(s₋)/G₀`. Then
   `R_t(z)(t/2π)^{−z} = Q_t(z) e^{E_t(z)}`, where:
   - `Q_t − 1 = (z²(2t²−½)+z⁴)/(¼+t²)²`;
   - `E_t = Σ± [LG(a±(z)) − LG(a±(0))] − z log(t/2)`, using the Weierstrass `log Γ` from
     `ZeroCountRvM` and `a± = (½+z±it)/2`.

   The mean value theorem on `u ↦ E_t(uz)` together with `ψ = log + O(1/|Im|)` and
   `log a₊ + log a₋ = 2 log(t/2) + log(1+η)` gives `‖E_t‖ ≤ 200(1+|y|)²/t` for `|y| ≤ t/4`.
   For `|y| > t/4`, two crude bounds suffice: `|Γ(w)| ≤ Γ(Re w)`, and the reflection bound
   `|Γ(¼ ± it/2)|^{−1} ≤ Γ(¾) e^{πt/2}/π` (`RankinError.norm_inv_Gamma_le_left`). Everything is
   absorbed into `K e^{y²/2}/t`.
4. **Main term** (`KerI_sub_V`, `zeta_sq_approx`). Replacing `R_t(z)` by `(t/2π)^z` turns each
   kernel into `π V(log(mn) − log τ)`, by the same Laplace–Gauss computation that gives
   `line_gauss` (`e^{−zL}/z = ∫_{u>L} e^{−zu}`, Fubini, then `integral_cexp_quadratic`). The error
   for the pair `(m,n)` is `≪ (τ/mn)^c / t`. Summed over all pairs it is
   `≪ τ^c Z_{1/2+c}²/t = O(t^{c−1})`. Choosing `c > 1/2` is what makes the error summable without
   any cutoff.
5. **Diagonal** (`abs_Dsum_sub_le`). Write `V(L) = ∫ 1_{u>L} g`. Then
   `Σ_n V(2 log n − ℓ)/n = ∫ g(u) H_{k((u+ℓ)/2)} du` (Tonelli, `lt_kc_iff`). Mathlib's bounds
   `eulerMascheroniSeq k < γ < eulerMascheroniSeq' k` give `|H − v − γ| ≤ (2+|v|)e^{−v}`, and
   `∫ g(u)((u+ℓ)/2+γ) du = ℓ + 2γ`. So the diagonal is `log τ + 2γ + O_c(t^{c−1})`, and
   `∫ log(t/2π) dt = t log(t/2π) − t` produces **Ingham's second term `(2γ−1)T`**.
6. **Off-diagonal** (`norm_integral_osc_le`, `norm_integral_bterm_off`). `t ↦ V(Λ − log(t/2π))`
   is increasing, so one integration by parts gives `|∫_a^T e^{itλ}V| ≤ 2V(·,T)/|λ|`. Two further
   bounds finish it: `V(x) ≤ 2 min(1, e^{−x}) ≤ 2e^{−cx}`, and `1/|log(n/m)| ≤ n/|n−m|`. With
   `σ = ½ + c > 1` the double sum is `≤ 8 (T/2π)^c Z_σ²`. The near-diagonal needs no
   Montgomery–Vaughan inequality: the weight `(mn)^{−σ}` with `σ > 1` makes `Σ m^{−σ}|n−m|^{−σ}`
   converge.
7. **Assembly** (`ingham_rpow`). Integrate over `[8,T]`. The interchange of `∫` and `Σ'` uses
   `integral_tsum_Icc`, and continuity of the sums uses `continuousOn_tsum`. The piece
   `∫_0^8 |ζ|²` is a constant. Finally take `c = min(½+ε, 1)`.

## 3. Files

| file | content | lines |
|---|---|---|
| `Gauss.lean` | `gk`, `V` and its properties, `line_gauss`, `line_gauss_zero` | 193 |
| `Line.lean` | `integrable_line_gauss`, `afe_line` (contour identity) | 192 |
| `Xi.lean` | `Xi`, `Xi_one_sub`, `Xi_eq_zeta`, `norm_Lambda0_le`, `norm_Xi_le`, `poly_le_gauss` | 105 |
| `AFE.lean` | `sp`, `sm`, `Phi`, `gfac`, `G0`, `Rt`, `afeTerm`, `Phi_neg`, `norm_Phi_le`, `Phi_zero`, `afe_exact` | 228 |
| `Split.lean` | `KerI`, `KerI_sub_V`, `bterm`, `Zs`, `zeta_sq_approx` | 244 |
| `Digamma.lean` | `norm_digamma_sub_log_le`, `log_pair`, `Efun`, `norm_E_le` | 245 |
| `GammaBound.lean` | `Qr`, `Rt_decomp`, `gamma_ratio_near`/`_far`/`_line`, `continuous_Rt_line` | 403 |
| `Diag.lean` | `kc`, `Hv`, `abs_Hv_sub_le`, `Dsum`, `Dsum_eq_integral`, `abs_Dsum_sub_le` | 258 |
| `OffDiag.lean` | `ellT`, `fV`, `norm_integral_osc_le`, `inv_abs_lg_sub_le`, `phiO`, `tsum_phiO`, `pair_bound`, `norm_integral_bterm_off` | 283 |
| `Pointwise.lean` | `zsq`, `bo`, `Oft`, `tsum_bterm_split`, `pointwise_err`, `diag_err` | 176 |
| `Ingham.lean` | `integral_tsum_Icc`, continuity lemmas, `integral_ellT`, `ingham_rpow` | 228 |
| `Main.lean` | `zeta_afe`, `bterm_eq`, `zeta_mean_square_ingham`, `zeta_mean_square_ingham_littleo`, `#print axioms` | 111 |

Reused results:

- `ZeroCountRvM.{LG, Gamma_eq_exp_LG, hasDerivAt_LG, digamma_eq_series, digamma_eq_log_add, et, norm_et_le, tsum_inv_sq_le}`
- `GORZXi.{Aθ, convA, completedRiemannZeta₀_eq}`
- `ZetaMeanSquare.riemannZeta_conj`
- `RankinError.{norm_Gamma_le_Gamma_re, norm_inv_Gamma_le_left}`

Mathlib supplies:

- `completedRiemannZeta₀_one_sub` and `completedRiemannZeta_eq`
- `integral_boundary_rect_eq_zero_of_differentiableOn` and `integral_cexp_quadratic`
- `integral_tsum_of_summable_integral_norm`
- `eulerMascheroniSeq(')`
- `norm_image_sub_le_of_norm_deriv_le_segment'` and `integral_mul_deriv_eq_deriv_mul`

## 4. Numerics (level 4): `scripts/zeta_afe/`

- `afe_check.gp` (`nbthreads = 1`, about 20 s) compares `|ζ(1/2+it)|²` with the smoothed main term
  `Σ (mn)^{−1/2}(n/m)^{it} erfc(log(mn/τ)/2)`, truncated at `mn ≤ τe⁸`. The output is in
  `afe_check.out`.

  | t | |ζ|² | main term | difference |
  |---|---|---|---|
  | 20 | 1.31754220 | 1.31754729 | −5.1e−6 |
  | 50 | 0.11610034 | 0.11607890 | 2.1e−5 |
  | 80 | 3.88039745 | 3.88038162 | 1.6e−5 |
  | 110 | 9.38448937 | 9.38450391 | −1.5e−5 |

  The true error is far below the proved `O(t^{c−1})`. The Γ-ratio error is really `O(t^{−2})`
  pointwise, since `R_t(z)τ^{−z} − 1 = O(|z|²/t)` and the linear term averages out.
- `ingham_check.gp` computes `I(T) = ∫₀ᵀ|ζ|²` and subtracts Ingham's main term (about 3 min);
  the output is in `ingham_check.out`:

  | T | I(T) | T log(T/2π) + (2γ−1)T | difference | difference/√T |
  |---|---|---|---|---|
  | 100 | 295.635 | 292.172 | 3.46 | 0.35 |
  | 200 | 736.833 | 722.974 | 13.86 | 0.98 |
  | 400 | 1729.514 | 1723.208 | 6.31 | 0.32 |

  The earlier `scripts/zeta_critical` run gave `I(1000) = 5212.5` against
  Ingham's `5224.3`, a difference of `−11.8` (`≈ −0.37√T`), consistent with the true `O(T^{1/2})`
  size of `E(T)`.

## 5. What is not claimed, and gaps

- The error is `O_ε(T^{1/2+ε})`, not Ingham's `O(T^{1/2} log T)` and not Balasubramanian's
  `O(T^{1/3+ε})`. To get `T^{1/2} log T`, take `c = 1/2 + 1/log T`. The constants then depend on
  `c` through `Z_{1/2+c}² ≍ (log T)²` and `1/(c − 1/2)`, which would give `T^{1/2}(log T)²`. A sharper
  constant tracking, or a shift of the off-diagonal line to `c = 1/2`, would be needed. Neither is
  done.
- The AFE proved is for `|ζ(1/2+it)|²` (`zeta_afe`, smoothed, error `O(t^{c−1})` for every
  `c ∈ (1/2,1]`, so `O(t^{−1/2+ε})`). The Hardy–Littlewood AFE for `ζ(1/2+it)` itself, with `χ` and
  sharp cuts at `√(t/2π)`, is **not** formalized.
- `t ≥ 8` and `T ≥ 8` are used throughout (Stirling region and `log(t/2π) ≥ 0`); `[0,8]` enters
  only as a constant.

## 6. Literature (from memory; attributions not checked)

- A. E. Ingham, *Mean-value theorems in the theory of the Riemann zeta-function*, Proc. LMS (2) 27
  (1926): the main term `T log(T/2π) + (2γ−1)T` and the error `O(T^{1/2} log T)`.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §7.4. Ivić, *The Riemann Zeta-Function*,
  Ch. 15. The latter covers Atkinson's formula and `E(T) = O(T^{1/3+ε})` (Balasubramanian 1978).
- The symmetric `ζ(s)ζ(1−s)` AFE with a Gaussian weight is in the style of the "AFE for moments"
  (e.g. Iwaniec–Kowalski Thm 5.3; Conrey et al., the recipe for moments). This route avoids
  `χ` and stationary phase.
