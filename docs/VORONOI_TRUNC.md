# The `L²`-truncated Voronoi formula for `∑_{n≤x} τ(n)`, the Cramér–Tong limit, and exact `Ω±(x^{23/4})`

Lean: `RamanujanTau/VoronoiTrunc/` (13 files, about 4860 lines). No `sorry`, no `native_decide`,
no new axiom, no named hypothesis. Build with `nice -n 10 lake build RamanujanTau.VoronoiTrunc.Main`
(exit 0). `#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
**Evidence level (1).** Deligne is not used. The public entry point is included in the `RamanujanTau.lean` import graph.

This closes gap (1) of `docs/VORONOI.md` (truncated Voronoi), the open item of
`docs/CRAMER_MEAN_SQUARE.md` (existence of `lim X^{−25/2}∫₁^X S²`), and the `23/4` gap of
`docs/TAU_OMEGA_PM.md` (which had `Ω±(x^β)` only for `β < 28/5`).

## 1. Statements

`S(x) = ∑_{1≤n≤x} τ(n)`, `B = ∑ τ(n)² n^{−25/2} = 1.5828…`.

```lean
-- namespace RamanujanTau.VoronoiTrunc   (Main.lean)
theorem voronoi_truncated_L2 {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2) /
        X ^ (25 / 2 : ℝ)) atTop (𝓝 0)

theorem voronoi_truncated_L2_rate {θ} (hθ0 : 0 < θ) (hθ : θ ≤ 1/4) : ∃ C ≥ 0, ∀ X ≥ 144,
    ∫ x in X..2X, (S x − V_{⌊X^θ⌋} x)^2 ≤ C X^{25/2} (X^{−1/16} + ∑_{n > ⌊X^θ⌋} τ(n)² n^{−25/2})

theorem tau_cramer :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2) /
        X ^ (25 / 2 : ℝ)) atTop
      (𝓝 ((∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (50 * π ^ 2)))

theorem tau_omega_pm_exact {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ (23 / 4 : ℝ) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ∧
      (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) < -c * x ^ (23 / 4 : ℝ))

theorem tau_partial_sum_omega_pm_exact {c} (hc : c < 1/(2π√2)) (X : ℝ) :
    (∃ x ≥ X, S x < −c x^{23/4}) ∧ (∃ x ≥ X, c x^{23/4} < S x)
```

In words:

- **(A)** The truncated Voronoi formula holds in mean square on every dyadic block, with the
  normalisation `x^{23/4}/(π√2) Σ_{n≤N} τ(n) n^{−25/4} cos(4π√(nx) − π/4)` (phase `−π/4` because
  `i^{12} = 1`, i.e. `cos(z − 12π/2 − π/4) = cos(z − π/4)`) and any `N = X^θ`, `0 < θ ≤ 1/4`.
  The remainder is `≪ X^{25/2}(X^{−1/16} + Σ_{n>N} τ(n)² n^{−25/2})`.
- **(B)** `∫₁^X S² ~ (B/50π²) X^{25/2}`: the Cramér–Tong theorem for `τ`, with the limit now
  proved to exist. (`CramerMeanSquare` had the log form, the liminf/limsup sandwich and the
  identification of the constant *if* the limit exists.)
- **(B′)** Exact `Ω±(x^{23/4})`, and in every dyadic interval: `S(x)/x^{23/4}` exceeds `c` and
  goes below `−c` in `[X, 2X]` for all large `X`, for every `c < 1/(2π√2) = 0.1125…`.
  This improves `TauOmegaPM.tau_partial_sum_omega_pm` (`β < 28/5`) to the exponent `23/4`
  with a positive constant.

Reusable intermediate results (all level (1)):

| name | statement |
|---|---|
| `Ik_asymp_twelve` / `kernel_asymp` | `|I₁₂(L) − cos(2L − π/4)/√(πL)| ≤ C₁₂/(πL)` for `L > 0` |
| `Ik_bound` | `|I_ν(L)| ≤ (2√π + C_ν)/√L` for `L ≥ 1`, `ν ≥ 1` |
| `Ak_asymp` | saddle point: `A_ν(L) = (−1+i) i^{−(ν+1)} e^{2iL} √(π/2L) + O(1/L)` |
| `lineInt_eq_Ik` | `(1/2π) ∫_ℝ f(c+iu) du = I_ν(L)` for every `c > 0`, `f(v) = v^{−ν−1}e^{L(v−1/v)}` |
| `laplace_inv` | `(1/2π) ∫ e^{w(1+it)} (1+it)^{−(r+1)} dt = w₊^r/r!` (`r ≥ 1`) |
| `integral_pow_mul_cexp_neg` | `∫₀^∞ v^r e^{−av} dv = r!/a^{r+1}`, `Re a > 0` |
| `Dq_modular` | `Σ τ(n)e^{−2πnz} = z^{−12} Σ τ(n)e^{−2πn/z}`, `Re z > 0` |
| `dual_W` | `W_r(x) = (r!/(2π)^r) Σ τ(n) k_r(n,x)` (`r ≥ 5`), `k_j(n,x) = (1/2π)∫ z^{−13−j}e^{2π(xz−n/z)}dt` |
| `kB_eq_Ik` | `k_j(n,x) = (x/n)^{(12+j)/2} I_{12+j}(2π√(nx))` |
| `kB_rel`, `hasDerivAt_kE` | `k_{j+1}(n,y+h) − k_{j+1}(n,y) = 2π∫₀^h k_j(n,y+s)ds` |
| `DkC_kB`, `DkC_WC_eq` | `Δ_h^r k_r = (2π)^r It_h^r k₀`; `Δ_h^r W_r(x) = r! Σ τ(n) It_h^r k₀(n,·)(x)` |
| `kB_zero_sub_main` | `|k₀(n,y) − y^{23/4}n^{−25/4}cos(4π√(ny)−π/4)/(π√2)| ≤ C y^{11/2} n^{−13/2}` |
| `mean_value` | `|∫_a^b y^{23/2}(Σ_{n∈F} cₙ cos θₙ)² − ½Σcₙ²∫_a^b y^{23/2}| ≤ b^{12}√M(2H_M+1)Σcₙ²` (`F ⊆ [1,M]`) |
| `integral_norm_It_sq_le` | `∫_a^b ‖It_h^j f‖² ≤ h^{2j} ∫_a^{b+jh} ‖f‖²` |
| `integral_short_sq_le` | `∫_X^{2X}(Σ_{x<n≤x+H}|τ(n)|)² ≤ (H+1)H Σ_{n≤3X}τ(n)²` |
| `L2_main` | the dyadic `L²` bound with free parameters `h, N, M` |

Here `I_ν(L) = Im A_ν(L)/π` with `A_ν(L) = ∫₀^∞ (−1+i) f((1−s)+is) ds` (the steepest-descent ray
from `1` through the saddle `i`). Numerically `I_ν(L) = J_ν(2L)` (§5); this identification is not
used.

## 2. Proof

No Bessel functions, no Stirling, no `Γ`. The kernel is the Schläfli integral, reached from the
modular relation of `Δ` through the Laplace transform.

1. **Dual expansion** (`Dual.lean`). By inverse Laplace on `Re z = 1`,
   `(2π)^r W_r(x)/r! = (1/2π)∫ e^{2πxz} z^{−r−1} Σ τ(n)e^{−2πnz} dt`. By `Dq_modular`,
   `Σ τ(n) e^{−2πnz} = z^{−12} Σ τ(n) e^{−2πn/z}`. Both interchanges are justified by
   `|τ(n)| ≤ A n^7` and `Σ n^7 e^{−na} ≤ K a^{−8}`; the second needs `r ≥ 5`. This gives
   `dual_W` with Schläfli kernels `k_r(n,x)`. Scaling `z = √(n/x)v` gives
   `k_j = (x/n)^{(12+j)/2} × line integral`.
2. **Contour** (`Contour.lean`). The vertical line `Re v = c` is moved to the ray
   `v = (1−u)+ui`. Write `F(u)` for the integral of `f` over the horizontal segment
   `[c+iu, (1−u)+iu]`. Then `F' = f(v(u))(−1+i) − i f(c+iu)`, using a primitive of `f` on a large
   disc in the upper half-plane (`DifferentiableOn.isExactOn_ball`). Also `F(T) → 0`, and `F(0)` is
   real. The lower half is the complex conjugate.
3. **Saddle point** (`Kernel.lean`). On the ray, `Re(v − 1/v) = −2s(1−s)²/((1−s)²+s²) ≤ 0`.
   Near the saddle, `v = i + u(1−i)` satisfies the exact identity
   `v − 1/v = 2i + w²/(i+w)` with `w = u(1−i)` and `w² = −2iu²`. So the integrand is
   `e^{2iL} e^{−2Lu²}` up to `|φ + 2u²| ≤ 4|u|³` in the exponent, and Lipschitz in the amplitude.
   The pieces `s ≤ 1/2` and `s ≥ 3/2` contribute `O(1/L)`, and Mathlib's Gaussian integral gives
   the main term. The result: `I₁₂(L) = cos(2L−π/4)/√(πL) + O(1/L)`. With `L = 2π√(ny)` this is
   `k₀(n,y) = y^{23/4}n^{−25/4}cos(4π√(ny)−π/4)/(π√2) + O(y^{11/2}n^{−13/2})`.
4. **Smoothing** (`Avg.lean`, `Dual.lean`). `Δ_h^r W_r/(r!h^r) = h^{−r}Σ τ(n) It_h^r k₀(n,·)`
   (iterated averages; `DkC_integral_on` from `TauPartialSumsSharp`). `bracket_signed` gives
   `|S − S_h| ≤ Σ_{x<n≤x+rh}|τ(n)|`.
5. **Assembly** (`Assembly.lean`, `Final.lean`). Take `r = 12`, `h = X^{7/32}`, `M = ⌊X^{5/8}⌋`,
   `N = ⌊X^θ⌋`. For `x ∈ [X, 2X]`:
   `S − V_N = (S − S_h) + (S_h − h^{−12}It V_M) + h^{−12}It(V_M − V_N) + (h^{−12}It V_N − V_N)`.

   | term | bound | relative to `X^{25/2}` |
   |---|---|---|
   | short sums, `L²` | `(12h+1)(12h)·Σ_{n≤3X}τ² ≪ X^{12+7/16}` | `X^{−1/16}` |
   | kernel error of the head | `CK(3X)^{11/2}M^{1/8}` (Rankin trick) | |
   | tail `n > M` | via `‖Δ_h^{12}k₁₂‖ ≤ 2^{12} sup‖k₁₂‖` and `Ik_bound`, `≪ X^{91/16}` | `X^{−1/8}` (both) |
   | block `N < n ≤ M` | `mean_value` over `[X, 3X]` | `Σ_{n>N}bₙ² + X^{−3/16}log X` |
   | Lipschitz `V_N` | `≪ N X^{21/4} h ≪ X^{183/32}` | `X^{−1/16}` |
6. **Cramér** (`Cramer.lean`).
   - `mean_value` with `F = [1, N]`, `N = X^{1/4}`, gives `∫_X^{2X} V_N² ~ (B/4π²)∫_X^{2X}x^{23/2}`.
   - `2|VD| ≤ εV² + D²/ε` transfers this to `S`.
   - Dyadic blocks are summed by induction over `[Y₀, 2^n Y₀]`:
     `|I(Y) − cY^{25/2}| ≤ K₀ + εY^{25/2}`.
7. **`Ω±`** (`Omega.lean`). This is Ingham's positive kernel on the first coefficient
   `b₁ = τ(1) = 1`.
   - `∫_X^{2X} S(x)x^{−23/4}(1 ± cos θ₁(x)) dx = ±X/(2π√2) + O(X^{5/8}) + o(X)`. All other
     frequencies are killed by one integration by parts (`abs_integral_cos_le`, `term_int`).
   - The remainder uses `2|D|x^{−23/4} ≤ η + D²x^{−23/2}/η` and `voronoi_L2`.
   - A one-sided bound `±S ≤ c x^{23/4}` on `[X, 2X]` would make the left side `≤ c(X + O(√X))`.

## 3. Files

| file | content | lines |
|---|---|---|
| `Kernel.lean` | path, integrand, piece bounds, Gaussian window, `Ak_asymp`, `Ik_bound`, `Ik_asymp_twelve` | 754 |
| `Contour.lean` | `exists_ball_sub`, `graph_finite`, `graph_zero`, `lineInt_eq_Ik` | 377 |
| `Laplace.lean` | `integral_pow_mul_cexp_neg`, Fourier transform of `y₊^r e^{−y}`, `laplace_inv` | 219 |
| `Modular.lean` | `Dq`, `hasSum_Dq`, `Dq_modular` | 79 |
| `Dual.lean` | τ bounds, `kB`, `dual_W`, `kE`, `hasDerivAt_kE`, `kB_rel`, `kB_eq_Ik`, `It`, `DkC_kB`, `DkC_WC_eq` | 599 |
| `Avg.lean` | linearity and sup bounds for `It`, Cauchy–Schwarz, `integral_norm_It_sq_le` | 207 |
| `MeanValue.lean` | `abs_integral_w_cos_le`, harmonic sums, `mean_value` | 388 |
| `Est.lean` | `kB_zero_sub_main`, `norm_kB_twelve_le`, Rankin-trick sums, Lipschitz bound, short sums | 341 |
| `Assembly.lean` | `Sre`, `Vth`, `Sh`, bracket, head/tail split, `pointwise_bound`, `L2_main` | 473 |
| `Final.lean` | `mv_tail`, parameter bounds, `voronoi_L2_bound`, `voronoi_L2` | 370 |
| `Cramer.lean` | integrability, `tendsto_v/d/s`, dyadic induction `tendsto_Iq`, `tau_cramer_core` | 407 |
| `Omega.lean` | `abs_integral_cos_le`, `term_int`, `main_int`, `omega_core`, `omega_plus/minus` | 521 |
| `Main.lean` | explicit-form headlines, `#print axioms` | 123 |

Reused from the repository: `TauPartialSumsSharp` (`WC`, `DkC`, `DkC_const_mul`,
`DkC_tsum_on`, `DkC_integral_on`, `norm_DkC_le`, `bracket_signed`); `HeckeL.Δf` and the
`q`-expansion `heckeData.coeff_discriminant`; `HeckeConvex` (`exists_sum_abs_tau_le`,
`exists_sum_sq_div_le`, `sum_sq_le`, `summable_abs_tau_div_rpow`); `MeanSquare.summable_tau_sq`;
`TauPartialSums.Icc_one_eq_Ioc`; `tau_one`. `TauPartialSumsSharp.dual_rep` (the Mellin–Barnes
route) is not used.

## 4. Gaps

- **Range of `N`.** It is `N = X^θ` with `θ ≤ 1/4`. The classical statement allows `N` up to
  about `X`. The same mean-value bound (off-diagonal `≪ X^{12}√N log N`) handles any
  `θ < 1` once `V_N − V_{X^{1/4}}` is added as a tail. This was not written out.
- **No pointwise truncated Voronoi.** The remainder is controlled only in `L²`. The pointwise form
  with error `x^{11/2+ε}(x/N)^{1/2}` needs Deligne-type short-interval bounds and was not
  attempted.
- **Constant in `Ω±`.** The constant `1/(2π√2)` is not sharp: numerically
  `max_{[X,2X]} S/x^{23/4} ≈ 0.6` (§5). Hafner–Ivić obtain a growing factor
  `exp(D(log log x)^{1/4}…)` using Deligne and simultaneous Diophantine approximation; that is not
  reached here.
- **Only `τ`.** For a level-one eigenform of weight `k`, `dual_W` (modularity), the kernel
  (`ν = k`, phase `cos(2L − kπ/2 − π/4)`) and the assembly carry over verbatim with `12` replaced
  by `k`. Not done.
- **Higher moments** (Tong's fourth moment) are not done.

## 5. Numerical checks (evidence level (4); `scripts/voronoi_trunc/`)

`check.gp`:

- The path kernel equals the Bessel function: `I₁₂(L) = J₁₂(2L)` to 10 digits at
  `L = 5, 20, 45`. (At `L = 80` they agree to 6 digits; the gap is numerical-quadrature error.)
- The mean of `(S − V_N)²/x^{23/2}` over `[X, 2X]` decreases with `N`:

  | `X` | `N` | mean |
  |---|---|---|
  | 2000 | 20 | 0.00447 |
  | 2000 | 60 | 0.00281 |
  | 8000 | 30 | 0.00354 |
  | 8000 | 100 | 0.00205 |
  | 16000 | 40 | 0.00314 |
  | 16000 | 120 | 0.00183 |

  The mean of `S²/x^{23/2}` is `0.0401`, against the prediction `B/(4π²) = 0.040133`.

`omega_check.gp`: on `[X, 2X]` with `X = 10³ … 2·10⁴`, `max S/x^{23/4} ≈ +0.48 … +0.60` and
`min ≈ −0.53 … −0.67`. Both have absolute value above `1/(2π√2) = 0.1125`, which is consistent
with `tau_omega_pm_exact`.

## 6. Literature (from memory, not checked against sources)

- G. Voronoi (1904) and J. R. Wilton (1929): the Voronoi formula for divisor sums and for `τ`.
- H. Cramér (1922) and K.-C. Tong (1956): mean square of the error terms.
- A. E. Ingham (1942): the positive-kernel trick for `Ω±`.
- J. L. Hafner and A. Ivić (1989): `Ω±` with a growing factor, using Deligne.
- The route used here was not checked against the literature, and no novelty claim is made. It
  combines the Schläfli kernel from the modular relation, an elementary steepest-descent
  evaluation, and Riesz differencing at scale `X^{7/32}`.
