# Rankin–Selberg error term: Mellin mean square, log-averaged mean square, and Ω±

Lean: `RamanujanTau/RankinOmegaPM/` (7 files, about 1710 lines). Build with
`nice -n 10 lake build RamanujanTau.RankinOmegaPM.Main` (exit 0). There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. `#print axioms` on all 23 listed results
gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1)** for everything in §1.
Deligne is not used. The public entry point is included in the `RamanujanTau.lean` import graph.

Notation: `R(x) = ∑_{n≤x} τ(n)²/n¹¹ − c x`. More generally `R(x) = ∑_{n≤x} |a_f(n)|²/n^{k−1} − c x`
for a nonzero level-one cusp form `f`, or `R(x) = ∑_{n≤x} aₙ − c x` for abstract Rankin–Selberg
data `RSDataM`. Here `c₀ = (3/π)(4π)¹²‖Δ‖²/11!` is Rankin's constant from
`RankinExact.rankinSelberg_exact`, which gives `|R| ≪ x^{3/5}` when `c = c₀`.

## 1. Statements (Lean, level 1)

```lean
-- namespace RamanujanTau.RankinOmegaPM   (Main.lean)

-- (1) Mellin mean-square lower bound; every real c
theorem tau_rankin_mellin_mean_sq_lower (c : ℝ) :
    ∃ K > 0, ∀ δ, 0 < δ → δ ≤ 1/32 →
      ENNReal.ofReal (K / δ) ≤ ∫⁻ x in Ioi 1,
        ENNReal.ofReal (|∑ n ∈ Icc 1 ⌊x⌋₊, τ(n)²/n¹¹ − c x|² · x^(−2(3/8+δ) − 1))

-- (1b) log-averaged mean square is not o(log X); every real c
theorem tau_rankin_log_mean_sq_omega (c : ℝ) :
    ∃ κ' > 0, ∀ X0, ∃ X ≥ X0,
      κ' * log X ≤ ∫ x in 1..X, |∑ n ∈ Icc 1 ⌊x⌋₊, τ(n)²/n¹¹ − c x|² · x^(−7/4)

-- (2) Ω± with exponent 3/20 − ε; Rankin's constant c₀
theorem tau_rankin_omega_pm {β : ℝ} (hβ : β < 3/20) (c1 X : ℝ) :
    (∃ x ≥ X, ∑_{n≤x} τ(n)²/n¹¹ − c₀ x < −c1 x^β) ∧
    (∃ x ≥ X, c1 x^β < ∑_{n≤x} τ(n)²/n¹¹ − c₀ x)
```

The same three statements hold for every nonzero level-one cusp form:
`cuspForm_mellin_mean_sq_lower`, `cuspForm_log_mean_sq_omega`, and `cuspForm_rankin_omega_pm`
with `c = rsConst f`. `cuspForm_omega_pm_of_bound` takes any `c` that has a `3/5` bound. They
also hold for abstract data `RSDataM`: `rs_mellin_mean_sq_lower`, `rs_log_mean_sq_omega`, and
`rs_omega_pm` under `|R(x)| ≤ C x^{3/5}`.

Reading (1): the lower integral is used, so there is no integrability side condition. If the
integral diverges, the statement holds trivially. With `σ = 3/8 + δ`, it reads

    ∫₁^∞ |R(x)|² x^{−2σ−1} dx ≥ K/(σ − 3/8)        (3/8 < σ ≤ 3/8 + 1/32).

Reading (2): `c₁` ranges over all of `ℝ`, so `limsup R/x^β = +∞` and `liminf R/x^β = −∞` for
every `β < 3/20`. That is, `R = Ω±(x^{3/20−ε})`. The two-sided exponent is `3/8`
(`RankinOmega`). The signed exponent proved here is `3/20 = 0.15`.

Reusable intermediate results (all level 1):

| theorem | statement |
|---|---|
| `Lam_eq_mellin_conv` | `Λ(s)γₘ(s)⁻¹ = ζ(2s)(sM(s) + cs/(s−1))` on `{Re s > θ, Im s < 0}`, assuming only that `∫ R x^{−s−1}` converges absolutely for `Re s > θ` (no pointwise bound) |
| `core_lower` | if `M` converges on `Re s > 3/8 + δ/2` and `h_σ ∈ L²` (`σ = 3/8+δ`, `δ ≤ 1/16`), then `∫|h_σ|² ≥ K₂/(8δ)`, with `K₂` independent of `δ` |
| `hfun_sq` | `∫_ℝ |h_σ(u)|² du = ∫₁^∞ |R|² x^{−2σ−1} dx` (Mellin–Plancherel change of variables) |
| `mc_of_fsq` | mean-square convergence at `σ` implies absolute Mellin convergence on `Re s > σ` (AM–GM) |
| `lintegral_weight_le` | Tonelli: `∫₁^∞ f x^{−p} ≤ ∫₁^∞ p y^{−p−1} Φ(y) dy` whenever `∫_{(1,y)} f ≤ Φ(y)` |
| `Z1_real_ne_zero` | `Z₁(σ) ≠ 0` for every real `σ > 0`, where `Z₁(w) = w − w(w−1)∫₁^∞{t}t^{−w−1}dt` is holomorphic on `Re w > 0` and equals `(w−1)ζ(w)` for `Re w > 1` |
| `exists_strip` | `Z₁ ≠ 0` on a thin strip `{β₀ ≤ Re w ≤ B, |Im w| < r}`, so `Q = (w−1)/Z₁ = 1/ζ` is holomorphic there |
| `M_eq_cont` | `M(s) = Λ(s)γ(s)⁻¹Q(2s)/s − c/(s−1)` on `θ < Re s < 1` (`θ ≥ 1/2`) |
| `landau_mellin_strip` | Landau's theorem for `g ≥ 0`. It needs a continuation only on a thin strip `{β < Re s < σ₀+η, |Im s| < r}` around the real axis, not on a half-plane |
| `conv_of_one_sided` | a one-sided bound `εR ≥ −c₁x^β` (with `0 < β < 3/5`) gives absolute convergence of `∫ R x^{−s−1}` on `Re s > β` |
| `false_of_conv` | that convergence with `β < 3/20` is impossible |
| `hR_of_nat` | turns the integer bound `|A(N) − cN| ≤ CN^{3/5}` into the real-variable bound |

## 2. Route decisions (on paper first)

### (1) Mellin mean-square lower bound

`RankinOmega.rs_omega_core` used the pointwise hypothesis `|R| ≤ c₀x^{3/8}` for two things:
holomorphy of `M` on `Re s > 3/8`, and `h_σ ∈ L¹ ∩ L²`. The Plancherel and dyadic-block lower
bound `∫|M(σ−2πiξ)|² ≥ K₂/(8δ)` needs only the functional-equation identity on the line, and that
identity needs only holomorphy of `M`.

So: suppose `∫₁^∞ |R|²x^{−2σ−1} < ∞` with `σ = 3/8 + δ`. By AM–GM,

    t^{−σ'−1}|R| ≤ ½(|R|²t^{−2σ−1} + t^{−2(σ'−σ)−1}),

so `M` converges absolutely on `Re s > σ`. Then `Lam_eq_mellin_conv` holds there. At
`σ' = 3/8 + 2δ`, `h_{σ'} ∈ L¹ ∩ L²`, and its `L²` norm is the Mellin mean square at `σ'`
(`hfun_sq`), which is `≤` the one at `σ`. So `core_lower` at `2δ` gives `≥ K₂/(16δ)`. About
150 new lines; most of the work was `core_lower`, a version of `rs_omega_core` under convergence.

### (1b) Does `∫₁^X R² x^{−7/4} ≫ log X` follow?

**Only in Ω form.** Let `G(X) = ∫₁^X R² x^{−7/4}`, which is nondecreasing. Then

    F(δ) = ∫₁^∞ R² x^{−7/4−2δ} = 2δ ∫₁^∞ G(y) y^{−2δ−1} dy.

The left side is the Mellin mean square at `σ = 3/8 + δ`. A lower bound `F(δ) ≥ K/δ` is an
Abelian-side statement about a Laplace transform of `G`.

- If `G(X) ≤ κ log X + B` for all large `X`, then `F(δ) ≤ 2δ(κ/δ² + B/(2δ)) = 2κ/δ + B`, using
  `log y ≤ y^δ/δ`. For `κ = K/4` this contradicts `F(δ) ≥ K/δ` as `δ → 0`. Hence
  `G(X) ≥ κ log X` for **arbitrarily large** `X` (`log_mean_sq_omega`, Tonelli in
  `lintegral_weight_le`).
- A lower bound for **all** large `X` does **not** follow from a Laplace-transform lower bound
  alone. `G` could be flat on very long ranges. It does follow if one also has the upper bound
  `G(X) ≤ A log X + B`. In that case, if `G(Y) ≤ ε log Y`, take `2δ log Y = u`. Then
  `δF(δ) ≤ εu/2 + A e^{−u}(u+1)/2`. With `u` large and `ε < K/u` this contradicts `δF ≥ K`.
  That upper bound is equivalent in strength to `∫₁^X R² ≪ X^{7/4}`, which is open (it is the
  conjectured order). Unconditionally `|R| ≪ x^{3/5}` only gives `G(X) ≪ X^{9/20}`. This
  Tauberian direction is recorded at level (3) and not formalized.
- Corollary on paper (level 3, trivial): `∫₁^X R² = Ω(X^{7/4})`. If it were `≤ εX^{7/4}` for
  large `X`, partial integration would give `G(X) ≤ (7/4)ε log X + O(1)`.

### (2) Ω±

- **Landau on `M(s) ± c'/(s−3/8)`** (the route suggested in the brief) fails. As
  `RankinOmega` noted, there is no real singularity at `3/8`.
- **`TauOmegaPM` route** (Landau plus Plancherel). A one-sided bound `εR ≥ −c₁x^β` makes
  `g = εR + c'1_{t≥1}t^β ≥ 0`, with Mellin transform `εM(s) + c'/(s−β)`. Landau needs a
  continuation of this along the real segment `(β, 3/5]`.

  **New obstruction compared to `τ`:** `M(s) = D(s)/s − c/(s−1)` and `D = ζ(s)L(sym²,s)/ζ(2s)`.
  So `M` is not known to be holomorphic on any half-plane `Re s > β` with `β < 1/2`. The
  nontrivial zeros of `ζ(2s)` at `Re s < 1/2` are poles unless they are cancelled. This forces the strip version of Landau
  (`landau_mellin_strip`). It needs only analyticity in a neighbourhood of the real axis, and so
  only that `ζ(w) ≠ 0` for real `w ∈ (0, 2]`. That is proved in `ZetaReal`:
  `Re Z₁(σ) = σ + σ(1−σ)∫₁^∞{t}t^{−σ−1} ≥ σ > 0` for `σ ≤ 1`.

  Landau then gives absolute convergence of `∫|R|t^{−σ−1}` for `σ > β`. That is `L¹`
  information. The Plancherel step needs `L²` at `σ ↓ 3/8`. With only the sup bound
  `|R| ≪ x^{θ}`, `θ = 3/5`, the conversion is
  `|h_σ|² ≤ C|h_{σ₁}|` with `σ₁ = 2σ − θ`. This works iff `β < 2·(3/8) − 3/5 = 3/20`.

  **Best β (formal): every `β < 3/20`.** Any improvement `θ` in the sup exponent gives
  `β < 3/4 − θ` one-for-one. Huang's `θ = 3/5 − 1/560` would give `β < 0.1518`. The conjectural
  `θ = 3/8 + ε` would give `3/8 − ε`.
- **A second route** (paper, level 3), giving `β < 1/4` conditionally. Landau's conclusion makes
  `M` bounded on each line `Re s = σ > β`: `|M| ≤ L(σ) = ∫|R|t^{−σ−1}`. Combine this with the
  pointwise functional-equation inequality `c_g T^{2−4σ}|Z(w)| ≤ |ζ(2s)||X(s)|`, the first moment
  `∫_T^{2T}|Z(w)| ≫ T` on `Re w = 1−σ`, and Cauchy–Schwarz with `∫_T^{2T}|ζ(2σ+it)|² ≪ T^{2−4σ}`
  (`2σ < 1/2`, via the ζ functional equation). This gives `T^{3−4σ} ≪ L T^{5/2−2σ}`, a
  contradiction iff `σ < 1/4`. The ζ mean square needed is at `Re = 1 − 2σ ∈ (1/2, 3/4)`. The
  repo's `zeta_mean_sq` covers only `[3/4, 1]`, so unconditionally this route gives only
  `β < 1/8 < 3/20`. With the classical (Hardy–Littlewood) mean square for `Re > 1/2` it gives
  `Ω±(x^{1/4−ε})`. Not formalized.
- **Exact `Ω±(x^{3/8})`** needs a Voronoi-type `L²` expansion of `R` with Ingham's kernel, as in
  `VoronoiTrunc`. That is target (3), which was not attempted (see §5).

## 3. Files

| file | content | lines |
|---|---|---|
| `Core.lean` | `differentiableAt_M`, `Lam_eq_mellin_conv`, `integrable_hfun_of_mc`, `core_lower` | 181 |
| `MeanSq.lean` | `ioi_zero_one`, `fsq`, `hfun_sq`, `amgm_rpow`, `mc_of_fsq`, `mellin_mean_sq_lower` | 216 |
| `MeanOmega.lean` | `ofReal_rpow_eq_lintegral`, `lintegral_weight_le`, `gsq`, `log_le_rpow_div`, `log_mean_sq_omega` | 273 |
| `ZetaReal.lean` | `Z1`, `Z1_eq`, `IN_real_re_nonneg`, `Z1_real_ne_zero`, `Qz`, `Qz_mul_zeta`, `exists_strip` | 107 |
| `LandauStrip.lean` | `landau_mellin_strip` | 232 |
| `OmegaPM.lean` | `Rf_eq_re`, `Pw`, `mellin_Pw`, `M_eq_cont`, `gfun`, `conv_of_one_sided`, `false_of_conv`, `rs_omega_pm` | 431 |
| `Main.lean` | `hR_of_nat`, abstract, cusp-form and `τ` headlines, `#print axioms` | 274 |

Reused results:

- `RankinOmega`: `block_lower`, `dyadic_weight8`, `Rf`, `hfun`, `fourier_hfun`,
  `mellin_Rf_large`, `Zf_eq`, `differentiableAt_Lam`, `IN`, `zeta_formula_large`,
  `differentiableAt_IN`, `exists_first`, `coeffSq_discriminant`, `discriminant_ne_zero'`.
- `TauOmegaPM`: `hasDerivAt_mellin_neg`, `differentiableOn_mellin_neg`, `iteratedDeriv_mellin_neg`,
  `mc_mono`, `conv_logPow`, `logPow`, `integrable_of_mc`, `mc_of_bound`, `norm_integrand`,
  `aesm_integrand`. The body of `landau_mellin` is copied, with the localisation changed.
- `TauOmegaPartial.plancherel_of_integrable`.
- `RankinExact.rankinSelberg_exact(_general)`.

## 4. Numerics (level 4)

`scripts/rankin_omega_pm/rankin_omega_pm_check.gp` (PARI, `nbthreads = 1`, 34 s, `N ≤ 5·10⁵`,
`c₀ = 0.384084054…`). On `[n, n+1)`, `R` is linear, so all integrals are exact piecewise.

| X | G(X) = ∫₁^X R²x^{−7/4} | G/log X | max R/x^{3/8} | min R/x^{3/8} | sign changes |
|---|---|---|---|---|---|
| 10⁴ | 0.4139 | 0.0449 | 0.580 | −0.456 | 754 |
| 10⁵ | 0.4846 | 0.0421 | 0.632 | −0.596 | 2746 |
| 2·10⁵ | 0.5040 | 0.0413 | 0.640 | −0.596 | 4377 |
| 5·10⁵ | 0.5317 | 0.0405 | 0.640 | −0.596 | 7899 |

The extremes are taken over `1000 < x ≤ X`.

- The increments of `G` per unit of `log X` are about `0.031`, `0.028` and `0.029` on
  successive ranges. This is consistent with `G(X) ≈ 0.03 log X + 0.13`, that is
  `∫₁^X R² ≍ X^{7/4}` (conjectured).
- `R/x^{3/8}` takes both signs at size about `0.6`. This is consistent with the conjectured
  true `Ω±(x^{3/8})`, which is far beyond the proved `3/20`.
- `δ·∫₁^X R²x^{−2σ−1}`, with `σ = 3/8 + δ`, at `X = 5·10⁵` is `0.0267`, `0.0176` and `0.0106`
  for `δ = 1/10, 1/20, 1/40`. These are still increasing in `X` (truncation), which is
  consistent with `δF(δ) → const`.

## 5. Gaps, and what is not claimed

- **Ω± exponent.** `3/20 − ε` is formal. `1/4 − ε` is paper only and conditional on the
  classical ζ mean square on `1/2 < Re < 3/4` (§2). The conjectured truth is `3/8`. Nothing is
  claimed at `β = 3/20` itself.
- **`∫₁^X R² x^{−7/4} ≫ log X` for all large `X`** is not proved. Only the Ω form is proved.
  The all-`X` form follows from the open upper bound `G(X) ≪ log X` (§2(1b)).
- **Target (3): degree-4 `L²` Voronoi and `∫₁^X R² ~ C X^{7/4}`** was not attempted. It needs
  three things. First, the degree-4 analogue of `VoronoiTruncGeneral.VData`, with kernel
  asymptotics for `Γ(s)Γ(s+11)` (Bessel-type `J` of order matching degree 4). Second, the
  `ζ(2s)` denominator: `D` is not an `L`-function of a single automorphic form, and its
  coefficients `aₙ = τ(n)²/n¹¹` come with the `1/ζ(2s)` twist. The Voronoi expansion is usually
  done for `ζ(2s)D(s) = ζ(s)L(sym²,s)` (coefficients `∑_{m²|n} a(n/m²)`) and then transferred.
  Third, a mean-square upper bound of the truncation error. Rough estimate: 2500–4000 Lean
  lines, mostly new. The `VoronoiTrunc` skeleton (dual sum, truncation, Cramér) transfers, but
  the kernel and the `ζ(2s)` transfer are new.
- The constants `K`, `κ'` are implicit. They come from `gamma_ratio_lower`, `Zf_first_moment` and
  `zeta_mean_sq` via `RankinOmega.block_lower`.
- Byproduct: `Z1_real_ne_zero` shows that `ζ` has no zero in `(0, 1)`. The identification
  `Z₁ = (w−1)ζ(w)` is proved only for `Re w > 1`. The statement "`ζ(σ) ≠ 0` on `(0,1)`" in
  Mathlib form would need the identity principle on `0 < Re < 1` (about 20 lines, not done since
  it is not needed).

## 6. Literature (from memory; attributions not checked)

- Rankin (1939): `O(x^{3/5})`. Huang (2021): `3/5 − 1/560`.
- Ivić: the Ω-result `x^{3/8}` and mean-square questions for the Rankin–Selberg problem
  (around 1990).
- Ivić–Matsumoto–Tanigawa (around 1999): Riesz means and mean squares for Rankin–Selberg
  coefficients, via a Voronoi-type formula. This is the classical route to `∫Δ² ≍ X^{7/4}` for
  smoothed versions.
- Landau's theorem for nonnegative Dirichlet/Mellin integrals and its local form (singularity at
  the real abscissa): Widder, *The Laplace Transform*, Ch. II.
