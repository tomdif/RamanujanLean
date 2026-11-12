# `∑_{n≤x} τ(n) = Ω±(x^β)` for every `β < 28/5`: sign changes at height beyond `x^{11/2}`

> **Update (2026-11-05):** the truncated Voronoi formula (L² form), the Cramér limit X^{−25/2}∫₁^X S² → B/(50π²) and exact Ω±(x^{23/4}) are proved in `VoronoiTrunc`; see [VORONOI_TRUNC](VORONOI_TRUNC.md).

Lean: `RamanujanTau/TauOmegaPM/` (3 files, about 915 lines). No `sorry`, no `native_decide`, no new
axiom, no named hypothesis. Build with `nice -n 10 lake build RamanujanTau.TauOmegaPM.Main`
(exit 0). `#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
**Evidence level (1).** Deligne is not used.

## 1. Statements

```lean
-- RamanujanTau.TauOmegaPM
theorem tau_partial_sum_omega_pm {β : ℝ} (hβ : β < (28 : ℝ) / 5) (c X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) < -c * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ))

-- every nonzero level-one cusp form with real coefficients, every weight k
theorem cuspForm_partial_sum_omega_pm (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) {β : ℝ} (hβ : β < ((k : ℝ) - 1) / 2 + 1 / 10) (c X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re < -c * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ β < (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n).re)
```

`c` ranges over all of `ℝ`, so the statement says
`limsup A(x)/x^β = +∞` and `liminf A(x)/x^β = −∞` for each `β < (k−1)/2 + 1/10`. For `τ` this is
`Ω±(x^{28/5−ε})`, where `28/5 = 11/2 + 1/10 = 5.6`.

**What is not proved.** The exponent `23/4 = 5.75` of the two-sided Ω result
(`TauOmegaPartial.tau_partial_sum_omega`) is **not** reached with signs. The loss is `3/20`. It is
exactly the gap `θ − α` between the unconditional upper exponent `θ = (k−1)/2 + 2/5`
(`TauPartialSumsSharp`) and the Ω-exponent `α = (2k−1)/4`. See §3.

Reusable intermediate results (all level (1)):

```lean
-- Landau's theorem for Mellin transforms of nonnegative functions
theorem landau_mellin {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t < 1, g t = 0)
    (hgm : Measurable g) {σ0 β : ℝ}
    (hconv : MellinConvergent (fun t => (g t : ℂ)) (-((σ0 : ℝ) : ℂ))) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | β < s.re})
    (hFG : ∀ s : ℂ, σ0 < s.re → mellin (fun t => (g t : ℂ)) (-s) = F s) :
    ∀ σ : ℝ, β < σ → MellinConvergent (fun t => (g t : ℂ)) (-((σ : ℝ) : ℂ))
-- holomorphy / derivatives of s ↦ ∫ φ(t) t^{-s-1} dt on the half-plane of convergence
lemma hasDerivAt_mellin_neg, iteratedDeriv_mellin_neg, mellin_eq_of_eventually
-- Step 1: one-sided bound ⇒ ∫₁^∞ |A| t^{-σ-1} < ∞ for all σ > β
theorem conv_of_one_sided ...
-- Step 2: that convergence + |A| ≤ C x^θ + β + θ < 2α ⇒ False
theorem false_of_conv ...
```

## 2. Proof

Let `α = (2k−1)/4` and `θ = (k−1)/2 + 2/5 + η`. Suppose `ε A(x) ≥ −c x^β` for `x ≥ X₀`, where
`ε = ±1`, `0 < β < (k−1)/2 + 1/10` and `η = ((k−1)/2 + 1/10 − β)/4`.

1. **A nonnegative function.** Let `g(t) = 1_{t≥1}(ε A(t) + c' t^β)` with
   `c' = |c| + ∑_{n≤X₀}|a(n)|`. Then `g ≥ 0`. Real coefficients make `A` real.
2. **Its Mellin transform.** For `Re s` large,
   `∫ g(t) t^{−s−1} dt = ε L(f,s)/s + c'/(s−β)` (`TauOmegaPartial.mellin_A_eq_of_large` and
   `integral_Ioi_cpow_of_lt`). The right side is holomorphic on `Re s > β`, because `L` is entire
   and `β > 0`.
3. **Landau** (`Landau.lean`, `landau_mellin`). Let `σ_c` be the abscissa of convergence and
   suppose `σ_c > β`.
   - `s ↦ ∫φ t^{−s−1}` is holomorphic on `Re s > σ_c`. Its `n`-th derivative is
     `∫(−log t)^n φ t^{−s−1}`. This is differentiation under the integral sign
     (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), with domination from
     `log t ≤ t^ε/ε`.
   - By the identity theorem, `F` equals the Mellin integral on `Re s > σ_c`.
   - Taylor-expand `F` at `a = σ_c + ρ`, where `ρ = (σ_c−β)/3`
     (`Complex.hasSum_taylorSeries_on_ball`). Evaluate at the real point `z = σ_c − ρ`. The terms
     are `(2ρ)^n/n!·∫(log t)^n g t^{−a−1} ≥ 0`.
   - Monotone convergence (`lintegral_tsum`) then gives
     `∫ g t^{−z−1} = ∑(…) < ∞`. That contradicts `z < σ_c`.
4. **Consequences** (`conv_of_one_sided`). `|A| ≤ g + c' t^β` on `[1,∞)`, so
   `∫₁^∞ |A(t)| t^{−σ−1} dt < ∞` for every `σ > β`. The identity principle
   (`mellin_eq_of_eventually`) then gives `∫ A t^{−w−1} = L(w)/w` on `Re w > β`. So
   `𝓕h_σ(ξ) = L(σ−2πiξ)/(σ−2πiξ)` for `σ > β`, where `h_σ(u) = e^{σu}A(e^{−u})` (as in
   `TauOmegaPartial`).
5. **`L²` from `L¹` + sup** (`false_of_conv`). Fix `σ₁ = (β + 2α − θ)/2`, so `β < σ₁` and
   `σ₁ + θ < 2α`. With `|A(x)| ≤ C x^θ` (`TauPartialSumsSharp.cuspForm_partial_sum_sharp`),
   `|h_σ(u)|² ≤ |C| |h_{σ₁}(u)|` pointwise for every `σ ≥ α`. Hence
   `∫|h_σ|² ≤ |C| ‖h_{σ₁}‖₁`, **uniformly** in `σ = α + δ`. The `L¹` norm is finite by step 4.
6. **Contradiction.** Plancherel (`TauOmegaPartial.plancherel_of_integrable`) and the dyadic
   blocks (`block_lower`, `dyadic_weight`) give `∫|h_σ|² ≥ K₂/(4δ)`. For
   `δ ≤ K₂/(8(|C|‖h_{σ₁}‖₁+1))` this exceeds the bound in step 5.
7. **Main.** Apply step 6 with `ε = 1`, which rules out `A ≥ −|c|x^{β'}` and gives the `Ω₋` half.
   Apply it with `ε = −1`, which rules out `A ≤ |c|x^{β'}` and gives the `Ω₊` half. Here
   `β' = max(β, (k−1)/2) > 0`. Then `x^β ≤ x^{β'}` for `x ≥ 1` handles any `β` and any sign of
   `c`.

## 3. Why `28/5` and not `23/4`

The Landau step only gives `L¹` information:
`∫|A| x^{−σ−1} ≲ 2c/(σ−β) + O(1)`. Plancherel needs `L²`. The only available converter is the
pointwise bound `|A| ≪ x^θ`. It turns `L¹` at `σ₁` into `L²` at `σ` once `2σ ≥ σ₁ + θ`. With
`σ ↓ α`, the method gives exactly `β < 2α − θ = (k−1)/2 + 1/10 − η`.

- A better unconditional sup exponent `θ` improves the result one-for-one:
  `β_max = 2α − θ`. For example, the classical `(k−1)/2 + 1/3`, if it were formalized, would give
  `(k−1)/2 + 1/6`, which is `17/3` for `τ`. The conjectural `θ = α + ε` would give `α − ε`, i.e.
  `23/4 − ε`.
- Keeping track of constants does not remove the loss. Even with a bounded initial-segment
  correction, `∫|A|x^{−σ'−1} ≤ |c|/δ + O(1)`, and the sup bound still carries the `+η` of
  `TauPartialSumsSharp`.
- The pure Landau argument at a fixed point, `|G(σ+it)| ≤ G(σ)`, cannot work. `L(s)/s` has no
  singularity on `Re s = α`, so the frequencies must grow like `1/δ`. That is the Plancherel
  route above.
- The exact `Ω±(x^α)` needs either the Voronoi series with Bessel asymptotics, or an `L^p`
  (`p > 2`) or mean-square **upper** bound for `A` at the critical exponent. With either input,
  Ingham's almost-periodicity trick applies. The repository has `TauPartialSumsSharp.dual_rep`
  for Riesz order `≥ 2`, but with Mellin–Barnes kernels and no cosine asymptotics.

## 4. Files

| file | content | lines |
|---|---|---|
| `Landau.lean` | `logPow`, `mc_mono`, `mc_logPow`, `conv_logPow`, `hasDerivAt_mellin_neg`, `differentiableOn_mellin_neg`, `iteratedDeriv_mellin_neg`, `mellin_eq_of_eventually`, `landau_mellin` | 379 |
| `OmegaPM.lean` | `mc_of_bound`, `integrable_of_mc`, `A_real`, `mellin_A_eq_of_conv`, `fourier_hfun_of_conv`, `conv_of_one_sided`, `false_of_conv`, `no_one_sided` | 435 |
| `Main.lean` | `cuspForm_partial_sum_omega_pm`, `tau_partial_sum_omega_pm`, `#print axioms` | 101 |

`Landau.lean` imports only Mathlib. It is a general Landau theorem for Mellin transforms on
`[1,∞)`.

Reused:
- `TauOmegaPartial`: `A`, `A_of_lt_one`, `measurable_A`, `norm_A_le`, `mellin_A_eq_of_large`,
  `hfun`, `measurable_hfun`, `plancherel_of_integrable`, `Fs`, `continuous_Fs`, `block_lower`,
  `exists_first_coef`, `dyadic_weight`;
- `TauPartialSumsSharp.cuspForm_partial_sum_sharp`;
- `HeckeConvexGeneral` (`fL_entire`, `coef_discriminant`, `eq_zero_of_lt_twelve`);
- `HardyZerosGeneral.discriminant_ne_zero'`.

The change of variables in `integrable_of_mc` copies Mathlib's private helper lemmas from
`MellinInversion`.

The public entry point is included in the `RamanujanTau.lean` import graph.

## 5. Gaps

- **Exponent.** The result is `28/5 − ε`, not `23/4` (§3). Closing the gap needs a stronger upper
  input: an exact sup exponent, an `L^p` bound, or Voronoi asymptotics.
- The `Ω±` here is "unbounded ratio" (`limsup A/x^β = +∞`) for `β < 28/5`. No `Ω±` with a
  constant is claimed at `β = 28/5`.
- **Real coefficients are assumed.** This covers `Δ` and, more generally, Hecke eigenforms.
  Complex `f` is handled only through its real-coefficient components, which is not formalized.

## 6. Literature

- E. Landau (1905–1915): the theorem that a Dirichlet integral of a nonnegative function is
  singular at the real point of its abscissa, and its use for Ω± results.
- J. L. Hafner, A. Ivić, *On sums of Fourier coefficients of cusp forms*, Enseign. Math. 35
  (1989): `Ω±(x^{k/2−1/4}·exp(D(log log x)^{1/4}(log log log x)^{−3/4}))`, using Deligne and the
  Voronoi formula.
- A. E. Ingham (1942): the positive-kernel and almost-periodicity method for Ω± from explicit
  oscillatory expansions.

These attributions are from memory and were not checked against the sources. The exponent
`(k−1)/2 + 1/10` is what this route gives from the repository's own upper bound. It is not a
literature value.
