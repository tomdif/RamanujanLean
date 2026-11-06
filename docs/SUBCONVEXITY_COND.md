# Conditional t-aspect subconvexity for `L(Δ,s)` from a shifted-convolution bound

**Status (2026-11-05).** This is the "conditional milestone" of `docs/SUBCONVEXITY.md` §5, done in a
form adapted to the repo. It is **evidence level 2**: Lean, axiom-clean, conditional on one named
arithmetic hypothesis class.

    nice -n 10 lake build RamanujanTau.SubconvexityCond.Main      # exits 0

* Every headline `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/SubconvexityCond/`.
* The directory has 11 files and about 1,760 lines.
* No existing file was modified.

## 1. The hypothesis

With `λ(n) = τ(n) n^{−11/2}` (`lam`) and `A_h(N) = Σ_{n=1}^{N} λ(n)λ(n+h)` (`shiftSum h N`):

```lean
class ShiftedConvolutionBound (η B : ℝ) : Prop where
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B
```

The hypothesis is a bound on the sharp shifted sums of the Fourier coefficients of `Δ`, and nothing
else. It says nothing about `L(Δ,s)`, about its mean values, or about Dirichlet polynomials.

How it relates to the usual form:

* For `h ≤ N` it is the classical statement `Σ_{n≤N} λ(n)λ(n+h) ≪ N^{1−η} h^B`.
* For `h > N` and `B ≥ η` it follows from the trivial bound. Cauchy–Schwarz plus Rankin give
  `|A_h(N)| ≤ A√(N(N+h)) ≤ A(N+h)`, which is at most `2A(N+h)^{1−η}h^{B}` in that range.

**Why it is true (literature, not formalized; citations from memory, not re-checked).**

* Selberg (1965, *On the estimation of Fourier coefficients of modular forms*) analytically
  continues the shifted Dirichlet series `D_h(s) = Σ a(n)a(n+h) n^{-s}`. He uses Poincaré series
  and Weil's Kloosterman bound, and deduces `Σ_{n≤x} a(n)a(n+h) ≪ x^{k−1/3+ε}`. Normalized, that is
  `≪ x^{2/3+ε}` for fixed `h`, with polynomial dependence on `h`.
* Good (1981–83) and Jutila (1987) give the same `x^{2/3}` exponent for sharp sums, with explicit
  uniformity in `h`.
* Smooth sums have better exponents: `x^{1/2+θ+ε}` (Blomer 2004; Blomer–Harcos), and
  `x^{1/2+ε}` with Kim–Sarnak's `θ = 7/64`. Here, though, the class is stated for **sharp** sums.
* So `SCS(η, B)` should hold for every `η < 1/3` with some fixed `B`.
* `B = 1` already suffices for the following reason. For `h ≥ N^{η}` the trivial bound
  `≪ N + h ≤ 2N·(h/N^η)` covers the range. That leaves only `h ≤ N^{1/3}`, where the Selberg/Good
  bound with at most polynomial `h`-loss applies.
* The exact power of `h` in Selberg/Good should be checked against the papers, or against Iwaniec,
  *Spectral Methods*, Ch. 3, before any claim beyond "some B" is made.

**Sanity checks on the class.**

* `shiftedConvolutionBound_trivial : ShiftedConvolutionBound 0 0` holds unconditionally. The proof
  is Cauchy–Schwarz plus Rankin, `HeckeConvex.exists_sum_sq_div_le`. So the class is not vacuous,
  and its `η = 0` instance is exactly the trivial bound.
* `subconvexDelta_zero : subconvexDelta 0 B = 0`. With no saving in the shifted sums the method
  saves nothing, which is convexity (`HeckeConvex.tauL_convexity`). The main theorem needs `η > 0`.
* `ShiftedConvolutionBound.mono`: smaller `η` and larger `B` give weaker statements.
* **Absurd values are visibly false.** Take `η > 1` with fixed `h`. The class then forces
  `A_h(N) → 0`, so `λ(n)λ(n+h) → 0`. That contradicts Sato–Tate type equidistribution and also
  contradicts the expected size `|A_h(N)| ≍ N^{1/2}` of the Rankin–Selberg cross terms.
  * This is **not** proved in Lean.
  * The partial-sum bound in the repo (Wilton's `x^{1/2}·log`) is too weak by a log to refute
    `η > 1 + B` formally.
  * The theorem itself only uses `0 < η ≤ 1`. `exists_subconvex_of_SCS` reduces any `η > 0` to
    `min η 1` by monotonicity.

## 2. Headline theorems (`Final.lean`)

```lean
theorem tauL_subconvex_of_SCS {η B : ℝ} [ShiftedConvolutionBound η B]
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta η B)
-- subconvexDelta η B = η / (10 B + 24)

theorem exists_subconvex_of_SCS {η B : ℝ} (h : ShiftedConvolutionBound η B) (hη0 : 0 < η)
    (hB : 0 ≤ B) : ∃ δ > 0, ∃ C ≥ 0, ∀ t, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - δ)
```

For example, the literature-expected `SCS(1/3 − ε, 1)` gives `δ ≈ 1/102`, so
`|L(Δ,6+it)| ≪ |t|^{1/2 − 1/102}`. The exponent is deliberately crude: no `ε` appears, and log
losses are absorbed by spending part of the saving. The optimal output of this method would be
`δ = η/(2(1+B))`.

## 3. The proof (all steps proved in Lean)

The pipeline differs from the doc's plan in two ways that save a lot of work:

* There is **no two-sided AFE**. The repo's one-sided Riesz–Perron approximation already suffices
  once the length is `X = T^{1+4δ}`.
* The pointwise step is applied to the **Dirichlet polynomial**, by Gallagher's inequality, not to
  `L` itself. So no pointwise-from-mean lemma for `L`, and no Cauchy-formula argument, is needed.

| Step | File | Statement |
|---|---|---|
| approximation | (repo) `MeanSquare.approx_tauL` with `σ=6, δ=1/2, ε=δ` | `‖L(6+iT) − Σ_{n≤X} τ(n)(1−n/X)³ n^{−6−iT}‖ ≤ C X^{−1/2}(1+T)^{1+δ}`, which is `≪ T^{1/2−δ}` for `X=T^{1+4δ}` |
| coefficients | `Coeff.lean` | `dpoly_bsm_eq`: that polynomial is `Σ λ(n) g_X(n) n^{−iT}` with `g_X(n) = (1−n/X)₊³/√n`; `gBound_gX`, `gBound_gX_log` give `|g| ≤ K n^{−1/2}`, `|Δg| ≤ K n^{−3/2}`, and support `≤ ⌊X⌋` |
| Gaussian window | `Gauss.lean` | `integral_gw_cos`: `∫ e^{−((t−T)/H)²} cos(lt) dt = H√π e^{−(Hl)²/4} cos(lT)` (from Mathlib's `integral_cexp_quadratic`) |
| exact mean value | `Expand.lean` | `integral_gw_normSq`: `∫ w|P|² = H√π Σ_{m,n} a_m a_n e^{−(H log(n/m))²/4} cos(T log(n/m))`; `reindex_symm` groups the sum by `h = m−n`; `integral_gw_normSq_le` bounds it by `H√π(Σaₙ² + 2Σ_h |S_h|)` |
| off-diagonal, one `h` | `Kernel.lean`, `OffDiag.lean` | `offS_bound`: Abel summation of `S_h = Σ λ(n)λ(n+h)·G_h(n)` against `A_h(n)`. `G_h = g(n+h)g(n)E_h(n)cos(Tℓ_h(n))`, `ℓ_h = log(1+h/n)`. The variation uses `|Δu| ≤ 2K²/n²`, monotonicity of `E_h`, and `|Δcos| ≤ |T|h/n²`. The range `nρ < hH` is killed by `E_h ≤ e^{−ρ²/64}` (`Ef_small`); the band `n ≥ hH/ρ` uses the hypothesis |
| mean value | `MeanValue.lean` | `mean_value_bound`: `∫ w|P|² ≤ H√πK²(Σλ²/n + 4CN^{3+B}(3+TN)e^{−ρ²/64} + 4C(Nρ/H)^{1+B}(H/ρ)^{−η}((2+Tρ/H)(1+log N)+1))` |
| pointwise | `Pointwise.lean` | `norm_sq_le_window`: `|P(T)|² ≤ 2e(∫w|P|² + ∫w|P_log|²)`, by FTC on `[T,t]`, averaging over `[T,T+1]`, `(∫f)² ≤ ∫f²`, and `w ≥ e^{−1}` |
| bookkeeping | `Assembly.lean`, `Final.lean` | `ρ=T^{2δ}`, `H=T^{1−4δ}`. Since `η = 2δ(5B+12)`, the band term is `≤ 4(1+log X)`, the diagonal is `≤ RS(12+δ/4) T^{δ/2}`, and the far term is bounded via `exp_poly_bound`. This gives `rpoly_bound`: `|P(T)| ≪ T^{1/2−δ}`. Then `t ≤ −1` follows by `tauL_conj`, and `|t| ≤ 1` by convexity |

## 4. Gaps and honest caveats

* **The hypothesis is not proved.** Proving `SCS(η,B)` for some `η > 0` is steps b1–b4 of
  `docs/SUBCONVEXITY.md`: Poincaré series, Kloosterman expansion, Weil, and Mellin inversion. That
  is roughly 2–3k more lines. The input is unconditional in the literature.
* The class uses **sharp** cutoffs and the `(N+h)^{1−η}` normalization. That is a slightly
  nonstandard packaging, equivalent to the usual one for `h ≤ N`. Smooth-weight SCS, which has
  better exponents, would need a smooth-to-sharp step or a re-derivation with smooth weights. Both
  are easy in principle but not done.
* The exponent `δ = η/(10B+24)` is not optimized. With `B=1` and `η→1/3` it is about `1/102`,
  versus `1/6` for Good/Jutila. That is fine for "subconvexity", not for records.
* Pre-existing inputs used, all axiom-clean repo theorems:
  * `MeanSquare.approx_tauL` (Perron plus contour shift plus convexity strip);
  * `HeckeConvex.tauL_convexity`;
  * `HeckeZeros.tauL_conj`;
  * Rankin's `HeckeConvex.exists_sum_sq_div_le`;
  * `MeanSquare.sum_tau_sq_rpow_le`.
