# The Rankin–Selberg mean square of τ (`RamanujanTau/RankinSelberg/`)

**Status (2026-11-04).** First milestone reached, with no hypotheses: the mean square has the right
order of magnitude,

    c₁ N ≤ ∑_{n=1}^{N} τ(n)²/n¹¹ ≤ c₂ N     for every N ≥ 1     (rankinSelberg_two_sided)

and `∑_{n≤N} τ(n)²/n¹¹ = Θ(N)` (`rankinSelberg_isTheta`). No sorry, no new axiom, no `native_decide`.
Every headline prints `[propext, Classical.choice, Quot.sound]`.

The asymptotic `∑ ~ c·N` and the error term `O(N^{3/5})` are **not** proved. See "What remains".

Build (only these files): `nice -n 10 lake build RamanujanTau.RankinSelberg.Main`. The `#print axioms`
block at the end of `Main.lean` covers the headlines. None of these files is imported by the root
`RamanujanTau.lean`. Nothing in `TauBound/`, `WeilKloosterman/` or `StepanovAS/` was modified; only
`TauBound.Reduction` is imported, for the bridge `qExpansion_discriminant_coeff_tau`.

| File | Lines | Content |
|---|---|---|
| `Parseval.lean` | 129 | Parseval on a horizontal line for any level-one cusp form |
| `Upper.lean` | 183 | Hecke–Parseval upper bound; summation by parts |
| `Band.lean` | 168 | the invariant `G = |Δ|² y¹²`; `G ≥ m > 0` on a band; the Farey step |
| `Lower.lean` | 274 | counting coprime pairs; disjoint Farey intervals; the horocycle lower bound |
| `Main.lean` | 213 | truncation (tail) argument; the two-sided bound; `Θ` form |
| `scripts/rankinselberg/mean_square.gp` | | numerical check (PARI) |

## The constant

Unfolding `∫_{SL₂(ℤ)\ℍ} |Δ|² y¹² E(z,s) dμ` against the real-analytic Eisenstein series
`E(z,s) = ∑_{Γ∞\Γ} Im(γz)^s` (residue `3/π` at `s = 1`) gives
`Γ(s+11)(4π)^{-(s+11)} ∑ τ(n)² n^{-(s+11)}`. So `∑ (τ(n)²/n¹¹) n^{-s}` has a simple pole at `s = 1`
with residue

    c = (3/π) · (4π)¹² / 11! · ‖Δ‖²,     ‖Δ‖² = ∫_{SL₂(ℤ)\ℍ} |Δ(z)|² y¹² dx dy / y²,

and Rankin–Selberg says `∑_{n≤x} τ(n)²/n¹¹ = c x + O(x^{3/5})`. With PARI's
`‖Δ‖² = 1.0353620568043209223…·10⁻⁶` this is **`c = 0.384084054468170…`**. Equivalently,
`∑_{n≤x} τ(n)² ~ (c/12) x¹²`, with `c/12 = 0.0320070…`.

## Headline theorems (evidence level 1: Lean, axiom-clean, no hypotheses)

| Theorem | File | Statement |
|---|---|---|
| `hasSum_normSq_coeff` | `Parseval` | for `f` a cusp form of weight `k` for `SL₂(ℤ)` and `y > 0`: `∑ₙ |aₙ(f)|² e^{-4πny} = ∫₀¹ |f(x+iy)|² dx` |
| `hasSum_tau_sq` | `Upper` | `∑ τ(n)² e^{-4πny} = ∫₀¹ |Δ(x+iy)|² dx` |
| `exists_integral_le` | `Upper` | `∫₀¹ |Δ(x+iy)|² dx ≤ C/y¹²` |
| `exists_sum_tau_sq_le` | `Upper` | `∑_{n≤N} τ(n)² ≤ K N¹²` |
| `sum_div_pow_le` | `Upper` | summation by parts: `∑_{n≤N} bₙ ≤ K N^{k+1}` (with `bₙ ≥ 0`) implies `∑_{n≤N} bₙ/nᵏ ≤ (k+1)K N` |
| `exists_sum_tau_sq_div_le` | `Upper` | **upper bound** `∑_{n≤N} τ(n)²/n¹¹ ≤ K N` |
| `G_smul`, `exists_band_lower` | `Band` | `G(z) = |Δ(z)|²(Im z)¹²` is `SL₂(ℤ)`-invariant, and `G ≥ m > 0` on `4/5 ≤ Im z ≤ 16` |
| `exists_smul_mem_band`, `normSq_farey_lower` | `Band` | if `(a,c) = 1`, `1 ≤ a ≤ c ≤ C` and `a/c − x ∈ [1/(4cC), 1/(2cC)]`, some `γ` with bottom row `(c, −a)` puts `x + i/C²` in the band; hence `|Δ(x+i/C²)|² ≥ m C²⁴` |
| `card_fareyPairs_ge` | `Lower` | `#{(a,c) : 1 ≤ a ≤ c ≤ C, (a,c) = 1} ≥ C²/8` (union bound with `∑_{d≥2} d⁻² ≤ 3/4`, then symmetry) |
| `fareyJ_disjoint` | `Lower` | the Farey intervals `J(a,c) = [a/c − 1/(2cC), a/c − 1/(4cC)]` are pairwise disjoint, using `|ac' − a'c| < 1` |
| `integral_lower` | `Lower` | **horocycle lower bound** `∫₀¹ |Δ(x + i/C²)|² dx ≥ (m/32) C²⁴` for all `C ≥ 1` |
| `exists_sum_tau_sq_ge_trunc` | `Main` | `∑_{n≤L} τ(n)² ≥ (m/32)C²⁴ − e^{-2πL/C²}·K2¹²C²⁴` |
| `exists_sum_tau_sq_ge` | `Main` | `∑_{n≤N} τ(n)² ≥ k N¹²` |
| **`rankinSelberg_two_sided`** | `Main` | **`∃ c₁ c₂ > 0, ∀ N ≥ 1, c₁N ≤ ∑_{n=1}^N τ(n)²/n¹¹ ≤ c₂N`** |
| **`rankinSelberg_isTheta`** | `Main` | **`(N ↦ ∑_{n=1}^N τ(n)²/n¹¹) =Θ[atTop] (N ↦ N)`** |

Sums are `∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ))^2 / (n : ℝ)^11`, where `tau` is the repo's integer `τ`.
`Δf` is Mathlib's `CuspForm.discriminant`.

## The argument

1. **Parseval.** Write `|f|² = f·conj f = ∑ₙ f·conj(aₙqⁿ)`. Dominated convergence swaps `∫₀¹` and
   `∑`, with majorant `(C/y^{k/2})·|aₙ|e^{-2πny}`. Here `C/y^{k/2}` is Mathlib's
   `CuspFormClass.exists_bound`, and absolute summability comes from `hasSum_qExpansion` and
   `summable_norm_iff`. Then use `conj(qⁿ) = e^{-4πny}q^{-n}` and Mathlib's coefficient integral
   `aₙ = ∫₀¹ q^{-n}f`.
2. **Upper bound.** At `y = 1/(4πN)` every weight with `n ≤ N` is at least `e^{-1}`. This gives
   `∑_{n≤N} τ(n)² ≤ e·C²(4πN)¹²`. Summation by parts is an induction whose step uses Bernoulli's
   inequality, `1/xᵏ − 1/(x+1)ᵏ ≤ k/x^{k+1}`.
3. **Lower bound on the horocycle.** `G` is invariant: Mathlib's `norm_petersson_smul`. It is
   continuous and positive (`discriminant_ne_zero`), so it is `≥ m` on the compact set
   `[0,1]×[4/5,16]`, and by `T`-periodicity on the whole band. For `z = x + iy`, `y = 1/C²`, and
   `γ` with bottom row `(c, −a)`, we have `Im γz = y/(c²(x − a/c)² + c²y²)`. On `J(a,c)` this lies
   in `[4/5, 16]`. The intervals `J(a,c)` are disjoint and lie in `(0,1]`. There are at least `C²/8`
   of them, each of length `≥ 1/(4C²)`, so their total length is at least `1/32`.
4. **Truncation.** For `n > L` we have `e^{-4πny} ≤ e^{-2πLy}·e^{-4πn(y/2)}`. So the tail of
   `∑ τ(n)² e^{-4πny}` is at most `e^{-2πLy}` times the full sum at height `y/2`, which is at most
   `K2¹²C²⁴` by the upper bound. Take `L = λC²` with `λ ≥ 64·2¹²K/m + 1`; then
   `∑_{n≤λC²} τ(n)² ≥ (m/64)C²⁴`. For general `N`, take `C = ⌊√(N/λ)⌋`, and use `τ(1) = 1` when
   `N < λ`.

This proof uses no Eisenstein series, no fundamental-domain integration and no Tauberian theorem.
The constants `c₁`, `c₂` are not effective, because `m` comes from compactness.

## Numerical evidence (level 4)

`scripts/rankinselberg/mean_square.gp` (PARI, `nbthreads = 1`, `N = 10⁵`):

| x | S(x)/x | (S(x) − cx)/x^{3/5} | A(x)/x¹² |
|---|---|---|---|
| 10 | 0.42535 | +0.104 | 0.03383 |
| 100 | 0.38080 | −0.021 | 0.03122 |
| 1000 | 0.38210 | −0.031 | 0.02955 |
| 10⁴ | 0.38395 | −0.005 | 0.03185 |
| 3·10⁴ | 0.38413 | +0.003 | 0.03202 |
| 10⁵ | 0.38403 | −0.005 | 0.03196 |

Here `S(x) = ∑_{n≤x} τ(n)²/n¹¹` and `A(x) = ∑_{n≤x} τ(n)²`.

* Predicted values: `c = 0.384084` and `c/12 = 0.032007`.
* Over `1 ≤ x ≤ 10⁵`, `S(x)/x` lies in `[0.3593, 1]` and `A(x)/x¹²` lies in `[0.0121, 1]`. Both maxima
  occur at `x = 1`.
* The scaled error `(S(x) − cx)/x^{3/5}` stays small, consistent with `O(x^{3/5})`.
* Parseval check at `y = 0.2`: `∑ τ(n)²e^{-4πny} = 244.626404345742`, and a numerical integral of
  `|Δ(x+0.2i)|²` over `[0,1]` gives `244.626404346417`.

## What remains (assessment)

**Milestone 2: the asymptotic `∑_{n≤x} τ(n)²/n¹¹ ~ c x`.** This is not reached, and there is no
cheap route. It is equivalent to the equidistribution of long horocycles for the single function
`G`, namely `∫₀¹ G(x+iy)dx → (3/π)‖Δ‖²` as `y → 0`, combined with a Tauberian step. Both standard
proofs of horocycle equidistribution use spectral theory (Zagier's proof goes through `E(z,s)`) or
mixing. Mathlib has (checked 2026-11-04):

* **No** real-analytic or non-holomorphic Eisenstein series, and no Epstein zeta. The only
  Eisenstein series are the holomorphic ones (`EisensteinSeries`).
* **No** measure-theoretic statement that `ModularGroup.fd` is a fundamental domain, so no
  `∫_{Γ\ℍ}` and no unfolding over `Γ∞\Γ`. It has only `fd`, `fdo` and `exists_smul_mem_fd`, all
  set-theoretic.
* **No** Wiener–Ikehara or Karamata Tauberian theorem. Wiener–Ikehara is in PrimeNumberTheoremAnd,
  which is not a dependency.

Honest line estimates:

| Piece | Lines |
|---|---|
| `E(z,s)` for `Re s > 1`, its Fourier expansion (`K_{s−1/2}`-Bessel), and continuation to `Re s > 1/2` with simple pole and residue `3/π` (Chowla–Selberg / Poisson summation) | 2500–4000 |
| Fundamental domain as an `IsFundamentalDomain`, and the unfolding identity for `|Δ|²y¹²E(z,s)` | 1000–1500 |
| A Tauberian theorem. Karamata's, for the Laplace transform `∑ τ(n)²e^{-4πny} ~ c'y^{-12}`, is the cheapest; Weierstrass approximation is in Mathlib | 500–800 |

Total for `~ c x`: about **4000–6000 lines**.

**Milestone 3: the error term `O(x^{3/5})`.** On top of milestone 2 this needs the functional equation
of `E(z,s)` (hence of `L(Δ⊗Δ,s)`), a convexity or Phragmén–Lindelöf bound, and Landau's
contour/smoothing lemma. That adds another 2000–3000 lines.

A cheaper intermediate that is still not done: an upper bound `S(x)/x ≤ c₂` with an explicit `c₂`.
It would need an explicit bound for `|Δ(z)|y⁶`. The Weil bound `StepanovAS.weilPrimeBound` does not
help with the mean square; the Parseval route here is sharper and elementary.

## Literature

* R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n) and similar arithmetical
  functions I, II*, Proc. Cambridge Phil. Soc. 35 (1939).
* A. Selberg, *Bemerkungen über eine Dirichletsche Reihe, die mit der Theorie der Modulformen nahe
  verbunden ist*, Arch. Math. Naturvid. 43 (1940).
* H. Iwaniec, *Topics in Classical Automorphic Forms*, §13 (Rankin–Selberg unfolding), §3.2.
* D. Zagier, *Eisenstein series and the Riemann zeta function* (1981), on horocycle
  equidistribution.
* Hecke's mean-square argument: Iwaniec, *Topics*, §5.1, `∑_{n≤x}|aₙ|² ≪ x^k`. This is the upper
  half here, and is classical.
