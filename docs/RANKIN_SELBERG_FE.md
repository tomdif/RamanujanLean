# The Rankin–Selberg theorem proper for `Δ` (`RamanujanTau/RankinSelbergFE/`)

**Status (2026-11-05).** Proved in Lean at evidence level 1 (axiom-clean, no hypotheses):

* the meromorphic continuation of `R(s) = ∑ τ(n)² n^{−11−s}` to all of `ℂ`;
* the functional equation `R*(1−s) = R*(s)` of the completed function;
* `R*` has only simple poles, at `s = 1` and `s = 0`, with residues `‖Δ‖²` and `−‖Δ‖²`;
* the residue of `R` itself at `s = 1` is `(3/π)(4π)¹²‖Δ‖²/11!`, which is Zagier's constant.

Separately, and new to the repo: the continuation and functional equation of the completed
real-analytic Eisenstein series `E*(z,s) = π^{−s}Γ(s)ζ(2s)E(z,s)` for each fixed `z ∈ ℍ`.

There is no sorry, no new axiom and no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`.

To build: `nice -n 10 lake build RamanujanTau.RankinSelbergFE.Main` (exits 0). The public entry point is included in the root import graph.

## Normalization

    R(s)  = ∑_{n≥1} τ(n)² n^{−11−s}                    (EdgeNonvanishing.RS; converges for Re s > 1)
    γ(s)  = 2 π^{−s} Γ(s) Γ(s+11) (4π)^{−s−11}           (RankinError.gam)
    R*(s) = γ(s) ζ(2s) R(s)                             (Re s > 1), continued to ℂ ∖ {0,1}

Equivalently, `R*(s) = 2 ∫_𝓕 y¹²|Δ|² E*(z,s) dμ` with `E*(z,s) = π^{−s}Γ(s)ζ(2s)E(z,s)`. The
factor 2 appears because the full lattice theta function is used: `Θ − 1 ↔ 2E*`. In Lean,
`R*` is `rsFE.Λ`, the Mellin transform of `Φ(t) − ‖Δ‖²`, where
`Φ(t) = ∫_𝓕 |Δ|²y¹² Θ_z(t) dμ` and `Θ_z(t) = ∑_{(m,n)} e^{−πt|mz+n|²/y}`.

## Headline theorems (all in `RamanujanTau.RankinSelbergFE`, evidence level 1)

### `Proper.lean`: the Rankin–Selberg theorem

| Theorem | Statement |
|---|---|
| `RStar_one_sub` | `RStar (1 - s) = RStar s` for all `s : ℂ` |
| `RStar_eq` | `RStar s = RStar₀ s − ‖Δ‖²/s − ‖Δ‖²/(1−s)` for all `s` |
| `differentiable_RStar₀`, `RStar₀_one_sub` | `RStar₀` is entire, and `RStar₀(1−s) = RStar₀(s)` |
| `differentiableAt_RStar` | `s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ RStar s` |
| `RStar_residue_one` | `(s−1)·R*(s) → ‖Δ‖²` as `s → 1`, `s ≠ 1` |
| `RStar_residue_zero` | `s·R*(s) → −‖Δ‖²` as `s → 0`, `s ≠ 0` |
| `petNormSq_ne_zero` | `‖Δ‖² ≠ 0`, so both poles really are simple poles |
| `RStar_eq_of_one_lt` | `1 < Re s → RStar s = gam s * riemannZeta (2s) * RS s` |
| `RStar_eq_of_one_lt'` | the same, with `γ` and the series `∑ τ(n)²/n¹¹ · n^{−s}` written out |
| `meromorphicAt_riemannZeta` | `ζ` is meromorphic at every point (Mathlib has no such lemma) |
| `meromorphic_Rcont` | `Rcont := R* · γ⁻¹ / ζ(2·)` is `MeromorphicOn` all of `ℂ` |
| `Rcont_eq` | `1 < Re s → Rcont s = RS s`, so `Rcont` continues `R` |
| `differentiableAt_Rcont` | `Rcont` is holomorphic off `{0, ½, 1}` and the zeros of `ζ(2s)` |
| **`Rcont_residue_one`** | `(s−1)·R(s) → rsc = (3/π)(4π)¹²‖Δ‖²/11!` as `s → 1` |

`Rcont_residue_one` agrees with the constant in the repo's independently proved asymptotic
`∑_{n≤N} τ(n)²/n¹¹ ∼ rsc·N`. This is a consistency check between the spectral route and the
horocycle route.

### `Theta.lean`, `Lattice.lean`, `Epstein.lean`, `EpsteinE.lean`: `E*(z,s)` for fixed `z`

| Theorem | Statement |
|---|---|
| `tsum_gauss_shift` | `∑ₙ e^{−πu(n−w)²} = u^{−1/2} ∑ₖ e^{−πk²/u} cos 2πkw` (from Mathlib's `Complex.tsum_exp_neg_quadratic`) |
| `theta_inv` | `Θ(z,1/t) = t·Θ(z,t)`, where `Θ(z,t) = ∑_{(a,c)∈ℤ²} e^{−πt|a−cz|²/Im z}` (2-D Poisson summation, done as two 1-D Poisson steps) |
| `nzEquiv`, `tsum_decomp` | `ℤ² ∖ 0 ≃ ℕ × {(a,c) coprime}`, `v = (k+1)·(a,c)` |
| `im_inv_mat`, `ofReal_Theta` | `Im(M_{(a,c)}⁻¹z) = 1/Q_z(a,c)`; `Θ = 1 + ∑_{coprime} H_t(Im M⁻¹z)` |
| `thetaFE z` | `WeakFEPair ℂ` for `(Θ(z,·), Θ(z,·))` with `k = 1`, `ε = 1`, `f₀ = g₀ = 1`. Decay: `Θ(z,t) − 1 ≤ e^{−π min(y,1/y)(t−1)}(Θ(z,1) − 1)` |
| `EpsteinStar_one_sub` | `E*(z,1−s) = E*(z,s)` for all `s` |
| `differentiableAt_EpsteinStar` | `E*(z,·)` is holomorphic on `ℂ ∖ {0,1}` |
| `EpsteinStar_residue_one`, `_zero` | residues `1` at `s = 1` and `−1` at `s = 0` |
| `hasSum_EpsteinStar` | `Re s > 1`: `E*(z,s) = ∑_{v≠0} Γ(s)(π Q_z(v))^{−s}`, where `Q_z(a,c) = \|a−cz\|²/y` |
| `tsum_lq_rpow` | real `σ > 1`: `∑_{v≠0} Q_z(v)^{−σ} = ζ(2σ)·2E(z,σ)` |
| **`EpsteinStar_ofReal`** | real `σ > 1`: `E*(z,σ) = 2π^{−σ}Γ(σ)ζ(2σ)E(z,σ)`, with the repo's `EisensteinReal.E` |

So `EpsteinStar z / 2` continues `π^{−s}Γ(s)ζ(2s)E(z,s)` to `ℂ ∖ {0,1}`, with functional
equation `s ↔ 1−s`.

| File | Lines | Content |
|---|---|---|
| `Theta.lean` | 238 | shifted-Gaussian Poisson, the lattice theta `Θ(z,t)`, summability, `theta_inv` |
| `Lattice.lean` | 186 | `ℤ²∖0 ≃ ℕ × copSet`, inverse coset matrices, primitive decomposition of `Θ` |
| `Epstein.lean` | 251 | `thetaFE`, `E*(z,s)`: FE, poles, residues, Dirichlet series (via Mathlib `hasSum_mellin`) |
| `EpsteinE.lean` | 123 | `∑_{v≠0} Q^{−σ} = 2ζ(2σ)E(z,σ)`, so `E*(z,σ) = 2π^{−σ}Γ(σ)ζ(2σ)E(z,σ)` |
| `Proper.lean` | 233 | the Rankin–Selberg theorem proper (on top of `RankinError.rsFE`, `rsUnfold`) |
| `Main.lean` | 37 | imports and `#print axioms` |

## Feasibility survey (what existed and what was missing)

**What Mathlib has (May 2026 snapshot).**

* `NumberTheory/LSeries/AbstractFuncEq.lean`. `WeakFEPair` gives the meromorphic
  continuation, the functional equation and the residues of Mellin transforms, provided
  `f(1/x) = ε x^k g(x)` and `f − f₀` decays rapidly. This is the engine for both results.
* `Complex.tsum_exp_neg_quadratic`: 1-D Poisson summation for Gaussians.
  `jacobiTheta₂_functional_equation`.
* `UpperHalfPlane.Measure`: the `GL₂(ℝ)`-invariant measure `dx dy/y²` on `ℍ`.
* `ModularGroup.fd`/`fdo` and their uniqueness lemmas; `hasSum_mellin` (Mellin transform =
  Dirichlet series).
* Mathlib does **not** have the real-analytic `E(z,s)`, the Epstein zeta function, K-Bessel
  functions, or a Fourier expansion of `E(z,s)`. It also has no `MeromorphicAt` lemma for `ζ`
  (proved here as `meromorphicAt_riemannZeta`).

**What the repo already had.**

* `EisensteinReal/`: `E(z,s)` for real `s > 1` only (summability, invariance, `E ≥ y^s`),
  the strip Mellin identity, and the unconditional asymptotic. There was no continuation
  and no functional equation of `E`.
* `RankinError/` (Route B for the power saving). It already contains the hardest
  infrastructure:
  * `Theta.lean`: `theta_inv` in `(x, y)` coordinates;
  * `HMeasure.lean`: the `ℍ`-measure in real coordinates and the unfolding over `U`;
  * `ThetaInt.lean`: `Φ(t)` with `Φ(1/t) = tΦ(t)` and its decay;
  * `RSFE.lean`: `rsFE : WeakFEPair ℂ`, with `Λ₀` entire, `Λ₀(1−s) = Λ₀(s)`, and bounded on
    strips;
  * `RSUnfoldProof.lean`: `rsUnfold`, i.e. `mellin(Φ − ‖Δ‖²) = γ(s)ζ(2s)R(s)` for `Re s > 2`.

  What was missing was the statement of the theorem proper: the completed `R*` as a function
  on `ℂ`, the identity on the whole half-plane `Re s > 1`, the residues, the meromorphic
  continuation of `R` itself, and the residue of `R` at `1`. `Proper.lean` adds these in about
  230 lines.
* The real-analytic Eisenstein series had no functional equation anywhere. `Theta`,
  `Lattice`, `Epstein` and `EpsteinE` (about 800 lines) prove it by the lattice-theta route.
  `Theta.lean` re-derives the 2-D Poisson formula in `ℍ`-native notation (the content is the
  same as `RankinError/Theta.lean`). It was written before `RankinError` was found, and was
  kept because the `E*` files are phrased in terms of `z : ℍ` and `Q_z`.

**Route chosen.** The lattice theta function plus `WeakFEPair`. It needs no K-Bessel
functions, no Fourier expansion in `x` and no spectral theory. For `R*`, the analytic input
(the fundamental-domain unfolding) was already proved in `RankinError`. Here the identity is
extended from `Re s > 2` to `Re s > 1` by the identity theorem: `LSeries` is holomorphic for
`Re s > 1`, using `rs_summable`.

## Gaps and what is *not* claimed

1. The classical integral form `R*(s) = 2∫_𝓕 y¹²|Δ|²E*(z,s) dμ`, valid for all `s ≠ 0, 1`
   after continuation (it needs `E*(z,s)` continued inside the integral, with uniform bounds
   in `z` on `𝓕`), is not stated. The continuation here goes through
   `Φ(t) = ∫_𝓕 G Θ_z(t) dμ` instead. Linking the two would need a dominated-convergence
   argument for `E*(z,s) = ½∫(Θ_z(t)−1)t^{s−1}dt` uniformly on `𝓕`, plus the cusp growth
   `E*(z,s) ≪ y^{max(σ,1−σ)}`. Estimate: 300–500 lines.
2. Poles of `Rcont` other than `s = 1`. `R(s)` can have poles where `ζ(2s) = 0`. Nothing is
   claimed about them. `differentiableAt_Rcont` only says that `Rcont` is holomorphic away
   from those points and from `0, ½, 1`.
3. The identification `EpsteinStar_ofReal` with the repo's `E(z,s)` is for real `σ > 1`, because
   `EisensteinReal.E` is only defined for real `s`. For complex `s` with `Re s > 1` the
   Dirichlet-series form `hasSum_EpsteinStar` holds.
4. No Fourier expansion of `E(z,s)` and no K-Bessel functions. Neither is needed for anything
   above.

## Literature

Rankin (1939); Selberg (1940); Zagier, *The Rankin–Selberg method for automorphic functions
which are not of rapid decay* (1981); Bump, *Automorphic Forms and Representations* §1.6;
Iwaniec–Kowalski §5.12 and §13.8 (Rankin–Selberg convolutions); Iwaniec, *Spectral
Methods* ch. 3 (the theta and Poisson route to `E*(z,s) = E*(z,1−s)`).
