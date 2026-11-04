# Rankin–Selberg asymptotic for τ: Karamata, `E(z,s)`, the strip Mellin identity (`RamanujanTau/EisensteinReal/`)

**Status (2026-11-04).** The asymptotic

    (1/N) ∑_{n≤N} τ(n)²/n¹¹  →  c = (3/π)(4π)¹² ‖Δ‖² / 11! = 0.384084054468170…

is proved in Lean, **conditional on one named hypothesis**: `HorocycleLimit L`, the equidistribution
of long closed horocycles for the single invariant function `G(z) = |Δ(z)|²(Im z)¹²`.
Everything else in the chain is axiom-clean: Karamata's Tauberian theorem, Abel summation,
Parseval (from `RankinSelberg/`), and the identification of the constant. The hypothesis is the
classical theorem of Zagier (1979) and Sarnak (1981). It is **equivalent** to the conclusion, by
the easy Abelian converse (paper level, not formalized). So all the depth of the asymptotic is in
this one statement. It is not yet proved.

Also done, axiom-clean: milestone E1 (the real-analytic Eisenstein series `E(z,s)` for real
`s > 1`, with convergence and `SL₂(ℤ)`-invariance), and the strip half E3a of the unfolding identity.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`.
Build only these files: `nice -n 10 lake build RamanujanTau.EisensteinReal.Main`.
Nothing in `RankinSelberg/`, `TauBound/` or `GORZXi/` was modified. The root `RamanujanTau.lean`
does not import these files.

| File | Lines | Content |
|---|---|---|
| `Karamata.lean` | 506 | Karamata's Tauberian theorem (Laplace / power-series form, real `ρ ≥ 1`) |
| `Asymptotic.lean` | 240 | Abel summation with a Cesàro mean; `HorocycleLimit`; the conditional asymptotic |
| `Mellin.lean` | 101 | E3a: `∫₀^∞ I(y) y^{s-2} dy = ∑ τ(n)² Γ(s+11)/(4πn)^{s+11}` in `[0,∞]` |
| `Eisenstein.lean` | 112 | E1: `E(z,s)` for real `s > 1`: summability, Γ-invariance, `E ≥ y^s` |
| `Main.lean` | 20 | imports and `#print axioms` |
| `scripts/eisensteinreal/horocycle_check.gp` | | numerics (PARI) |

## Headline theorems

### Evidence level 1 (Lean, axiom-clean, no hypotheses)

| Theorem | Statement |
|---|---|
| `karamata` | If `aₙ ≥ 0`, `∑ aₙe^{-nt}` converges for `t > 0`, and `t^ρ ∑ aₙe^{-nt} → K` as `t → 0⁺` with `ρ ≥ 1` (bundled as `KarHyp a ρ K`), then `(∑_{n≤N} aₙ)/N^ρ → K/Γ(ρ+1)`. |
| `tendsto_sum_div_pow` | If `(∑_{n≤N} bₙ)/N^{k+1} → α`, then `(∑_{n≤N} bₙ/nᵏ)/N → (k+1)α`. |
| `lintegral_mellin_horocycle` | For real `s > −11`: `∫⁻_{y>0} I(y) y^{s−2} dy = ∑' τ(n)² Γ(s+11)/(4πn)^{s+11}`, where `I(y) = ∫₀¹ G(x+iy) dx` (`Ihor`). |
| `summable_eSummand` | For `s > 1`, `v ↦ y^s |v₀z + v₁|^{−2s}` is summable over `ℤ²`. |
| `E_smul` | `E(γz, s) = E(z, s)` for `γ ∈ SL₂(ℤ)`, where `E(z,s) = ½ ∑_{gcd(c,d)=1} y^s|cz+d|^{−2s}`. |
| `E_ge`, `E_pos` | `E(z,s) ≥ y^s > 0` for `s > 1`. |

### Evidence level 2 (Lean, conditional on the named hypothesis `HorocycleLimit`)

```lean
def HorocycleLimit (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ y₀ > 0, ∀ (y : ℝ) (hy : 0 < y), y < y₀ →
    |(∫ x in (0:ℝ)..1, G (hp hy x)) - L| < ε
```

Here `G z = ‖Δ z‖² (Im z)¹²` is `RankinSelberg.G`, and `hp hy x = x + iy`.

| Theorem | Statement |
|---|---|
| `tendsto_sum_tau_sq_of_horocycle` | `HorocycleLimit L → (∑_{n≤N} τ(n)²)/N¹² → (4π)¹² L/12!` |
| **`rankinSelberg_asymptotic_of_horocycle`** | `HorocycleLimit L → (∑_{n≤N} τ(n)²/n¹¹)/N → (4π)¹² L/11!` |
| `horocycleLimit_pos` | `HorocycleLimit L → 0 < L` (using the unconditional `rankinSelberg_two_sided`) |
| **`rankinSelberg_asymptotic_of_zagier`** | `HorocycleLimit ((3/π)·petNormSq) → (∑_{n≤N} τ(n)²/n¹¹)/N → (3/π)(4π)¹² petNormSq/11!` |

`petNormSq` is defined as `∫_{0<y, |x|≤1/2, x²+y²≥1} G(x+iy) dx dy/y²`, which is `‖Δ‖²`.

## The chain, and a correction to the plan

1. **Parseval** (`RankinSelberg.hasSum_tau_sq`):
   `∑ τ(n)² e^{−nt} = ∫₀¹ |Δ(x + i t/4π)|² dx`. Hence `HorocycleLimit L` is the same statement
   as `t¹² ∑ τ(n)² e^{−nt} → (4π)¹² L`.
2. **Karamata** with `ρ = 12`. Put `S_t(f) = ∑ aₙe^{−nt} f(e^{−nt})` and
   `Λ(f) = Γ(ρ)⁻¹ ∫₀^∞ f(e^{−u}) e^{−u}u^{ρ−1} du`.
   * For monomials, `t^ρS_t(xᵐ) = t^ρF((m+1)t) → K(m+1)^{−ρ} = KΛ(xᵐ)`.
   * Induction over polynomials (`Polynomial.induction_on'`) extends this to every polynomial.
   * Weierstrass (`exists_polynomial_near_of_continuousOn`) plus a sandwich extends it to every
     continuous `f`.
   * Finally, the step function `g = x⁻¹·1[x ≥ e⁻¹]` lies between two continuous ramps. Their
     `Λ`-gap is at most `δ·8·2^{ρ−1}/(e^{−2}Γ(ρ))`, by a measure bound in `u` (`Lam_bump_le`).
   * At `t = 1/N`, `S_t(g) = ∑_{n≤N} aₙ`, and `Λ(g) = 1/Γ(ρ+1)`.
3. **Abel summation**:
   `∑_{n≤N} bₙ/nᵏ = A(N)/Nᵏ + ∑_{n<N} A(n)(n^{−k} − (n+1)^{−k})`.
   The factor `n^{k+1}(n^{−k} − (n+1)^{−k})` tends to `k`, by a Bernoulli squeeze. Then apply
   Mathlib's `Filter.Tendsto.cesaro`.

**Correction to milestone E4 as briefed.** The plan proposed using `D(s) ~ c/(s−1)` as `s → 1⁺`,
with `aₙ ≥ 0`, to get `∑_{n≤x} aₙ ~ cx`. That implication is **false**. Karamata/Hardy–Littlewood
applied to Dirichlet series gives only the logarithmic mean `∑_{n≤x} aₙ/n ~ c log x`.

Counterexample: take `bₙ = 1 + cos(log n) ≥ 0`. Then
`∑ bₙn^{−s} = ζ(s) + ½(ζ(s−i) + ζ(s+i)) ~ 1/(s−1)` as `s → 1⁺`. But
`∑_{n≤x} bₙ = x + Re(x^{1+i}/(1+i)) + O(log x)`, so the ratio `(∑_{n≤x} bₙ)/x` keeps oscillating
by `±1/√2`.

So knowing the pole at `s = 1` along the real axis (the "constant term of E and residue 3/π"
shortcut) cannot give the asymptotic. Two inputs do suffice:

* **(a)** the Laplace-side statement `t¹²F(t) → K`, which is `HorocycleLimit`, combined with
  Karamata (this is what is formalized here); or
* **(b)** the behaviour of `D(s)` on the whole line `Re s = 1`, combined with Wiener–Ikehara.

Route (b) needs `E(z,s)` continued to `Re s = 1` and `ζ(1+2it) ≠ 0`, together with Wiener–Ikehara,
which is about 1500 lines and is not in Mathlib. That is strictly more work than (a).

## Numerical evidence (level 4)

`scripts/eisensteinreal/horocycle_check.gp` (PARI, `nbthreads = 1`, 10⁵ coefficients):

* `‖Δ‖² = 1.0353620568043209223·10⁻⁶`, both from `mfpetersson` and from a direct double integral
  over the fundamental domain `𝓕` (which matches the definition of `petNormSq`). This gives
  `L = (3/π)‖Δ‖² = 9.8869793538119641441·10⁻⁷` and `c = 0.384084054468170370`.
* `I(y)/L` for `y` from 0.5 down to 0.0002:
  1.0659, 1.0134, 1.0419, 1.0052, 1.0065, 0.99552, 0.99740, 0.99810, 1.00056, 1.00079, 1.00031.
* `(I(y)/L − 1)/√y` stays in `[−0.05, +0.14]`, which fits Zagier's `O(y^{1/2})` error term.
* `docs/RANKIN_SELBERG.md` has `S(x)/x = 0.38403` at `x = 10⁵`.

## What remains: proving `HorocycleLimit`

Three routes.

**Route A: Eisenstein series / Zagier (as briefed).** Remaining work, with estimates:

| Piece | Lines |
|---|---|
| E1 for complex `s` and holomorphy in `s` (`differentiableOn_tsum_of_summable_norm`) | 200 |
| E2: Fourier expansion by Poisson summation in `d`. Mathlib has no `K`-Bessel function, so define it by its integral. Includes continuation to `Re s > 1/2`, `φ(s) = √π Γ(s−½)ζ(2s−1)/(Γ(s)ζ(2s))`, and its residue `3/π` | 1500–2200 |
| E3b: `ModularGroup.fd` as a measure-theoretic fundamental domain, and the unfolding `∫_{Γ\ℍ} G E dμ = ∫_{strip} G y^s dμ`. With E3a (done) this gives the Rankin–Selberg integral | 900–1300 |
| Zagier's step: growth of `⟨G, E(·,σ+it)⟩` in `t`, Mellin inversion of `I(y)` with the contour moved to `Re s = 1/2`, which gives `HorocycleLimit` with error `O(y^{1/2})` | 1200–2000 |

Total: about **3800–5700 lines**.

**Route B: Farey fractions and Ramanujan sums (recommended; cheaper, my own sketch, evidence level 3).**
It needs no `E(z,s)`, no spectral theory, and no measure-theoretic fundamental domain.

* **Write `G` as a sum over cosets.** Write `G = ∑_{Γ∞\Γ} h(γz)`, with `h = G·r(Im z)/E(z|r)`.
  Here `r ∈ C_c(0,∞)` is nonnegative and positive on `[√3/2, Y]`, and `E(·|r)` is the incomplete
  Eisenstein series, which is a finite sum locally. Cut off the cusp separately, using
  `sup_{Im ≥ Y} G → 0` on `𝓕`.
* **Unfold the horocycle integral.** Bruhat decomposition of `Γ∞\Γ/Γ∞` gives
  `I_h(y) = ∫₀¹ h + ∑_{c≥1} ∑*_{a mod c} ∫_ℝ h(a/c − 1/(c²(x+iy))) dx`.
* **Main term.** Expand `h` in Fourier modes in `Re`. Since `∑*_a e(ma/c) = c_c(m)` (Ramanujan
  sum), the `m = 0` term is `y ∑_c φ(c) F(c²y)`. By `∑_{c≤X} φ(c) ~ 3X²/π²`, it tends to
  `(3/π²)∫F = (3/π)∫_{strip} h dμ`.
* **Error terms.** For `m ≠ 0`, `|c_c(m)| ≤ gcd(c,m)`, so each term is `O_m(y^{1/2})`. A
  Fejér approximation in `Re` controls the tail in `m`.

Estimated cost: `∑φ ~ 3X²/π²` about 250 lines (Mathlib has `ζ(2) = π²/6`), the coset
parametrization and unfolding about 500, the Riemann-sum limit about 300, the Fourier truncation
about 300, the partition of unity and cusp cut-off about 500. Total about **1800–2500 lines**.

This route proves `∃ L, HorocycleLimit L` with
`L = (3/π)∫_{strip} h dμ`, and so `∑ τ²/n¹¹ ~ c x` for some `c > 0`. Identifying `L` with
`(3/π)‖Δ‖²` needs `∫_{strip} h dμ = ∫_𝓕 G dμ`, which is the only place `𝓕` enters.

**Route C: dynamics** (mixing of the geodesic flow, Margulis thickening; Sarnak, Dani–Smillie).
This is the heaviest route in Lean.

Error term `O(x^{3/5})`: unchanged from `docs/RANKIN_SELBERG.md`. It needs the functional
equation of `L(Δ⊗Δ, s)` and Landau's lemma.

## Literature

* J. Karamata, *Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes*,
  Math. Z. 32 (1930). The proof used here is the one in Titchmarsh, *Theory of Functions*, §7.53.
* D. Zagier, *Eisenstein series and the Riemann zeta function* (1981). The horocycle mean of a
  rapidly decaying `f` is `(3/π)∫f dμ + O(y^{1/2})`.
* P. Sarnak, *Asymptotic behavior of periodic orbits of the horocycle flow and Eisenstein series*,
  CPAM 34 (1981).
* R. A. Rankin (1939), A. Selberg (1940); H. Iwaniec, *Topics in Classical Automorphic Forms*, §13
  (unfolding) and §3 (Eisenstein series, Fourier expansion).
