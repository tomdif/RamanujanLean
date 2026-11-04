# Rankin–Selberg asymptotic for τ: Karamata, horocycle equidistribution, `E(z,s)` (`RamanujanTau/EisensteinReal/`)

**Status (2026-11-04, Route B completed).** The asymptotic

    (1/N) ∑_{n≤N} τ(n)²/n¹¹  →  c = (3/π)(4π)¹² ‖Δ‖² / 11! = 0.384084054468170…

is now proved in Lean **unconditionally**, with Zagier's constant
(`rankinSelberg_asymptotic_zagier_unconditional`). The former named hypothesis
`HorocycleLimit L` (equidistribution of long closed horocycles for `G(z) = |Δ(z)|²(Im z)¹²`) is
discharged: `horocycleLimit_zagier : HorocycleLimit ((3/π)·petNormSq)`, and also the bare
existence `exists_horocycleLimit : ∃ L, HorocycleLimit L`. The proof is the elementary Route B
below (lattice-point counts, Möbius, a sandwich): no `E(z,s)`, no spectral theory, no Fourier
expansion in `x`, no `K`-Bessel functions.

Also done, axiom-clean: Karamata's Tauberian theorem, Abel summation, milestone E1 (the
real-analytic Eisenstein series `E(z,s)` for real `s > 1`), and the strip half E3a of the
unfolding identity. Those remain, but `E(z,s)` is no longer needed for the asymptotic.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`.
Build only these files: `nice -n 10 lake build RamanujanTau.EisensteinReal.HoroIdent`
(this imports everything in this directory except `Mellin`/`Eisenstein`; for those use
`lake build RamanujanTau.EisensteinReal.Main`).
Nothing outside `EisensteinReal/` was modified, and the files `Karamata`, `Asymptotic`, `Mellin`,
`Eisenstein`, `Main` are unchanged. The root `RamanujanTau.lean` does not import these files.

| File | Lines | Content |
|---|---|---|
| `Karamata.lean` | 506 | Karamata's Tauberian theorem (Laplace / power-series form, real `ρ ≥ 1`) |
| `Asymptotic.lean` | 240 | Abel summation with a Cesàro mean; `HorocycleLimit`; the conditional asymptotic |
| `Mellin.lean` | 101 | E3a: `∫₀^∞ I(y) y^{s-2} dy = ∑ τ(n)² Γ(s+11)/(4πn)^{s+11}` in `[0,∞]` |
| `Eisenstein.lean` | 112 | E1: `E(z,s)` for real `s > 1`: summability, Γ-invariance, `E ≥ y^s` |
| `Main.lean` | 20 | imports and `#print axioms` (unchanged; does not import the `Horo*` files) |
| `HoroArith.lean` | 409 | coprime count in an interval (Möbius), divisor rearrangement, harmonic error, Riemann sum for `√(1−t²)`, dominated convergence for `∑ μ(e)/e²·S(se)` |
| `HoroUnfold.lean` | 163 | `SL₂(ℤ) ≃ {(a,c) coprime} × ℤ`; unfolding `∫₀¹ ∑_γ F(γz) dx = ∑_{(a,c)} ∫_ℝ F(M(a,c)z) dx` |
| `HoroCount.lean` | 325 | rectangle count `N_R`, its horocycle mean as `2∑_{c≥1} G(c)`, two-sided bounds on `G(c)` |
| `HoroLimit.lean` | 336 | explicit error bound and the limit `∫₀¹ N_R(x+iy) dx → K₀(β−α)/A` |
| `HoroSandwich.lean` | 270 | fundamental-domain facts (orbit meets `U`; meets `S` only at `±γ`); box counts |
| `HoroMain.lean` | 444 | the `1/K`-grid adapted to the arc, pointwise upper/lower bounds for `G` |
| `HoroFinal.lean` | 417 | integration, gap bound, Cauchy argument: `∃ L, HorocycleLimit L` and the unconditional asymptotic |
| `HoroConst.lean` | 74 | `κ = ∑μ(e)/e² = 6/π²`, `W = π/4`, `K₀ = 6/π` |
| `HoroIdent.lean` | 575 | `∑c⁻μ ≤ ‖Δ‖² ≤ ∑c⁺μ + M/L` (Fubini on boxes), hence `L = (3/π)‖Δ‖²` |
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
| **`rankinSelberg_asymptotic_zagier_unconditional`** | `(∑_{n≤N} τ(n)²/n¹¹)/N → (3/π)(4π)¹²·petNormSq/11!` (no hypotheses) |
| **`horocycleLimit_zagier`** | `HorocycleLimit ((3/π)·petNormSq)`: `∫₀¹ G(x+iy) dx → (3/π)‖Δ‖²` |
| **`exists_horocycleLimit`** | `∃ L, HorocycleLimit L` |
| **`rankinSelberg_asymptotic_unconditional`** | `∃ c > 0, (∑_{n≤N} τ(n)²/n¹¹)/N → c` |
| `sum_tau_sq_asymptotic_unconditional` | `∃ c > 0, (∑_{n≤N} τ(n)²)/N¹² → c` |
| `Horo.tendsto_horoR_const` | for `α ≤ β`, `A > 0`: `∫₀¹ #{γ ∈ SL₂(ℤ) : γ(x+iy) ∈ [α,β)×[A,∞)} dx → (6/π)(β−α)/A` |
| `Horo.horo_bound` | explicit error: for `0<y<A`, `Ay ≤ 1`, `s=√(Ay)`: `|mean − 4(β−α)T(s)/A| ≤ (4s/A)(1+log(1/s))²` |
| `Horo.lintegral_unfold` | `∫₀¹ ∑_{γ∈SL₂(ℤ)} F(γ(x+iy)) dx = ∑_{(a,c) coprime} ∫_ℝ F(M(a,c)(x+iy)) dx` for measurable `F ≥ 0` |
| `Horo.coprimeCount_bound` | `|#{a ∈ [u,v) : (a,c)=1} − (v−u)∑_{e∣c}μ(e)/e| ≤ d(c)` |
| `Horo.smul_mem_S_unique` | if `γz, γ′z ∈ {−½ ≤ Re < ½, |w|>1}` then `γ′ = ±γ` |
| `Horo.petNormSq_ge`, `Horo.petNormSq_le` | the grid brackets `‖Δ‖²` |
| `Horo.kappa_eq`, `Horo.Wc_eq` | `∑ μ(e)/e² = 6/π²`, `∫₀¹ √(1−t²) dt = π/4` |

### Evidence level 1, reduction steps (Lean; formerly the only route, now fed by `horocycleLimit_zagier`)

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
* Rectangle counts (Python, direct enumeration of `(c,d)`, 5000–20000 points in `x`). The
  horocycle mean of `N_R` divided by `(6/π)(β−α)/A` is 0.986–1.004 for `y ∈ {10⁻³, 10⁻⁴, 10⁻⁵}`
  and three rectangles. This was checked before formalizing `tendsto_horoR_const`.

## How `HorocycleLimit` is proved (Route B, as formalized)

The previous sketch (Fourier modes in `x`, Ramanujan sums, a partition of unity) was checked on
paper and then **simplified**: no Fourier expansion and no partition of unity are needed. The
formalized argument has four steps.

1. **Unfold a lattice-point count** (`HoroUnfold`, `HoroCount`). For the rectangle
   `R = [α,β) × [A,∞)` put `N_R(z) = #{γ ∈ SL₂(ℤ) : γz ∈ R}` (summed over the whole group, so
   no periodization and no choice of coset representatives). Writing `γ = M(a,c)·Tᵏ` with left
   column `(a,c)` gives `∫₀¹ N_R(x+iy) dx = ∑_{(a,c)} ∫_ℝ 1_R(a/c − 1/(c²(x+iy))) dx`. For
   `y < A` the `c = 0` terms vanish, `±(a,c)` contribute equally, and for `c ≥ 1` the inner sum
   over `a` is the number of `a` coprime to `c` in an interval of length `c(β−α)`.
2. **Möbius** (`HoroArith.coprimeCount_bound`): that number is `c(β−α)ν(c) + O(d(c))`, with
   `ν(c) = ∑_{e∣c}μ(e)/e`. The `x`-measure of `{A ≤ y/(c²(x²+y²))}` is
   `λ_c = 2√(y/(Ac²) − y²)`.
3. **Limit** (`HoroLimit`). With `s = √(Ay)` and `w(t) = √(1−t²)`:
   `∑_c cν(c)λ_c = (2/A)∑_e μ(e)/e² · S(se)`, where `S(h) = ∑_{1≤m≤1/h} h·w(mh)`, so
   `|S(h) − ∫₀¹w| ≤ h`, and dominated convergence applies. The error is
   `∑_c d(c)λ_c ≤ (2s/A)(1+log(1/s))²`. So the mean tends to `4κW(β−α)/A = (6/π)(β−α)/A`.
4. **Sandwich** (`HoroSandwich`, `HoroMain`, `HoroFinal`). Two facts about `SL₂(ℤ)` are used:
   every orbit meets `U = {−½ ≤ Re < ½, |w| ≥ 1}`, and an orbit meets
   `S = {−½ ≤ Re < ½, |w| > 1}` only at `±γ`. A `1/K`-grid of boxes, adapted column by column
   to the arc (`√(1−x²)` is 1-Lipschitz on `[−½,½]`), plus uniform continuity of `G` on
   `[−½,½]×[¼, L+2]` gives
   `∑_γ lo(γz) ≤ 2G(z) ≤ ∑_γ up(γz)`. Here `up`/`lo` are box combinations with coefficients
   `G(corner) ± δ`, and `up` has one cusp rectangle with coefficient `M = sup G`. Each box count
   has a horocycle limit, and the two limits differ by at most
   `|K₀|(16(M+δ)/K + 8δL + M/L)`. A Cauchy argument then gives `∃ L`.
   **Identification** (`HoroIdent`): the same grid brackets
   `‖Δ‖² = ∫_𝓕 G dx dy/y²`, because `∫_{box} dx dy/y² = (β−α)(1/a−1/b)` by Fubini, which matches
   the box-count limit. With `K₀/2 = 3/π` (`κ = 6/π²` from `L(μ,2) = 1/ζ(2)`, and `W = π/4`),
   this gives `L = (3/π)‖Δ‖²`.

Actual cost: 3013 lines (estimate was 1800–2500). The error term `O(√y log²(1/y))` for box
counts is explicit (`horo_bound`), but no rate is extracted for `G` itself, because the
uniform-continuity step is not quantitative. An `O(x^{3/5})` error for the asymptotic would need
Lipschitz bounds on `G` and is not attempted.

**Route A** (`E(z,s)`, Fourier expansion, Zagier's contour shift, estimated 3800–5700 lines) is
superseded. E1/E3a stay as independent results. **Route C** (mixing) is not needed.

## Literature

* The lattice-point/sandwich proof here is self-contained. Its main term is the classical
  equidistribution of Farey fractions with weights `φ(c)/c`. Its structure (unfold, count, sandwich
  on a fundamental domain) is the standard elementary route to horocycle equidistribution on
  `SL₂(ℤ)\ℍ` for compactly supported test functions.

* J. Karamata, *Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes*,
  Math. Z. 32 (1930). The proof used here is the one in Titchmarsh, *Theory of Functions*, §7.53.
* D. Zagier, *Eisenstein series and the Riemann zeta function* (1981). The horocycle mean of a
  rapidly decaying `f` is `(3/π)∫f dμ + O(y^{1/2})`.
* P. Sarnak, *Asymptotic behavior of periodic orbits of the horocycle flow and Eisenstein series*,
  CPAM 34 (1981).
* R. A. Rankin (1939), A. Selberg (1940); H. Iwaniec, *Topics in Classical Automorphic Forms*, §13
  (unfolding) and §3 (Eisenstein series, Fourier expansion).
