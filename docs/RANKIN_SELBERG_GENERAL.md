# Rankin–Selberg for every level-one cusp form (`RamanujanTau/RankinSelbergGeneral/`)

**Status (2026-11-04).** For every level-one cusp form `f ∈ S_k(SL₂(ℤ))` with q-expansion
coefficients `a(n)`, and weight `k ≥ 1`, Lean now proves

    (1/N) ∑_{n≤N} |a(n)|²/n^{k−1}  →  (3/π)(4π)^k ‖f‖² / Γ(k),     ‖f‖² = ∫_𝓕 |f|² y^k dx dy/y²,

with no hypotheses (`rankinSelberg_asymptotic`, `rankinSelberg_asymptotic_Gamma`). Also proved:
`‖f‖² > 0` when `f ≠ 0`, a two-sided bound `c₁N ≤ ∑ ≤ c₂N` for every `N ≥ n₀`, and `Θ(N)`. The
five one-dimensional weights 16, 18, 20, 22 and 26 are stated for the integer coefficients of
`ΔE₄`, `ΔE₆`, `ΔE₄²`, `ΔE₄E₆` and `ΔE₄²E₆`. At `f = Δ`, the general theorem re-proves the
existing `τ` result with the same constant.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`. Build only this directory:
`nice -n 10 lake build RamanujanTau.RankinSelbergGeneral.Main`.

The proof reuses `EisensteinReal/`, `RankinSelberg/` and `RankinError/`.
`RankinSelbergGeneral.Main` is included in the `RamanujanTau.lean` import graph.

| File | Lines | Content |
|---|---|---|
| `Basic.lean` | 37 | class `HoroFn`: a continuous, nonnegative, bounded, `SL₂(ℤ)`-invariant `G : ℍ → ℝ`; generic `petNormSq = ∫_𝓕 G dμ` |
| `GMain.lean` | 439 | copy of `EisensteinReal/HoroMain`, with `G` abstracted: the `1/K`-grid and the pointwise bounds `up`/`lo` |
| `GFinal.lean` | 379 | copy of `HoroFinal`, abstracted: the sandwich and the Cauchy argument, `∃ Λ, ∫₀¹G(x+iy)dx → Λ` |
| `GIdent.lean` | 547 | copy of `HoroIdent`, abstracted: the grid brackets `∫_𝓕 G dμ`, so `Λ = (3/π)∫_𝓕 G dμ` |
| `Cusp.lean` | 176 | `G_f = \|f\|²y^k` is a `HoroFn`; horocycle limit; Parseval, then Karamata (`ρ = k`), then Abel summation |
| `Positive.lean` | 227 | `‖f‖² > 0` (identity theorem plus an open set of positive measure); two-sided bound; `Θ(N)` |
| `Instances.lean` | 140 | integer-coefficient forms (`BoylanWebb.IntForm`); `ΔE₄ᵃE₆ᵇ`; weights 16, 18, 20, 22, 26 |
| `Main.lean` | 57 | the `Δ` consistency check; `#print axioms` for every headline |
| `scripts/rankinselberggeneral/check.gp` | | numerics (PARI) |

## How it was generalized

The horocycle proof in `EisensteinReal/Horo*` uses only four properties of `G = |Δ|²y¹²`:
continuity, `G ≥ 0`, `G ≤ M`, and `SL₂(ℤ)`-invariance. It uses no decay at the cusp, because
the cusp rectangle `[−½,½)×[L,∞)` is handled by the sup bound `M` and contributes `M/L` to the
gap. It also never uses `G > 0`; only `G ≥ 0` is needed.

Those four properties are packaged as the field-only class `HoroFn` (fields `G`, `continuous_G`,
`G_nonneg`, `exists_G_le`, `G_smul`). The three `G`-dependent files `HoroMain`, `HoroFinal` and
`HoroIdent` were copied with `variable [HoroFn]` and `open HoroFn`, so that the name `G` now
refers to the class field. Apart from that, the copies differ from the originals in only five
places: `G_pos` becomes `G_nonneg`, the `Δ`-specific `exists_G_le` lemma is dropped (it is now a
class field), `petNormSq` is the generic one, one `simp only [bx, box]` becomes
`unfold bx; simp only [EisensteinReal.Horo.box]`, and the linter for unused section variables is
switched off. The `G`-independent files (`HoroArith`, `HoroUnfold`, `HoroCount`, `HoroLimit`,
`HoroSandwich`, `HoroConst`, `Karamata`, `Asymptotic`) are imported unchanged.

For a cusp form `f`, put `G_f z = ‖f z‖²(Im z)^k`. Each class field then comes from Mathlib:

* `G_f = ‖petersson k f f‖`;
* invariance is `SlashInvariantFormClass.norm_petersson_smul`;
* boundedness is `CuspFormClass.petersson_bounded_left`;
* continuity comes from `ModularFormClass.holo`.

## Headline theorems

### Evidence level 1 (Lean, axiom-clean, no hypotheses)

Throughout, `f : CuspForm 𝒮ℒ (k : ℤ)` with `k : ℕ`. Define:

* `coeffSq f n = ‖(qExpansion 1 f).coeff n‖²`;
* `S f N = ∑_{n ∈ [1,N]} coeffSq f n / n^{k−1}`;
* `petNormSqF f = ∫_{0<y, |x|≤½, x²+y²≥1} ‖f‖²y^k dx dy/y²`;
* `rsConst f = (3/π)(4π)^k·petNormSqF f/(k−1)!`.

| Theorem | Statement |
|---|---|
| `Horo.tendsto_Aint_zagier` (generic, `GIdent`) | for any `[HoroFn]`: `∫₀¹ G(x+iy) dx → (3/π)·∫_𝓕 G dμ` as `y → 0⁺` |
| **`horocycle_tendsto`** | `∫₀¹ \|f(x+iy)\|²y^k dx → (3/π)‖f‖²` as `y → 0⁺` (Zagier/Sarnak horocycle equidistribution for `G_f`) |
| `coeff_zero_eq_zero` | `a(0) = 0` |
| `tendsto_sum_coeffSq` | `1 ≤ k → (∑_{n≤N} \|a(n)\|²)/N^k → (3/π)(4π)^k‖f‖²/k!` |
| **`rankinSelberg_asymptotic`** | `1 ≤ k → (1/N)∑_{n≤N} \|a(n)\|²/n^{k−1} → (3/π)(4π)^k‖f‖²/(k−1)!` |
| `rankinSelberg_asymptotic_Gamma` | the same with `Γ(k)` in place of `(k−1)!` |
| `Horo.petNormSq_pos_of` (generic) | if `G(p₀) > 0` at a point with `Im p₀ > 1` and `\|Re p₀\| < ½`, then `∫_𝓕 G dμ > 0` |
| `exists_ne_zero_near` | `f ≠ 0 → ∃ z, \|z − 2i\| < ¼ ∧ f z ≠ 0` (identity theorem on the upper half-plane) |
| **`petNormSqF_pos`** | `f ≠ 0 → 0 < ‖f‖²` |
| `rankinSelberg_asymptotic_pos` | `f ≠ 0 → 1 ≤ k → 0 < c_f ∧ S f N / N → c_f` |
| **`rankinSelberg_two_sided`** | `f ≠ 0 → 1 ≤ k → ∃ n₀ ≥ 1, a(n₀) ≠ 0 ∧ (∀ N < n₀, S f N = 0) ∧ ∃ c₁ c₂ > 0, ∀ N ≥ n₀, c₁N ≤ S f N ≤ c₂N` |
| **`rankinSelberg_isTheta`** | `f ≠ 0 → 1 ≤ k → S f =Θ[atTop] (N ↦ N)` |
| `rankinSelberg_intForm` | if `IntForm k a` (`a ∈ ℤ⟦q⟧` is the q-expansion of a level-one form of weight `k`), `a(0) = 0`, `a ≠ 0`, `k ≥ 1`: `∃ F : CuspForm`, `qExpansion F = a`, `0 < c_F`, and `(1/N)∑ a(n)²/n^{k−1} → c_F` |
| `rankinSelberg_deltaE a b` | the same for `deltaE a b = q∏(1−qⁿ)²⁴·p4ᵃ·p6ᵇ = ΔE₄ᵃE₆ᵇ`, weight `12+4a+6b` |
| **`rankinSelberg_weight16/18/20/22/26`** | instances `ΔE₄`, `ΔE₆`, `ΔE₄²` (`= ΔE₈`), `ΔE₄E₆` (`= ΔE₁₀`), `ΔE₄²E₆` (`= ΔE₁₄`), with exponents `n¹⁵, n¹⁷, n¹⁹, n²¹, n²⁵`, in integer coefficients |
| `rankinSelberg_asymptotic_discriminant` | at `f = Δ`, the general theorem gives `(1/N)∑τ(n)²/n¹¹ → (3/π)(4π)¹²·EisensteinReal.petNormSq/11!` (consistency; `petNormSqF Δ = petNormSq` and `Gf Δ = RankinSelberg.G` hold by `rfl`) |

Notes on the statements:

* **Weight hypothesis.** `1 ≤ k` is used only to set `ρ = k ≥ 1` in Karamata and to write
  `k − 1` in ℕ. Nonzero level-one cusp forms have `k ≥ 12`, but the theorems do not need that.
* **Two-sided bound.** It cannot hold for every `N ≥ 1` in general: if `a(1) = 0` (possible
  once `dim S_k ≥ 2`), then `S(1) = 0`. So it is stated from the first nonzero index `n₀` on,
  and `S = 0` before `n₀`. For `ΔE₄ᵃE₆ᵇ`, `n₀ = 1` (`coeff_one_deltaE`). The constants come from
  the limit, so they are not effective.
* **The instances.** Each is stated as `∃ F : CuspForm 𝒮ℒ k` with `qExpansion 1 F` equal to the
  explicit integer series, because `IntForm` is an existential over modular forms. The constant
  is `rsConst F`; it is positive and explicit in terms of `‖F‖²`.

## Numerical evidence (level 4)

`scripts/rankinselberggeneral/check.gp` (PARI, `nbthreads = 1`, `N = 10⁵`). `‖f‖²` is from
`mfpetersson(mfsymbol(...))`, and `c = (3/π)(4π)^k‖f‖²/(k−1)!`.

| k | f | a(2), a(3), a(4) | ‖f‖² | c | S(x)/x at x = 10, 10², 10³, 10⁴, 10⁵ |
|---|---|---|---|---|---|
| 12 | Δ | −24, 252, −1472 | 1.035362e−6 | 0.3840840545 | 0.4253, 0.3808, 0.3821, 0.3839, 0.38403 |
| 16 | ΔE₄ | 216, −3348, 13888 | 2.169061e−6 | 0.6124934244 | 0.6911, 0.6183, 0.6145, 0.6131, 0.61251 |
| 18 | ΔE₆ | −528, −4284, 147712 | 4.594736e−6 | 0.7532532273 | 0.9970, 0.7611, 0.7635, 0.7548, 0.75366 |
| 20 | ΔE₈ | 456, 50652, −316352 | 8.265542e−6 | 0.6256700317 | 0.7760, 0.6189, 0.6349, 0.6266, 0.62562 |
| 22 | ΔE₁₀ | −288, −128844, −2014208 | 2.009982e−5 | 0.5720534524 | 0.6186, 0.5977, 0.5728, 0.5723, 0.57196 |
| 26 | ΔE₁₄ | −48, −195804, −33552128 | 2.053347e−4 | 0.4800036628 | 0.5943, 0.4824, 0.4800, 0.4818, 0.48003 |

The coefficients agree with `deltaE` (for example, `ΔE₄` has `a(2) = −24 + 240 = 216`). The
`k = 12` row reproduces `docs/RANKIN_SELBERG.md`.

## What remains

* **Power saving (optional item; not attempted).** `RankinError/` proves
  `S(N) = cN + O(N^{1−1/84})` for `τ`. The `G`-independent files of that directory are
  reusable as they stand: Perron, Riesz/RieszK, Landau, the Γ-bounds, Phragmén–Lindelöf,
  `HMeasure`, `Coset`.

  The `Δ`-specific files are `Tau`, `ThetaBound`, `ThetaInt`, `UnfoldTheta`, `RSMellin`,
  `RSUnfoldProof`, `RSFE` and `PowerSaving84`, about 1400 lines. They use exponential decay
  `G ≤ K e^{−c y}` on `y ≥ ½` (`exists_G_exp_le`), which holds for every cusp form via the
  q-expansion, and the Parseval identity, which is already general.

  The same `HoroFn`-style abstraction would need one more class field (exponential cusp decay)
  plus a general weight `k` in the Γ-factors `Γ(s+k−1)`. Estimate: 1000–1600 lines, about one
  focused session. I see no mathematical obstruction.
* **The real-analytic `E(z,s)` route** is not needed and was not touched.

## Literature

* R. A. Rankin (1939), A. Selberg (1940). The mean square `∑_{n≤x}|a(n)|²/n^{k−1} ~ c_f x` with
  `c_f = (3/π)(4π)^k‖f‖²/Γ(k)` holds for every level-one cusp form; see Iwaniec, *Topics in
  Classical Automorphic Forms*, §13, and Iwaniec–Kowalski §14 (normalizations vary by the
  volume `π/3` of `𝓕`).
* D. Zagier, *Eisenstein series and the Riemann zeta function* (1981), and P. Sarnak, CPAM 34
  (1981): horocycle equidistribution. The elementary lattice-point proof formalized here (see
  `docs/EISENSTEIN_REAL.md`) works for every bounded continuous invariant test function.
* J. Karamata (1930); Titchmarsh, *Theory of Functions*, §7.53.
