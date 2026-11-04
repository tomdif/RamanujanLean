# Sign changes of Ramanujan's τ (`RamanujanTau/TauSigns/`)

**Status (2026-11-04).** *Update: the quantitative exponents are now `x^{4/5+ε}` and
`X^{1/5−ε}`. See the next section.* Three results are **proved unconditionally**: τ changes sign
infinitely often, it changes sign in every interval `(x, x + A·x^{83/84}]` for large `x`, and it
has `≫ X^{1/84}` sign changes in `[1, X]`. There are no hypotheses, no sorry, no new axiom and
no `native_decide`. Every headline prints `[propext, Classical.choice, Quot.sound]`.

Build only these files (about 970 lines):
`nice -n 10 lake env lean RamanujanTau/TauSigns/Main.lean`. That needs the oleans of
`Qualitative`, `HeckeSum`, `Window` and `Count`, which were produced with `lake env lean -o`.
`lake build RamanujanTau.TauSigns.Main` should also work, but it was not run because it might rebuild stale upstream modules. Nothing outside `TauSigns/`,
`scripts/tausigns/` and this write-up was modified. The root file does not import the directory.

## Update (2026-11-04): sharp Rankin–Selberg exponent, windows `x^{4/5+ε}`, `≫ X^{1/5−ε}`

Three new files: `WindowGeneral.lean` (218 lines), `CountGeneral.lean` (165 lines) and
`Sharp.lean` (56 lines). They are built with `lake build RamanujanTau.TauSigns.Sharp`, which
completed without rebuilding upstream modules. The original five files are unchanged. All headlines
print `[propext, Classical.choice, Quot.sound]` (evidence level 1).

| Theorem | File | Statement |
|---|---|---|
| **`tau_sign_change_short_interval_of_power_saving`** | `WindowGeneral` | if `∃ C, ∀ N ≥ 1, \|S(N) − cN\| ≤ C N^{1−δ}`, then for every `θ` with `3/4 < θ ≤ 1` and `1 − δ ≤ θ`: `∃ A > 0, X₀, ∀ x h, X₀ ≤ x → A x^θ ≤ h → h ≤ x →` both signs in `(x, x+h]` |
| `card_signChanges_ge_of_window` | `CountGeneral` | windows of exponent `θ ∈ [0,1)` ⇒ `∃ c > 0, X₀, ∀ X ≥ X₀, c X^{1−θ} ≤ #signChanges X` |
| `card_signChanges_ge_of_power_saving` | `CountGeneral` | the same RS hypothesis and `3/4 < θ < 1`, `1 − δ ≤ θ` ⇒ `≫ X^{1−θ}` sign changes |
| **`tau_sign_change_short_interval_sharp`** | `Sharp` | for every `4/5 < θ ≤ 1`: both signs in every `(x, x+h]` with `A x^θ ≤ h ≤ x`, `x ≥ X₀` |
| **`card_signChanges_ge_sharp`** | `Sharp` | for every `0 < η < 1/5`: `∃ c > 0, X₀, ∀ X ≥ X₀, c X^η ≤ #signChanges X` |

Here `S(N) = ∑_{n≤N} τ(n)²/n¹¹` and `c = (3/π)(4π)¹²‖Δ‖²/11!`. The hypothesis is stated
verbatim in the form of `RankinSharp.rankinSelberg_power_saving_sharp` and
`RankinError.rankinSelberg_power_saving_84`. A future improvement of `δ` therefore feeds through
with a one-line proof. `Sharp.lean` takes `δ = ((1−θ) + 1/5)/2` for the window and `δ = η`,
`θ = 1 − η` for the count. Concrete instances in `Sharp.lean` are windows `x^{81/100}` and
`≫ X^{19/100}` sign changes. The old exponents were `x^{83/84}` and `X^{1/84}`.

**Optimal exponent for this method.** On a one-signed window, Hecke and Weil give
`∑_W τ²/n¹¹ ≪ x^{−11}·x^{23/4+ε}·x^{6+ε} = x^{3/4+2ε}`, and Rankin–Selberg gives `≥ c h − O(x^{1−δ})`.
So the method yields `θ = max(1 − δ, 3/4) + ε` and a count of `X^{1−θ}`. In the proof,
`ε = (θ − 3/4)/4`, which leaves a gap of `(θ − 3/4)/2 > 0`.

* With `δ < 1/5`, the RS term dominates, since `1 − δ > 4/5 > 3/4`. That gives windows
  `x^{4/5+ε}` and `≫ X^{1/5−ε}` sign changes. These are the best values available from the
  current RS exponent.
* Every `δ ≥ 1/4` gives the Hecke × Weil limit: windows `x^{3/4+ε}` and `≫ X^{1/4−ε}`.
  Rankin's classical `δ = 2/5` lands here. The RS exponent stops mattering at `δ = 1/4`.
* Going below `3/4` would need something other than "max|τ| × ∑|τ|". Deligne's bound
  `|τ(n)| ≪ n^{11/2+ε}` would give `x^{1/2+2ε}` on that side, so `θ = max(1−δ, 1/2)`.

## Headline theorems (evidence level 1: Lean, axiom-clean)

| Theorem | File | Statement |
|---|---|---|
| **`tau_sign_changes`** | `Qualitative` | `∀ N, ∃ m n, N ≤ m ∧ N ≤ n ∧ 0 < τ m ∧ τ n < 0` |
| `not_eventually_signed` | `Qualitative` | for `s = ±1`: `¬ ∀ n ≥ N, 0 ≤ s·τ(n)` |
| `exists_Δ_iy_bdd` | `Qualitative` | `∃ y₀ > 0, ∃ B, ∀ y ∈ (0, y₀], ‖Δ(iy)‖ ≤ B` |
| `hasSum_tau_iy` | `Qualitative` | `Δ(iy) = ∑ τ(n) e^{−2πny}` (real part) |
| `norm_Δ_S` | `Qualitative` | `‖Δ(z)‖ = ‖Δ(−1/z)‖ / ‖z‖¹²` |
| **`hecke_partial_sum`** | `HeckeSum` | `0 < ε ≤ 1 → ∃ C, ∀ M ≥ 1, \|∑_{n≤M} τ(n)\| ≤ C·M^{6+ε}` |
| `kernel_bound` | `HeckeSum` | on `(0,1)` with `y = 1/M`: `\|∑_{n≤M} wⁿ\| ≤ 2e^{6π}M^ε(x^{ε−1}+(1−x)^{ε−1})`, `w = 1/q` |
| **`tau_sign_change_short_interval`** | `Window` | `∃ A > 0, X₀, ∀ x h, X₀ ≤ x → A·x^{83/84} ≤ h → h ≤ x → (∃ m ∈ (x,x+h], τ m > 0) ∧ (∃ n ∈ (x,x+h], τ n < 0)` |
| `exists_signChange_between` | `Count` | `a < b`, `τ(a)τ(b) < 0` ⇒ there is a sign change `(n,m)` with `a ≤ n < m ≤ b` |
| **`card_signChanges_ge`** | `Count` | `∃ c > 0, ∃ X₀, ∀ X ≥ X₀, c·X^{1/84} ≤ #signChanges X` |

`IsSignChange n m` means `n < m`, `τ(n)τ(m) < 0`, and `τ(k) = 0` for `n < k < m`.
`signChanges X` is the set of `n ≤ X` such that some `m ≤ X` makes `IsSignChange n m` hold.
`τ` is the repo's `RamanujanTau.tau`.

## Proofs

### 1. Infinitely many sign changes (`Qualitative.lean`, 248 lines)

This uses only the modular transformation of Δ, with no L-function and no Landau theorem.

* On the imaginary axis, `Δ(iy) = ∑ τ(n) e^{−2πny}`, from Mathlib's `hasSum_qExpansion` and the
  repo's bridge `TauBound.qExpansion_discriminant_coeff_tau`.
* Mathlib's `discriminant_S_invariant` gives `Δ(iy) = y^{−12}Δ(i/y)`.
* Cusp decay (`CuspFormClass.exp_decay_atImInfty`) gives `|Δ(i/y)| ≤ Ce^{−2π/y}`.
* Since `e^{2π/y} ≥ (2π/y)¹²/12!`, `Δ(iy)` is bounded as `y → 0⁺`. Numerically it even tends
  to 0 very fast.
* Now suppose `s·τ(n) ≥ 0` for every `n ≥ N`. Take `y = 1/(2πK)`. Then
  `e^{−1}∑_{N≤n≤K}|τ(n)| ≤ B + ∑_{n<N}|τ(n)|` for every large `K`.
* But `τ(m²) ≠ 0` for all `m ≥ 1` (`TauDensity.tau_sq_ne_zero`), and τ takes integer values.
  So the left side is at least `e^{−1}(√K − N)`, which is unbounded. Contradiction.

The brief proposed a cheaper route than Hecke plus Landau: the modular-transformation route.
That is the route implemented here. Neither the entire continuation of `L(Δ,s)` nor Landau's
theorem is needed.

### 2. Hecke's partial-sum bound (`HeckeSum.lean`, 268 lines)

This is Hecke's argument with the logarithm replaced by `M^ε`.

* Mathlib's coefficient integral (`ModularFormClass.qExpansion_coeff_eq_intervalIntegral`) gives
  `∑_{n≤M} τ(n) = ∫₀¹ K(x)Δ(x+i/M) dx`, with `K = ∑_{n≤M} wⁿ`, `w = e^{2πy}e^{−2πix}` and `y = 1/M`.
* `|Δ| ≤ CM⁶` by `CuspFormClass.exists_bound`.
* The kernel satisfies `|K| ≤ 2Me^{2π}` and `|K|·|w−1| = |w^{M+1}−1| ≤ 2e^{4π}`.
* `|w−1| ≥ 2 sin πx`. This holds because `|e^{a+ib}−1|² ≥ 4sin²(b/2)` for `a ≥ 0`.
* Interpolation (`a ≤ A`, `at ≤ B` ⇒ `a ≤ A^εB^{1−ε}t^{ε−1}`) and Jordan's inequality give
  `|K| ≤ cM^ε(x^{ε−1}+(1−x)^{ε−1})`. That bound is integrable, by `intervalIntegrable_rpow'`.

### 3. Short intervals (`Window.lean`, 222 lines)

Suppose `±τ ≥ 0` on `W = (x, x+h]` with `h ≤ x`, and take `ε = 1/20`. Then:

* `∑_W |τ| = |∑_W τ| ≤ 129·C_H·x^{6+ε}` (`hecke_partial_sum`);
* `∑_W τ² ≤ max_W|τ| · ∑_W|τ| ≤ K·x^{23/4+ε}·x^{6+ε}`
  (Weil, `StepanovAS.tau_isBigO_23_4_unconditional`);
* `∑_W τ²/n¹¹ ≥ ch − 3C_R·x^{83/84}` (`RankinError.rankinSelberg_power_saving_84`);
* `∑_W τ²/n¹¹ ≤ x^{−11}∑_W τ²`.

Together these give `ch − 3C_R x^{83/84} ≤ K x^{17/20}`. With `h ≥ A x^{83/84}`, where
`A = (3C_R+1)/c`, this says `x^{29/210} ≤ K`, which is false for large `x`.

### 4. Counting (`Count.lean`, 217 lines)

* Split `(X/2, X]` into `J = ⌊(X/2)/H⌋` disjoint windows of length `H = ⌈A X^{83/84}⌉`.
* Each window contains both signs, so by strong induction on `b − a` it contains a sign change
  (`exists_signChange_between`).
* Hence `#signChanges X ≥ J ≥ X^{1/84}/(16A)` once `X ≥ max(8, 4X₀, (16A)^{84})`.

## Where the exponents come from

The only bottleneck is the Rankin–Selberg error term. The window has to beat both of these:

* the RS error, `h ≫ x^{83/84}`, which is the repo's power saving `1/84`;
* the Hecke/Weil loss, `h ≫ x^{3/4+2ε}`.

So the result scales with the RS exponent. Rankin's classical `O(x^{3/5})` would give windows
`x^{3/4+ε}` and `≫ X^{1/4−ε}` sign changes. Improving that further would need more than Hecke
plus Weil, for example Deligne's bound together with a sharper mean value. Sharpening the RS
exponent in `RankinError` (see "What remains" in `RANKIN_ERROR.md`) feeds through unchanged:
`Window.lean` uses only the statement `|S(N) − cN| ≤ C N^{1−δ}`.

## Numerical evidence (level 4)

`scripts/tausigns/sign_changes.gp` (PARI, `nbthreads = 1`, τ(n) for n ≤ 2·10⁵, about 1 s):

| x | sign changes in [1,x] | /x | max gap between consecutive sign changes | x^{83/84} |
|---|---|---|---|---|
| 10³ | 517 | 0.517 | 9 | 921 |
| 10⁴ | 4959 | 0.496 | 12 | 8962 |
| 10⁵ | 49893 | 0.499 | 15 | 87192 |
| 2·10⁵ | 99848 | 0.499 | 18 | 172951 |

* Sign changes have density about 1/2, and τ(n) > 0 for exactly 50.00% of the n ≤ 2·10⁵.
  The proved `X^{1/84}` and windows of length `x^{83/84}` are therefore very weak but correct.
  The truth (Matomäki–Radziwiłł) is `≍ X` sign changes.
* `|∑_{n≤M} τ(n)|/M⁶` stays between 0.005 and 0.013 for `M = 10³ … 2·10⁵`, consistent with
  Hecke's bound.
* `Δ(iy)` at `y = 1, 0.5, 0.2, 0.1, 0.05` equals `1.79e−3, 1.43e−2, 5.54e−6, 5.16e−16, 1.09e−39`,
  and agrees with `y^{−12}Δ(i/y)` to all printed digits (250-digit precision). So the bound used in
  §1 holds with a huge margin.

## Gaps and next steps

* None for the three stated theorems.
* A positive-proportion result (`≫ X` sign changes, Matomäki–Radziwiłł 2015) or sign changes in
  intervals of length `x^{1/2}`-type is far beyond this method. It needs Deligne plus
  multiplicative-function machinery.
* The entire continuation of `L(Δ,s)` (Hecke) was not needed. If wanted, it is a direct
  `StrongFEPair` instance for `f(t) = Δ(it)`, using `norm_Δ_S` and `exists_Δ_iy_bdd`-type decay.
  The same pattern as `RankinError/RSFE.lean` should work, at roughly 150 lines. It has not been
  done.

## Literature

* E. Hecke, *Theorie der Eisensteinschen Reihen höherer Stufe…* (1927) and *Über Modulfunktionen
  und die Dirichletschen Reihen mit Eulerscher Produktentwicklung* (1937): `∑_{n≤x} a(n) ≪ x^{k/2}log x`
  and the entire continuation of `L(f,s)`.
* E. Landau's theorem on Dirichlet series with nonnegative coefficients. This is the classical
  route to infinitely many sign changes; it is bypassed here.
* M. Knopp, W. Kohnen, W. Pribitkin, *On the signs of Fourier coefficients of cusp forms*,
  Ramanujan J. 7 (2003): infinitely many sign changes for general cusp forms.
* M. Ram Murty, *Oscillations of Fourier coefficients of modular forms*, Math. Ann. 262 (1983):
  quantitative oscillation. Exact exponents not re-checked here.
* K. Matomäki, M. Radziwiłł, *Sign changes of Hecke eigenvalues*, GAFA 25 (2015): `≫ X` sign
  changes.
* R. A. Rankin (1939) and A. Selberg (1940): the mean square of τ. A. Weil (1948): Kloosterman sums.
