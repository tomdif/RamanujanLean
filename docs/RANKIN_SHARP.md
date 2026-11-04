# A sharper Rankin–Selberg error exponent for `τ` (`RamanujanTau/RankinSharp/`)

**Status (2026-11-04).** The error exponent of `RankinError.rankinSelberg_power_saving_84`
(`1 − 1/84`) has been improved to **any exponent above 4/5**:

    S(N) = ∑_{n≤N} τ(n)²/n¹¹ = c·N + O(N^{1−δ})   for every 0 < δ < 1/5,
    c = (3/π)(4π)¹²‖Δ‖²/11!.

Evidence level 1 (Lean, axiom-clean, no hypotheses). Every headline prints
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no new axiom and no
`native_decide`.

| Theorem | File | Statement |
|---|---|---|
| **`rankinSelberg_power_saving_sharp`** | `Sharp` | `0 < δ → δ < 1/5 → ∃ C, ∀ N ≥ 1, \|∑_{n=1}^N τ(n)²/n¹¹ − 3/π·(4π)¹²·petNormSq/11!·N\| ≤ C·N^{1−δ}` |
| `rankinSelberg_power_saving_81_100` | `Sharp` | the same with `N^{81/100}` (the case `δ = 19/100`) |
| `power_saving_fifth_of_RSData` | `Sharp` | the same for any `a ≥ 0`, `a 0 = 0` with `RSData a κ` and `abscissaOfAbsConv a ≤ 1`; main term `κ·rsConst·N` |
| `rankinSelberg_power_saving_lt_eighth` | `Sharp8` | milestone 1: every `δ < 1/8`, Perron applied to `D(s)` directly (no Möbius step) |
| `abscissa_aTau_le_one` | `Sharp8` | `∑ τ(n)² n^{−s−11}` converges absolutely on `Re s > 1`. Proof: partial sums are `O(N)` by `rankinSelberg_power_saving_84`, then Mathlib's `LSeriesSummable_of_sum_norm_bigO_and_nonneg` |
| **`fA_bound`** | `Convex` | Step A: `f_A(s) = E(s)Γ(s+1)/(Γ(4−s)(s+3))` is bounded on `−1/2 ≤ Re s ≤ 3/2` |
| `ratioA_le` | `Convex` | on `Re s = −1/2`: `‖(s−1)γ(1−s)γ(s)⁻¹Γ(s+1)Γ(4−s)⁻¹/(s+3)‖ ≤ 25¹⁵`, computed exactly with `u = s+1` and `ū = 1−u` |
| `Efun_line` | `Convex` | Step B: on `Re s = σ_L` with `n = 3−2σ_L ∈ ℕ`, `σ_L ≥ 0`: `‖E(s)‖ ≤ C‖s+3‖^{n+1}` |
| **`Efun_bound`** | `Convex` | Step C: `‖E(s)‖ ≤ B‖s+3‖^{n+1}` on `σ_L ≤ Re s ≤ 5/2` |
| `Efun_eq_LSeries'`, `Lam_eq` | `Efun` | `E(s) = (s−1)ζ(2s)D(s)` and `Λ(s) = γ(s)ζ(2s)D(s)` on `Re s > 1`, by the identity theorem from `Re s > 2` |
| `Efun_growth` | `Efun` | `‖E(s)‖ ≤ K e^{L\|t\|}` on `−3/2 ≤ Re s ≤ 5/2`, `\|t\| ≥ 1` |
| `pl_strip` | `PL` | Phragmén–Lindelöf for a strip of width `< 2π`, given growth `K e^{L\|t\|}` (wraps Mathlib's `PhragmenLindelof.vertical_strip`) |
| **`mu2_mul_chi`** | `Squares` | `μ₂ * χ = 1` as arithmetic functions over `ℝ`, where `χ` is the indicator of the nonzero squares and `μ₂(m²) = μ(m)`. Proof: uniqueness of L-series (`LSeries.eq_of_LSeries_eventually_eq`) |
| `LSeries_sqPull`, `LSeries_chi` | `Squares` | `L(sqPull h, s) = L(h, 2s)`; `L(χ, s) = ζ(2s)` |
| **`sum_a_eq_mobius`** | `Squares` | `∑_{n≤N} aₙ = ∑_{m≤N} μ(m)·∑_{n≤⌊N/m²⌋} (χ*a)(n)` |
| **`mobius_transfer`** | `Mobius` | if `A(N) = ∑_{m≤N} μ(m)B(⌊N/m²⌋)`, `B(0) = 0` and `B(M) = c₀M + O(M^{1−δ})` with `0 ≤ δ < 1/2`, then `A(N) = (6/π²)c₀N + O(N^{1−δ})` |
| `tsum_moebius_div_sq` | `Mobius` | `∑ μ(m)/m² = 6/π²` |

Build only these files with `nice -n 10 lake build RamanujanTau.RankinSharp.Sharp`. That builds
7 files, about 1420 lines, and needs `RankinError` already built. Nothing outside
`RankinSharp/`, `scripts/rankinsharp/` and this write-up was created or modified. Files
in `RankinError/` are imported but unchanged.

## Why `1/84` was far from optimal, and what replaced it

In `RankinError`, `δ = (1−σ₁)/(K+2)`. Here `K` is the polynomial growth exponent of
`F = D − c₀/(s−1)` on `[σ₁, c]`: the Riesz order is `k = K+1`, and one `k`-th difference
divides the saving by `k+1`. `K = 19` came from the fixed normalisation `(s+3)^{19}` in the
Phragmén–Lindelöf function on the wide strip `[−3/2, 5/2]`.

**The convexity bound without Stirling.** Mathlib has no complex Stirling formula. We use the
fact that `Γ`-ratios are exactly computable on lines where the real parts differ by an integer
(`|Γ(ū)| = |Γ(u)|`, plus `Γ(w+n) = ∏(w+j)·Γ(w)`). Put `E(s) = (s−1)ζ(2s)D(s)`, which is entire.

* **Step A.** Phragmén–Lindelöf on `[−1/2, 3/2]` for `f_A = E(s)·Γ(s+1)/(Γ(4−s)(s+3))`.
  The factor `Γ(s+1)/Γ(4−s)` has modulus about `|t|^{2σ−3}`: a *variable* exponent, linear in
  `σ`.
  * At `Re s = 3/2` we have `4−s = conj(s+1)`, so this factor has modulus exactly `1`, and `D`
    converges absolutely (`abscissa ≤ 1`).
  * At `Re s = −1/2` the functional equation produces `γ(1−s)/γ(s)`. Together with the
    normaliser this is a degree-15/degree-15 rational function of `u = s+1`, so it is bounded.
* **Step B.** On the half-integer lines `σ_L = 0` and `σ_L = 1/2`, `Γ(4−s)/Γ(s+1)` is an exact
  polynomial of degree `n = 3 − 2σ_L`. This gives `|E| ≪ |s+3|^{4−2σ_L}`, which is the
  convexity exponent of the strip `[−1/2, 3/2]`.
* **Step C.** Constant-exponent Phragmén–Lindelöf on `[σ_L, 3/2]` extends that bound to the
  whole strip.

**Two ways to use it.**

| Route | Contour `σ₁` | growth `K` | Riesz order `k` | `δ = (1−σ₁)/(k+1)` |
|---|---|---|---|---|
| `RankinError` (crude `(s+3)^{19}`) | `3/4` | 19 | 20 | `1/84` |
| Milestone 1: `D(s)` directly; `1/ζ(2s)` forces `σ₁ > 1/2`; line `σ_L = 1/2` | `σ₁ ↓ 1/2` | 2 | 3 | `(1−σ₁)/4 → 1/8` |
| **Milestone 2**: `ζ(2s)D(s) = ∑ bₙ n^{−s}` (`b = χ*a ≥ 0`), line `σ_L = 0`, then Möbius | `σ₁ ↓ 0` | 3 | 4 | `(1−σ₁)/5 → 1/5` |

In milestone 2 the twisted series has no `1/ζ(2s)`, so the contour can approach `Re s = 0`. The
twist is undone by `∑ aₙ = ∑ μ(m) B(N/m²)`. This keeps any `δ < 1/2`, because
`∑ m^{−2(1−δ)} < ∞` and `|⌊x⌋ − x| ≤ x^{1−δ}`. The residue becomes `c₀·6/π² = κ·rsConst`.

## Numerical check (evidence level 4)

The script `scripts/rankinsharp/sharp_check.gp` (PARI, `nbthreads = 1`, `N = 10⁶`, about
10 s) computes `|S − cx|` for `aₙ = τ(n)²/n¹¹` and `|B − c₀x|` for the twisted `b = χ*a`
(`c₀ = c·ζ(2)`).

| decade | max\|S−cx\| | max\|B−c₀x\| | local slope S | local slope B |
|---|---|---|---|---|
| [10², 10³) | 4.97 | 9.01 | 0.45 | 0.66 |
| [10³, 10⁴) | 16.1 | 17.1 | 0.51 | 0.28 |
| [10⁴, 10⁵) | 41.2 | 51.1 | 0.41 | 0.48 |
| [10⁵, 10⁶] | 96.1 | 127.0 | 0.37 | 0.40 |

Both errors grow like about `x^{0.4}`, well inside the proved `x^{4/5+ε}`, Rankin's `x^{3/5}`
and the conjectured `x^{3/8+ε}`. The twisted series behaves like the original, so the
Möbius step loses nothing visible.

## Gaps and next steps

1. **`δ → 1/4` (two pieces, paper level 3).**
   * Convexity with edges `1+ε` and `−ε` gives `|ζ(2s)D(s)| ≪ |t|^{2+2ε}` on `Re s = 0`.
     This needs a bound `|Γ(x+it)/Γ(y+it)| ≪ (1+|t|)^{x−y}` for non-integer `x−y`, that is,
     Stirling or a substitute. Mathlib has neither.
   * `rieszAsymp_of_continuation` must accept a real growth exponent. It now takes `K : ℕ`
     with `k = K+1`, but only `k > K` is needed for integrability.

   With both, `K = 2+2ε`, `k = 3` and `δ = (1−σ₁)/4 → 1/4`. Moving the contour to
   `σ₁ ≤ 0` instead does not help: the pole of `P_k` at `s = 0` contributes a term of size
   `x^k`, which caps the saving at `θ ≤ 1`.
2. **Rankin's `δ = 2/5`.** Smoothed Perron with a `k`-th difference loses a factor `k+1`.
   The classical `(A−1)/(A+1) = 3/5` (Landau's theorem for degree `A = 4`) does not stop at a
   convexity bound on the shifted contour. It moves the Riesz integral far left and
   evaluates it with the functional equation: the dual sum of Bessel-type kernels, which
   needs Stirling asymptotics of `γ(1−s)/γ(s)` with phase. Only then does it difference,
   with `h` optimised against the dual-sum error. Estimate: 1500+ lines of new Lean,
   dominated by the complex Stirling/oscillatory-integral part.
3. Cosmetic: some `<;>` linter warnings in `Convex.lean`.

## Literature

* R. A. Rankin, Proc. Cambridge Phil. Soc. 35 (1939) 351–372: `O(x^{3/5})`.
* A. Selberg, Arch. Math. Naturvid. 43 (1940).
* E. Landau, *Über die Anzahl der Gitterpunkte in gewissen Bereichen*, Gött. Nachr. 1912 (and
  Chandrasekharan–Narasimhan, Ann. of Math. 76 (1962)): `(A−1)/(A+1)` for degree `A`.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1 (convexity bound via
  Phragmén–Lindelöf).
* See also `docs/RANKIN_ERROR.md` for the base machinery (unfolding, functional equation,
  Perron/Riesz, `riesz_kdiff`).
