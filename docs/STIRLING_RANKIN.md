# Gamma ratios in vertical strips, and the Rankin–Selberg error `δ < 1/3` (`RamanujanTau/Stirling/`)

> **Current status (2026-11-12).** The stronger error `O(N^{3/5})` is proved for τ and every level-one cusp form by `RankinExact.rankinSelberg_exact` and `rankinSelberg_exact_general`, without Deligne. See [RANKIN_EXACT](RANKIN_EXACT.md).
> The earlier checkpoints and gap lists below describe the development at that stage.

**Status (2026-11-04).** Two results, both at evidence level 1 (Lean, axiom-clean, no
hypotheses). Every headline prints `[propext, Classical.choice, Quot.sound]`. There is no
`sorry`, no new axiom and no `native_decide`.

1. **A Stirling substitute for complex `Γ`** (this fills a gap in Mathlib). For `Re z ≥ 1` and
   **every real** `θ ≥ 0`, with no integrality condition:

       ‖Γ(z)‖ ‖z‖^θ ≤ e¹⁰ ‖Γ(z+θ)‖,     ‖Γ(z+θ)‖ ≤ (n+1)! e¹⁰ ‖z‖^θ ‖Γ(z)‖  (θ ≤ n+1).

   Two-sided Stirling bounds follow: `|Γ(σ+it)| ≍ ‖3/2+it‖^{σ−1/2} e^{−π|t|/2}` with explicit
   constants.
2. **The Rankin–Selberg error, every `δ < 1/3`**, for `τ` and for every level-one cusp form:

       ∑_{n≤N} |a_f(n)|²/n^{k−1} = c_f N + O(N^{1−δ}),   c_f = (3/π)(4π)^k ‖f‖²/(k−1)!.

   This improves `RankinSharp` / `RankinSharpGeneral` (`δ < 1/5`). The brief asked for
   `δ < 1/4`, and this goes further. The classical exponent is `δ = 2/5` (Rankin 1939); see
   the gaps below.

Build only this directory: `nice -n 10 lake build RamanujanTau.Stirling.Main`. That is 6 new
files, about 1600 lines. It needs `RankinSharpGeneral/` built. Nothing outside
`RamanujanTau/Stirling/`, `scripts/stirling/` and this write-up was created or modified.
`RankinSharp*`, `RankinError*` and `RankinSelberg*` are imported, not edited. The root file does
not import this directory.

## Headline theorems (evidence level 1)

| Theorem | File | Statement |
|---|---|---|
| **`norm_Gamma_mul_rpow_le`** | `GammaRatio` | `1 ≤ Re z → 0 ≤ θ ≤ 1 → ‖Γ z‖·‖z‖^θ ≤ e¹⁰·‖Γ(z+θ)‖` (the core) |
| **`norm_Gamma_mul_rpow_le_add`** | `GammaRatio` | the same for every real `θ ≥ 0` |
| **`norm_Gamma_add_le`** | `GammaRatio` | `1 ≤ Re z → 0 ≤ θ ≤ n+1 → ‖Γ(z+θ)‖ ≤ (n+1)!·e¹⁰·‖z‖^θ·‖Γ z‖` |
| `norm_Gamma_add_le_one` | `GammaRatio` | the case `θ ≤ 1`, constant `e¹⁰` |
| `norm_Gamma_ratio_le_of_le` / `_of_ge` | `GammaRatio` | `t`-form: `‖Γ(α+it)‖ ≤ C‖β+it‖^{α−β}‖Γ(β+it)‖` for `1 ≤ β ≤ α`; `‖Γ(α+it)‖ ≤ e¹⁰‖α+it‖^{α−β}‖Γ(β+it)‖` for `1 ≤ α ≤ β` |
| `norm_add_ofReal_le` | `GammaRatio` | almost log-concavity: `Re w ≥ 1`, `θ ∈ [0,1]` ⇒ `‖w+θ‖ ≤ e^{θ(5/(x−½)−5/(x+½))}‖w+1‖^θ‖w‖^{1−θ}` |
| **`norm_Gamma_half_sq`** | `Absolute` | `‖Γ(½+it)‖² = π / cosh(πt)` |
| **`norm_Gamma_le_stirling`** | `Absolute` | `3/2 ≤ σ ≤ n+5/2`: `‖Γ(σ+it)‖ ≤ (n+1)! e¹⁰ √(2π) ‖3/2+it‖^{σ−1/2} e^{−π\|t\|/2}` |
| **`stirling_le_norm_Gamma`** | `Absolute` | `σ ≥ 3/2`: `(√π/3) e⁻¹⁰ ‖3/2+it‖^{σ−1/2} e^{−π\|t\|/2} ≤ ‖Γ(σ+it)‖` |
| `integral_line_eq_rpow` | `RieszReal` | contour shift under a bound `C(1+\|t\|)^{−p}`, `p > 1` (real) |
| **`rieszAsymp_of_continuation_rpow`** | `RieszReal` | `rieszAsymp_of_continuation` with a **real** growth exponent: `‖F‖ ≤ B(1+\|t\|)^r`, `r < k` ⇒ `RieszAsymp a c₀ k (1−σ₁)` |
| **`ratioEps_le`** | `ConvexEps` | on `Re s = −ε` (`0 < ε ≤ ½`, `m ≥ 1`): `‖(s−1)γₘ(1−s)γₘ(s)⁻¹Γ(s+1)Γ(3+2ε−s)⁻¹/(s+3)‖ ≤ RL m = e²⁰·6(m+1)^m 3^m` |
| `fEps_bound` | `ConvexEps` | Phragmén–Lindelöf: `f_ε = E·Γ(s+1)/(Γ(3+2ε−s)(s+3))` is bounded on `−ε ≤ Re s ≤ 1+ε` |
| **`Efun_bound_eps`** | `ConvexEps` | convexity: `‖E(s)‖ ≤ B‖s+3‖^{3+2ε−2σ₁}` on `σ₁ ≤ Re s ≤ 5/2` (`0 ≤ σ₁ ≤ 1`) |
| `Fb_bound_eps` | `Third` | `‖ζ(2s)D(s) − c₀/(s−1)‖ ≤ B(1+\|t\|)^{2+2ε−2σ₁}` on the same strip |
| **`power_saving_third_of_RSDataM`** | `Third` | from `RSDataM m a κ` (`m ≥ 1`), `a ≥ 0`, `a 0 = 0`, abscissa `≤ 1`: `0 < δ < 1/3 ⇒ \|∑_{n≤N} aₙ − κ·rsConstM m·N\| ≤ C N^{1−δ}` |
| `power_saving_third_RSFn` | `Third` | the same for every abstract `RSFn` (`m ≥ 2`) |
| **`rankinSelberg_power_saving_third_general`** | `Third` | `∀ f : CuspForm 𝒮ℒ k, 0 < δ < 1/3 → ∃ C, ∀ N ≥ 1, \|∑_{n∈[1,N]} coeffSq f n/n^{k−1} − rsConst f·N\| ≤ C N^{1−δ}` |
| `rankinSelberg_power_saving_67_100_general` | `Third` | the case `δ = 33/100`: error `C·N^{67/100}`, every cusp form |
| **`rankinSelberg_power_saving_third`** | `Third` | for `τ`: `\|∑ τ(n)²/n¹¹ − 3/π·(4π)¹²·petNormSq/11!·N\| ≤ C N^{1−δ}` for all `0 < δ < 1/3` (the statement of `RankinSharp.rankinSelberg_power_saving_sharp`, with `1/5` replaced by `1/3`) |
| `rankinSelberg_power_saving_67_100` | `Third` | for `τ`: error `C·N^{67/100}` |

## Goal A: the Gamma ratio without Stirling

**Mathlib inventory.** Mathlib has `Complex.Gamma`, `Gamma_conj`, the reflection
`Gamma_mul_Gamma_one_sub`, duplication, the Beta integral, Bohr–Mollerup (real log-convexity),
`Real` Stirling (`Stirling.stirlingSeq`), the digamma function (definition and special values
only), and the Gauss limit `Complex.GammaSeq_tendsto_Gamma`. It has no bound on complex `Γ` in
vertical strips, and no complex `logGamma`.

**Route: the Gauss product.** Neither the Beta integral nor three-lines is needed. We have
`Γ(z)/Γ(z+θ) = lim n^{−θ} ∏_{j≤n}(z+θ+j)/(z+j)`. The function `x ↦ log|x+iy|` is concave only
for `|x| > |y|`, so the naive Hölder step fails. Its concavity defect is small, though. With
`A = |w|²`, `B = |w+1|²`, `u = (2x+1)/A`, the inequalities `log(1+θu) ≤ θu` and
`log(B/A) ≥ (2x+1)/B` give

    log|w+θ| − θ log|w+1| − (1−θ) log|w|  ≤  θ (2x+1)²/(2AB)  ≤  θ · 5/(x² − ¼),

and `5/(x²−¼) = 5/(x−½) − 5/(x+½)` telescopes (`prod_norm_add_le`). The geometric means
telescope to `(|z+n+1|/|z|)^θ`, and `(|z+n+1|/n)^θ ≤ 1 + |z+1|/n → 1`. That gives the
core inequality with constant `e^{θ·10} ≤ e¹⁰`. The opposite direction comes from `θ ↦ 1−θ`
and `Γ(z+1) = zΓ(z)`. Larger `θ` follow by induction with `Γ(w+1) = wΓ(w)`. The whole file is
360 lines.

The constant `e¹⁰` is far from sharp: numerically, the supremum of `|Γ(z)||z|^θ/|Γ(z+θ)|` over
`Re z ≥ 1` is `2/√π ≈ 1.128`, attained at `z = 1`, `θ = ½`. Sharpness does not matter for any
application here.

## Goal B: δ < 1/3

**Why the old route stopped at `1/5`.** In `RankinSharp`, the Phragmén–Lindelöf edges were at
`3/2` and `−1/2`, because only on half-integer lines is the `Γ`-ratio of the functional
equation exactly computable. Interpolating from `|E| ≪ |t|` on `Re s = 3/2` to `|E| ≪ |t|^5` on
`Re s = −1/2` gives `|ζ(2s)D(s)| ≪ |t|³` at `Re s = 0`. With an integer exponent, that forces
Riesz order 4 and `δ = 1/5`.

**New route.**

* **Edges at `1+ε` and `−ε`** (`ConvexEps`). The normaliser is `Γ(s+1)/Γ(3+2ε−s)`, which is
  unimodular on `Re s = 1+ε` because `3+2ε−s = conj(s+1)` there. On `Re s = −ε`, with
  `v = 1−s`, the left-edge ratio becomes

      (s−1) s ∏_{j<m}(v+j) Γ(v)² / ( ∏_{j<m−1}(s+1+j) · Γ(s+1) · (w)(w+1) Γ(w) · (s+3) ),
      w = v + 2ε.

  The real-part differences `2ε` and `1−2ε` are not integers, so the new core inequality is
  used twice: `‖Γ(v)‖²‖v‖ ≤ e²⁰‖s+1‖‖s‖‖Γ(s)‖‖Γ(v+2ε)‖`. What remains is a bounded rational
  function of degree `m+2` over degree `m+2`. This works for every weight, so the general and
  `τ` cases share one proof.
* **Convexity on each line** `0 ≤ σ ≤ 1+ε`. Here `Γ(3+2ε−s) = Γ(conj(s+1) + θ)` with real
  `θ = 2+2ε−2σ ∈ [0,3]`, so `norm_Gamma_add_le` gives `|E(s)| ≪ |s+3|^{3+2ε−2σ}`. This is the
  convexity bound for a degree-4 L-function. Phragmén–Lindelöf is no longer needed for the
  interpolation.
* **Real-exponent Riesz lemma** (`RieszReal`). Only `k + 1 − r > 1` is needed for
  integrability and for the horizontal segments to vanish. Both `RankinError` lemmas were
  copied with `(1+|t|)^{−2}` replaced by `(1+|t|)^{−p}`, `p > 1`.
* **The trade-off.** On `[σ₁, 5/2]`, `F_b = ζ(2s)D(s) − c₀/(s−1) ≪ (1+|t|)^{2+2ε−2σ₁}`. Take
  `ε = σ₁/4`. Then `r = 2 − 3σ₁/2 < 2`, so Riesz order **`k = 2`** suffices, where `RankinSharp`
  needed `k = 4`. One second difference costs a factor `k+1 = 3`, so
  `δ = (1−σ₁)/3 → 1/3` as `σ₁ → 0⁺` (`σ₁ = 1−3δ`). The square twist `b = χ*a` and the Möbius
  step are reused unchanged from `RankinSharp`. The Möbius step needs `δ < 1/2`.

| Route | Edges | `F_b` growth on the contour | Riesz order | `δ` |
|---|---|---|---|---|
| `RankinError` | (crude) | `19` | 20 | `1/84` |
| `RankinSharp` | `−½, 3/2` | `3` (integer, at `σ₁ ≥ 0`) | 4 | `→ 1/5` |
| the brief's plan | `−ε, 1+ε` | `2+2ε` (uniform from `Re s = 0`) | 3 | `→ 1/4` |
| **this directory** | `−ε, 1+ε` | `2+2ε−2σ₁ < 2` (convexity *at* `σ₁`) | **2** | **`→ 1/3`** |

The brief's `1/4` used the exponent at `Re s = 0` on the whole strip. Using the convexity
exponent at `σ₁` itself is what lets the order drop to 2.

## Numerical checks (evidence level 4)

* `scripts/stirling/gamma_ratio_check.py` (mpmath, under a second) samples a grid of
  `Re z ∈ [1,5]`, `|Im z| ≤ 1000`, `θ ∈ [0,1]`. It gives `max |Γ(z)||z|^θ/|Γ(z+θ)| = 1.128`
  against the proved `e¹⁰`. The per-factor inequality `norm_add_ofReal_le` holds with ratio
  `≤ 1`, with equality at `θ ∈ {0,1}`. The ratio `|Γ(σ+it)|/(|t|^{σ−1/2}e^{−π|t|/2})` tends to
  `√(2π)`.
* The error term itself: `scripts/rankinsharp/sharp_check.gp` (`docs/RANKIN_SHARP.md`) measures
  `|S(x) − cx| ≈ x^{0.4}` up to `10⁶`. This is consistent with the proved `x^{2/3+ε}`, Rankin's
  `x^{3/5}` and the conjectured `x^{3/8+ε}`.

## Gaps and next steps

1. **Rankin's `δ = 2/5`** (Landau's `(A−1)/(A+1)` for degree `A = 4`) is still open here. It
   needs the dual-sum method: move the Riesz integral far to the left, use the functional
   equation, and evaluate the dual sum with Stirling asymptotics *with phase*
   (`arg Γ(σ+it)`, which these modulus bounds do not give), then difference with an optimised
   `h`. The `Γ` bounds here are the modulus half of that. The phase half (complex
   `log Γ`/Binet) is not in Mathlib. Estimate: 1000+ lines.
2. **Constants are not explicit for `C_{f,δ}`.** They come from compactness, the PL constant
   and `RL m`. The `Γ` constants themselves (`e¹⁰`, `(n+1)!`) are explicit.
3. The Stirling bounds in `Absolute` are stated with `‖3/2+it‖` for `σ ≥ 3/2`. Smaller `σ`
   follow by `Γ(s) = Γ(s+n)/∏(s+j)`, which is not packaged as a theorem.
4. Level one only, as in `RankinSharpGeneral`.
5. Cosmetic: some `<;>` linter warnings.

## Literature

* R. A. Rankin, Proc. Cambridge Phil. Soc. 35 (1939) 351–372; A. Selberg, Arch. Math.
  Naturvid. 43 (1940): `O(x^{3/5})`.
* E. Landau (1912); K. Chandrasekharan, R. Narasimhan, Ann. of Math. 76 (1962): `(A−1)/(A+1)`.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1 (convexity), §5.A (Stirling).
* Gauss product for `Γ`: e.g. E. T. Whittaker, G. N. Watson, *Modern Analysis*, §12.11. The
  "almost log-concavity" telescoping used here is elementary and was written for this
  formalization. Similar in spirit is Gautschi's inequality `x^{1−θ} ≤ Γ(x+1)/Γ(x+θ)`
  (real `x`).
* See `docs/RANKIN_SHARP.md` and `docs/RANKIN_SHARP_GENERAL.md` for the `δ < 1/5` machinery
  reused here.
