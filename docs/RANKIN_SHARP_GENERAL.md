# Rankin–Selberg error `O(N^{1−δ})` for every `δ < 1/5`, every level-one cusp form (`RamanujanTau/RankinSharpGeneral/`)

> **Current status (2026-11-12).** The stronger error `O(N^{3/5})` is proved for τ and every level-one cusp form by `RankinExact.rankinSelberg_exact` and `rankinSelberg_exact_general`, without Deligne. See [RANKIN_EXACT](RANKIN_EXACT.md).
> The earlier checkpoints and gap lists below describe the development at that stage.

**Status (2026-11-04).** For every level-one cusp form `f ∈ S_k(SL₂(ℤ))`, of any weight `k`,
and every `0 < δ < 1/5`, Lean proves

    |∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C_{f,δ} N^{1−δ}   (N ≥ 1),
    c_f = (3/π)(4π)^k ‖f‖²/(k−1)!.

This generalizes `RankinSharp.rankinSelberg_power_saving_sharp` (which covers `f = Δ` only)
and improves `RankinErrorGeneral.rankinSelberg_power_saving_general` (exponent `1 − 1/84`) to
any exponent above `4/5`. At `f = Δ` it gives back exactly the statement of the `τ` theorem.

**Evidence level 1**: Lean, axiom-clean, no hypotheses. Every headline prints
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no new axiom, no `native_decide`.

Build only this directory: `nice -n 10 lake build RamanujanTau.RankinSharpGeneral.Main`
(4 new files, 1036 lines; needs `RankinSharp/` and `RankinErrorGeneral/` built). Nothing outside
`RankinSharpGeneral/` and this write-up was created or modified. `RankinSharp/`,
`RankinErrorGeneral/` and `RankinSelbergGeneral/` are imported, not edited. The root file does not
import this directory.

## Headline theorems (evidence level 1)

Notation is that of `RankinSelbergGeneral`: `coeffSq f n = ‖(qExpansion 1 f).coeff n‖²`,
`petNormSqF f = ‖f‖²`, `rsConst f = 3/π·(4π)^k·petNormSqF f/(k−1)!`.

| Theorem | File | Statement |
|---|---|---|
| **`rankinSelberg_power_saving_sharp_general`** | `Main` | `∀ f : CuspForm 𝒮ℒ k, 0 < δ → δ < 1/5 → ∃ C, ∀ N ≥ 1, \|∑_{n∈[1,N]} coeffSq f n/n^{k−1} − rsConst f·N\| ≤ C·N^{1−δ}` |
| `rankinSelberg_power_saving_sharp_general'` | `Main` | the same, with the constant written out as `3/π·(4π)^k·petNormSqF f/(k−1)!` |
| `rankinSelberg_power_saving_81_100_general` | `Main` | the case `δ = 19/100`: error `C·N^{81/100}` |
| **`rankinSelberg_power_saving_sharp_discriminant`** | `Main` | at `f = Δ`: `\|∑ τ(n)²/n¹¹ − 3/π·(4π)¹²·petNormSq/11!·N\| ≤ C N^{1−δ}`; an `example` checks that this is literally the type of `RankinSharp.rankinSelberg_power_saving_sharp` |
| `rankinSelberg_power_saving_sharp_intForm` | `Main` | if `IntForm k a`, `a(0) = 0`, `a ≠ 0`: `∃ F` with `qExpansion F = a`, `0 < rsConst F` and the `N^{1−δ}` bound for `∑ a(n)²/n^{k−1}` |
| `rankinSelberg_power_saving_sharp_deltaE a b` | `Main` | the same for `ΔE₄ᵃE₆ᵇ`, weight `12+4a+6b` |
| **`rankinSelberg_power_saving_sharp_weight16/18/20/22/26`** | `Main` | `ΔE₄`, `ΔE₆`, `ΔE₄²`, `ΔE₄E₆`, `ΔE₄²E₆` with `n¹⁵, n¹⁷, n¹⁹, n²¹, n²⁵`, `0 < c_F`, every `δ < 1/5` |

### Intermediate results (evidence level 1)

| Theorem | File | Statement |
|---|---|---|
| **`ratioAM_le`** | `Convex` | for `m ≥ 1`, on `Re s = −1/2`: `‖(s−1)γₘ(1−s)γₘ(s)⁻¹Γ(s+1)Γ(4−s)⁻¹/(s+3)‖ ≤ 125(2m+3)²` |
| `fA_bound` | `Convex` | Step A: `f_A = E(s)Γ(s+1)/(Γ(4−s)(s+3))` bounded on `−1/2 ≤ Re s ≤ 3/2`, given `RSDataM m a κ`, `m ≥ 1`, abscissa `≤ 1` |
| `Efun_line`, **`Efun_bound`** | `Convex` | Steps B, C: `‖E(s)‖ ≤ B‖s+3‖^{n+1}` on `σ_L ≤ Re s ≤ 5/2`, `n = 3−2σ_L ∈ ℕ` |
| `Efun_eq_LSeries'`, `Lam_eq`, `Efun_growth` | `Efun` | `E(s) = (s−1)ζ(2s)D(s)` on `Re s > 1`; `‖E‖ ≤ Ke^{L\|t\|}` on `[−3/2, 5/2]` (any `m`) |
| `Fb_bound` | `Sharp` | `F_b = dslope E 1` is `O((1+\|t\|)³)` on `0 ≤ Re s ≤ 5/2` |
| **`power_saving_fifth_of_RSDataM`** | `Sharp` | `m ≥ 1`, `a ≥ 0`, `a 0 = 0`, `RSDataM m a κ`, abscissa `≤ 1`: `\|∑_{n≤N} aₙ − κ·rsConstM m·N\| ≤ C N^{1−δ}`, every `δ < 1/5` |
| `abscissa_le_one_of_bound` | `Sharp` | `a ≥ 0` and `∑_{n≤N} aₙ = cN + O(N^θ)`, `θ ≤ 1`, imply abscissa of absolute convergence `≤ 1` |
| **`power_saving_sharp_RSFn`** | `Sharp` | for any `[RSFn]` with `m ≥ 2`: `\|∑_{n≤N} cₙ/n^m − ‖G‖·rsConstM m·N\| ≤ C N^{1−δ}` |

## How it was generalized

**What was already generic.** In `RankinSharp`, the square twist and Möbius step
(`Squares`: `chi`, `sum_a_eq_mobius`, `LSeries_chi`; `Mobius`: `mobius_transfer`), the
Phragmén–Lindelöf wrapper `pl_strip`, and the helpers `norm_prod_ge`,
`exists_norm_zeta_le3`, `LSeriesSummable_of_one_lt`, `summable_of_LSeriesSummable` and
`norm_add_three_le` do not depend on the weight. So do the Perron/Riesz lemmas of
`RankinError` (`rieszAsymp_of_continuation`, `riesz_kdiff`, `partial_sum_of_riesz0`). All of
these are imported unchanged.

**What was not generic.** `power_saving_fifth_of_RSData` takes `RSData a κ`. That structure is
hard-wired to the weight-12 factor `gam` (`m = 11`), so `RankinErrorGeneral`'s `RSDataM m a κ`
cannot be fed into it. `Efun`, `Convex` and the `F_b` part of `Sharp` were therefore redone
with `RSDataM m`, `gamM m`, `invGamM m` and `rsConstM m`:

* `Efun`: `invGam1M m s = γₘ(s)⁻¹/s` replaces `Γ(s+11)` by `Γ(s+m)`. The growth bound uses
  `exists_norm_inv_Gamma_le` at `s + m`. That lemma only needs a lower bound on `Re`, so it
  holds for every `m`; the prefactor bound becomes `(4π)^{m+3}`.
* `Convex`: the only real change is the left-edge `Γ`-ratio `ratioAM_le`. The `τ` proof wrote
  `Γ(1−s+11)/Γ(s+11)` as a ratio of products of 12 and 10 factors, giving a degree-15/degree-15
  rational function. With `w = s + m` (so `Re w = m − 1/2 > 0` for `m ≥ 1`) we have
  `1 − s + m = w̄ + 2`, hence `Γ(1−s+m)/Γ(s+m) = w̄(w̄+1)·Γ(w̄)/Γ(w)`. The whole factor is then

      (u−2)·ū·(u−1)·w̄(w̄+1) / (ū(ū+1)(ū+2)(ū+3)·(u+2)) · Γ(w̄)/Γ(w),   u = s+1, Re u = 1/2,

  a degree-5/degree-5 rational function times a unimodular factor. Using `‖w‖ ≤ ‖u‖ + m − 1`
  and `‖u‖ ≥ 1/2`, it is at most `125(2m+3)²`. Steps A, B and C then go through literally as
  before. Only the constant changes, from `25¹⁵` to `RA m = 125(2m+3)²`.
* `Sharp`: the residue is `cB m κ = κ·rsConstM m·π²/6`, from `gfunM_one`. With the same
  contour `σ₁ = 1 − 5δ`, Riesz order 4 and Möbius transfer, the exponent is again
  `δ < 1/5`, uniformly in `m`.

**The abscissa hypothesis** in general weight comes from the `1/84` theorem already proved:
`power_saving_RSFn` gives `∑_{n≤N} aₙ = O(N)`, and `abscissa_le_one_of_bound` (Mathlib's
`LSeriesSummable_of_sum_norm_bigO_and_nonneg`) turns that into `abscissa ≤ 1`.
This is the same route as `abscissa_aTau_le_one`.

**The cusp-form instance and small weights.** As in `RankinErrorGeneral.Cusp`, `rsFnCusp f`
sets `m = k−1` and `cₙ = |a_f(n)|²`, and `rsConst_eq` converts `‖G‖·rsConstM (k−1)` into
`rsConst f`. For `k < 12`, `cuspForm_eq_zero_of_lt` (Mathlib
`CuspForm.rank_eq_zero_of_weight_lt_twelve`) gives `f = 0`; then both sides vanish and `C = 0`
works. So the headline has no weight hypothesis.

**Consistency at Δ.** `rankinSelberg_power_saving_sharp_discriminant` specializes the general
theorem to `k = 12`, `f = Δ`, using `coeffSq Δ n = τ(n)²` and
`petNormSqF Δ = EisensteinReal.petNormSq`. An `example` proves the same type directly by
`RankinSharp.rankinSelberg_power_saving_sharp`, which confirms the two statements are
identical.

| File | Lines | Content |
|---|---|---|
| `Efun.lean` | 227 | `invGam1M`, `Efun`, `Lam`, `E = (s−1)ζ(2s)D` on `Re s > 1`, growth |
| `Convex.lean` | 388 | `ratioAM_le`, Steps A/B/C (`fA_bound`, `Efun_line`, `Efun_bound`) |
| `Sharp.lean` | 218 | `cB`, `Fb_bound`, `power_saving_fifth_of_RSDataM`, `abscissa_le_one_of_bound`, `power_saving_sharp_RSFn` |
| `Main.lean` | 203 | cusp-form headline, `Δ` check, integer-coefficient instances (weights 16–26), `#print axioms` |

## Numerical evidence (level 4)

No new numerics were run. The statement is fully proved and the constant is not effective.
`docs/RANKIN_SELBERG_GENERAL.md` tabulates `S(x)/x → c_f` for `k = 12, …, 26`.
`docs/RANKIN_SHARP.md` shows errors of size about `x^{0.4}` for `τ`.

## Gaps and what remains

* **Not effective.** `C_{f,δ}` comes from compactness and Phragmén–Lindelöf, so it is not
  explicit. It depends on `k` only through `(4π)^{m+3}`, `125(2m+3)²` and the `RSFn` data.
* **`δ → 1/4` and Rankin's `2/5`** need the same missing pieces as for `τ`: a
  Stirling-type bound `|Γ(x+it)/Γ(y+it)| ≪ |t|^{x−y}` for non-integer `x−y`, and a Riesz lemma
  with a real growth exponent (for `1/4`), plus the dual-sum/Voronoi analysis (for `2/5`). See
  `docs/RANKIN_SHARP.md` §Gaps. Any improvement of the `m = 11` chain should carry over, because
  the Γ-ratio here has bounded degree for every `m`.
* **Level 1 only.** Higher level would need the fundamental domain and cusps of `Γ₀(N)`.
* Cosmetic: the `<;>` linter warnings copied from `RankinSharp/Convex.lean`.

## Literature

* R. A. Rankin, Proc. Cambridge Phil. Soc. 35 (1939) 351–372; A. Selberg, Arch. Math.
  Naturvid. 43 (1940). They prove `∑_{n≤x}|a_f(n)|²/n^{k−1} = c_f x + O(x^{3/5})` for every
  cusp form.
* E. Landau (1912); K. Chandrasekharan, R. Narasimhan, Ann. of Math. 76 (1962): the exponent
  `(A−1)/(A+1)` for degree `A`.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1 (convexity), §14.
* See `docs/RANKIN_SHARP.md` (the `τ` proof) and `docs/RANKIN_ERROR_GENERAL.md` (the general
  weight Rankin–Selberg data).
