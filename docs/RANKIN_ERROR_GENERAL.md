# A power-saving error term for Rankin–Selberg, every level-one cusp form (`RamanujanTau/RankinErrorGeneral/`)

> **Current status (2026-11-12).** The stronger error `O(N^{3/5})` is proved for τ and every level-one cusp form by `RankinExact.rankinSelberg_exact` and `rankinSelberg_exact_general`, without Deligne. See [RANKIN_EXACT](RANKIN_EXACT.md).
> The earlier checkpoints and gap lists below describe the development at that stage.

**Status (2026-11-04).** For every level-one cusp form `f ∈ S_k(SL₂(ℤ))`, of any weight `k`,
with q-expansion coefficients `a_f(n)`, Lean proves

    |∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C_f N^{1−1/84}   (N ≥ 1),
    c_f = (3/π)(4π)^k ‖f‖²/(k−1)!,   ‖f‖² = ∫_𝓕 |f|² y^k dx dy/y².

This is **evidence level 1**: Lean, axiom-clean, no hypotheses. The headline is
`rankinSelberg_power_saving_general`. It generalizes `RankinError.rankinSelberg_power_saving_84`,
which covers `f = Δ` only. At `f = Δ` it gives back exactly the statement of that theorem
(`rankinSelberg_power_saving_discriminant`).

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`. Build only this directory:
`nice -n 10 lake build RamanujanTau.RankinErrorGeneral.Main`.

Nothing outside `RankinErrorGeneral/` and this write-up was modified. `RankinError/`,
`RankinSelbergGeneral/` and `EisensteinReal/` are imported, not edited. The root file does not
import this directory.

## Headline theorems (evidence level 1)

Notation is that of `RankinSelbergGeneral`: `coeffSq f n = ‖(qExpansion 1 f).coeff n‖²`,
`petNormSqF f = ‖f‖²`, and `rsConst f = 3/π·(4π)^k·petNormSqF f/(k−1)!`.

| Theorem | File | Statement |
|---|---|---|
| **`rankinSelberg_power_saving_general`** | `Cusp` | `∀ f : CuspForm 𝒮ℒ k, ∃ C, ∀ N ≥ 1, \|∑_{n∈[1,N]} coeffSq f n/n^{k−1} − rsConst f·N\| ≤ C·N^{1−1/84}` |
| `rankinSelberg_power_saving_general'` | `Cusp` | the same, with the constant written out as `3/π·(4π)^k·petNormSqF f/(k−1)!` |
| **`rankinSelberg_power_saving_discriminant`** | `Cusp` | at `f = Δ`: `\|∑ τ(n)²/n¹¹ − 3/π·(4π)¹²·EisensteinReal.petNormSq/11!·N\| ≤ C N^{1−1/84}`. This is the statement of `RankinError.rankinSelberg_power_saving_84`, which an `example` in `Cusp` checks against it |
| `rankinSelberg_power_saving_intForm` | `Main` | if `IntForm k a`, `a(0) = 0` and `a ≠ 0`, then `∃ F` with `qExpansion F = a`, `0 < rsConst F`, and the power saving for `∑ a(n)²/n^{k−1}` |
| `rankinSelberg_power_saving_deltaE a b` | `Main` | the same for `ΔE₄ᵃE₆ᵇ`, weight `12+4a+6b` |
| **`rankinSelberg_power_saving_weight16/18/20/22/26`** | `Main` | `ΔE₄`, `ΔE₆`, `ΔE₄²`, `ΔE₄E₆`, `ΔE₄²E₆` in integer coefficients, with `n¹⁵, n¹⁷, n¹⁹, n²¹, n²⁵`, and `0 < c_F` |

### Milestones (each a separate theorem, evidence level 1)

| Theorem | File | Statement |
|---|---|---|
| `gammaM_ratio_le` | `Gamma` | for `m ≥ 2`, on `Re s = −3/2`: `‖γₘ(1−s)/γₘ(s)‖ ≤ (m+1)⁴(‖s+2‖+13)^{17}`, where `γₘ(s) = 2π^{−s}Γ(s)Γ(s+m)(4π)^{−s−m}` |
| `fPLM_bound` | `PL` | Phragmén–Lindelöf: given `RSDataM m a κ` and `m ≥ 2`, `(s(s−1)Λ₀+κ)/(γₘ(s)(s+3)^{19})` is bounded on `[−3/2, 5/2]` |
| **`power_saving_84_of_RSDataM`** | `Saving` | for `m ≥ 2`, `a ≥ 0`, `a 0 = 0`, `∑aₙn^{−5/2} < ∞` and `RSDataM m a κ`: `\|∑_{n≤N} aₙ − κ·3(4π)^{m+1}/(π m!)·N\| ≤ C N^{1−1/84}` |
| `exists_cf_le`, `summable_aF` | `RSFn` | `cₙ ≤ K n^{m+1}` (from Parseval and boundedness of `G`), so `∑ (cₙ/n^m) n^{−5/2} < ∞` |
| `lintegral_mellin_horocycleG` | `RSFn` | `∫₀^∞ I(y)y^{s−2}dy = ∑ cₙΓ(s+m)(4πn)^{−s−m}` in `[0,∞]`, for real `s > −m` |
| `PhiG_inv`, `PhiG_sub_le`, `rsFEG`, `rsFEG_Λ₀_bdd` | `ThetaG` | `Φ(1/t) = tΦ(t)`; `0 ≤ Φ(t)−‖G‖ ≤ C_R(t−1)^{−R}`; `WeakFEPair`; `Λ₀` bounded on strips |
| `unfold_thetaG` | `UnfoldG` | `∫_𝓕 G(Θ_z(t)−1)dμ = 2∫₀^∞ I(v)h_t(v)dv/v²` in `[0,∞]` |
| `lintegral_mellin_PhiG` | `UnfoldG` | `∫₀^∞ t^{σ−1}(Φ−‖G‖)dt = 2Γ(σ)π^{−σ}ζ(2σ)∑cₙΓ(σ+m)(4πn)^{−σ−m}` |
| **`rsUnfoldG`** | `UnfoldProofG` | `mellin(Φ−‖G‖)(s) = γₘ(s)ζ(2s)∑(cₙ/n^m)n^{−s}` for `Re s > 2` |
| `rsDataG` | `UnfoldProofG` | `RSDataM m aF ‖G‖`, with no hypotheses |
| **`power_saving_RSFn`** | `UnfoldProofG` | for any `[RSFn]` with `m ≥ 2`: `\|∑_{n≤N} cₙ/n^m − ‖G‖·3(4π)^{m+1}/(π m!)·N\| ≤ C N^{1−1/84}` |

## How it was generalized

**One abstract class.** `RSFn` (in `RSFn.lean`) extends `RankinSelbergGeneral.HoroFn`, which
packages a continuous, nonnegative, bounded, `SL₂(ℤ)`-invariant `G`. It adds three things:

* a weight `m : ℕ` and coefficients `cf : ℕ → ℝ` with `cf ≥ 0` and `cf 0 = 0`;
* `parseval`: `∫₀¹ G(x+iy)dx = ∑ cₙ y^{m+1} e^{−4πny}`;
* `exp_decay`: `G(z) ≤ K e^{−c Im z}` for `Im z ≥ ½`.

The `Δ`-specific files were copied with `variable [RSFn]`. Each copy changes only `G_pos` to
`G_nonneg`, `exists_G_exp_le` to `RSFn.exp_decay`, `Ihor` to `GFinal.Aint`, `τ(n)²` to `cₙ`,
and `11` to `m`, and its names carry the suffix `G`/`M`:

| Original | Copy |
|---|---|
| `ThetaInt` + `RSFE` | `ThetaG` |
| `UnfoldTheta` + `RSMellin` | `UnfoldG` |
| `RSUnfoldProof` | `UnfoldProofG` |
| `EisensteinReal/Mellin` (E3a) | the end of `RSFn` |

The `G`-independent files are imported unchanged: `Theta`, `ThetaBound` (except
`exists_G_exp_le`), `HMeasure`, `Coset`, `Riesz`, `RieszK`, `RieszKernel`, `Contour`, `Perron`,
`PerronShift`, `GammaBound`. The same holds for the generic lemmas of `Convexity` and `Landau2`
(`norm_LSeries_le`, the two ζ bounds, `D5`, `norm_le_exp_abs_im`).

**General weight in the Γ-factors.** `Convexity`, `Landau`, `Landau2` and `Landau3` depend on
`m = 11` through `gam`. They were redone with a parameter `m` in `Gamma`, `PL` and `Saving`.
The only real mathematical change is the left-edge Γ-ratio. The old proof bounded
`Γ(1−s+11)/Γ(s+11)` as a ratio of products of 13 and 9 factors, which gives degree 13. That
degree grows with `m`, so it would worsen the exponent. The new proof takes `w = s+m`, so that
`Re w = m − 3/2 > 0` (this needs `m ≥ 2`). Then `1−s+m = w̄+4`, so

    Γ(1−s+m)/Γ(s+m) = (∏_{j<4}(w̄+j))·Γ(w̄)/Γ(w),

which has degree 4 times a unimodular factor. The total degree is therefore `4+4 = 8 ≤ 17` for
every `m`, so the Phragmén–Lindelöf normalization `(s+3)^{19}` is unchanged. The order of the
Riesz mean stays `20` and the saving stays `(1/4)/21 = 1/84`, uniformly in `k`. The dependence
on `k` sits only in the constants `(m+1)⁴` and `(4π)^{m+3}`, and those go into `C_f`.

**The cusp-form instance** (`rsFnCusp f hk`, in `Cusp.lean`) sets `m = k−1` and
`cₙ = |a_f(n)|²`, and gets the class fields as follows:

* the `HoroFn` part is `RankinSelbergGeneral.horoFn f`;
* `parseval` is `RankinSelberg.hasSum_normSq_coeff`;
* `exp_decay` is `exists_Gf_exp_le`, a copy of `exists_G_exp_le` with `Δ` replaced by `f` and
  `12` by `k`, using Mathlib's `CuspFormClass.exp_decay_atImInfty'` for every cusp form.

**No weight hypothesis in the headline.** The general machinery needs `m = k−1 ≥ 2`. For
`k < 12`, Mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` gives `f = 0`; then both sides
vanish and `C = 0` works. So `rankinSelberg_power_saving_general` holds for every `k`.

**Consistency at Δ.** `petNormSqF Δ = EisensteinReal.petNormSq` and `coeffSq Δ n = τ(n)²` (via
`TauBound.qExpansion_discriminant_coeff_tau`). With these, the general theorem gives exactly the
statement of `RankinError.rankinSelberg_power_saving_84`, with the same constant
`(3/π)(4π)¹²‖Δ‖²/11!` and the same exponent. `gamM 11 = gam` and `invGamM 11 = invGam` hold
definitionally (`gamM_eleven`, `invGamM_eleven`).

| File | Lines | Content |
|---|---|---|
| `Gamma.lean` | 185 | `gamM`, `invGamM`, `RSDataM`, `gammaM_ratio_le` |
| `PL.lean` | 218 | Phragmén–Lindelöf `fPLM_bound` |
| `Saving.lean` | 181 | `gfunM`, `rsConstM`, `FfunM_bound`, `power_saving_84_of_RSDataM` |
| `RSFn.lean` | 184 | class `RSFn`; `cₙ ≪ n^{m+1}`; strip side of the unfolding |
| `ThetaG.lean` | 222 | `Φ`, the theta functional equation, `rsFEG` |
| `UnfoldG.lean` | 257 | unfolding (U), real Mellin transform |
| `UnfoldProofG.lean` | 260 | identity theorem, `rsDataG`, `power_saving_RSFn` |
| `Cusp.lean` | 175 | cusp-form instance, headline, `Δ` check |
| `Main.lean` | 120 | integer-coefficient instances (weights 16–26), `#print axioms` |

The total is 1802 lines, mostly mechanical copies.

## Numerical evidence (level 4)

`docs/RANKIN_SELBERG_GENERAL.md` already tabulates `S(x)/x → c_f` for `k = 12, 16, 18, 20, 22, 26`
up to `x = 10⁵`, from `scripts/rankinselberggeneral/check.gp`. No new numerics were run: the
power-saving statement is fully proved, and its constant `C_f` is not effective.

## Gaps and what remains

* **Not effective.** `C_f` comes from compactness and Phragmén–Lindelöf bounds, so it is not
  explicit. This is the same as for `Δ`.
* **The exponent `1/84` is not sharp.** Rankin–Selberg give `3/5`, that is, error
  `O(N^{3/5})`. Sharpening the exponent is being done separately in `RankinSharp/`, which was not
  touched here. Any improvement of the `m = 11` chain should carry over, because the
  generalization keeps the same exponents, uniformly in `m`.
* **Level 1 only.** Higher level would need the fundamental domain and cusps of `Γ₀(N)`.

## Literature

* R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n) … I, II*, Proc.
  Cambridge Phil. Soc. 35 (1939); A. Selberg, Arch. Math. Naturvid. 43 (1940). They prove the
  mean square `∑_{n≤x}|a_f(n)|²/n^{k−1} = c_f x + O(x^{3/5})` for every cusp form.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, §13; Iwaniec–Kowalski §14.
* E. Landau (1912), for the contour/smoothing lemma; Phragmén–Lindelöf (Mathlib
  `PhragmenLindelof.vertical_strip`).
