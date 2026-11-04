# A sub-Hecke bound for Ramanujan's τ (Kloosterman 1927 route)

**Status (round 3, 2026-11-03): UNCONDITIONAL.** `tau_isBigO_47_8_unconditional`
(`TauBound/Unconditional.lean`): for every `ε > 0`, `τ(n) = O(n^{47/8+ε})`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`. Build:
`nice -n 10 lake build RamanujanTau.TauBound.Unconditional`.

> **Superseded exponent (2026-11-04).** This 47/8 result has since been improved twice, reusing the unconditional
> `PoincareFormula` from this directory: `Stepanov.tau_isBigO_35_6_unconditional` (Salié, 35/6; see
> [STEPANOV](STEPANOV.md)) and `StepanovAS.tau_isBigO_23_4_unconditional` (Weil, 23/4; see
> [STEPANOV_ARTIN_SCHREIER](STEPANOV_ARTIN_SCHREIER.md)). The repository's best τ bound is now Weil's
> `τ(n) = O(n^{23/4+ε})`. Deligne's `11/2 + ε` is still not formalized.

Goal: improve on Hecke's bound `τ(n) = O(n⁶)` (`tau_isBigO_real`, `TauHeckeBound.lean`) with Kloosterman's
exponent `τ(n) = O(n^{47/8+ε})` (`47/8 = 6 − 1/8`). Deligne's `11/2 + ε` is out of scope (the 35/6 and 23/4 improvements are noted above).

Directory: `RamanujanTau/TauBound/` (20 files, about 2900 lines). Scripts: `scripts/taubound/`.
These files were written outside the root import; they have since been added to the root `RamanujanTau.lean`.

## Route chosen and why

The Poincaré-series / Kloosterman-sum route (A) was chosen over Rankin–Selberg (B). Mathlib has no
real-analytic Eisenstein series, no integration over a fundamental domain, and no unfolding. What it does have:

* `S₁₂(SL₂ℤ) = ℂΔ` (`CuspForm.exists_smul_discriminant_of_weight_eq_twelve`);
* coefficients as horizontal-line integrals (`ModularFormClass.qExpansion_coeff_eq_intervalIntegral`);
* primitive additive characters on `ZMod N` and their orthogonality (`ZMod.stdAddChar`,
  `AddChar.sum_mulShift`);
* Japanese-bracket integrability (`integrable_rpow_neg_one_add_norm_sq`).

Two choices keep the work elementary:

* **No Bessel functions.** The unfolded integral is
  `K(n,c;y) = ∫_ℝ w^{-12} e(-1/(c²w)) e(-nw) dx` with `w = x+iy`.
  It is bounded with absolute values only, using `e^{-t} ≤ M_r t^{-r}`:
  `|K(n,c;1/n)| ≤ B_r n^{11-r} c^{2r}` for `0 ≤ r < 11/2`.
  This is exactly the `J₁₁ ≪ min(x^{11}, 1)` information that is needed, without any oscillation argument.
* **No Weil bound.** Kloosterman's own elementary fourth-moment argument handles primes. The averaging
  trick `u ↦ u(1+p^j t)` handles prime powers. Twisted multiplicativity handles everything else.

## Evidence levels

### (1) Lean-proved, axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorry` or `native_decide`)

| Theorem | File | Statement |
|---|---|---|
| `norm_kInt_le` | `Basic.lean` | `‖K(n,c;y)‖ ≤ M_r e^{2πny} (2πy/c²)^{-r} (y²)^{r-6} y J_r` for `0≤r<11/2`, `c≠0`, `y>0` |
| `norm_kInt_inv_le` | `Endgame.lean` | `‖K(n,c;1/n)‖ ≤ B_r n^{11-r} c^{2r}` |
| `tau_bound_of_kloosterman` | `Endgame.lean` | `KloostermanBound α → PoincareFormula → ∃C, ∀n≥1, \|τ n\| ≤ C n^{11-r}` whenever `0≤α`, `0≤r`, `α+2r<11` |
| `tau_isBigO_47_8` | `Endgame.lean` | `(∀δ>0, KloostermanBound (3/4+δ)) → PoincareFormula → ∀ε>0, τ =O(n^{47/8+ε})` |
| `kloosterman_eq_kl`, `kl_mul_left_unit`, `kl_mul_coprime` | `KlBasic.lean` | bridge to `ZMod`; `S(ta,b)=S(a,tb)`; twisted multiplicativity `S(m,n;qr)=S(um,un;q)S(vm,vn;r)` for `ur+vq=1` |
| `sum_norm_kl_pow_four`, `card_solutions_le` | `KlPrime.lean` | `∑_{a,b}\|S(a,b;p)\|⁴ = p²N`, `N ≤ 3(p−1)²` |
| `norm_kl_prime_pow_four_le` | `KlPrime.lean` | **Kloosterman 1927**: `\|S(1,b;p)\|⁴ ≤ 3p³` |
| `kl_eq_sum_filter`, `card_sqrt_le` | `KlPrimePow.lean` | averaging identity; at most `4p^j` unit solutions of `p^j(u²−b)=0` mod `p^k` |
| `norm_kl_primePow_le` | `KlPrimePow.lean` | `\|S(1,b;p^k)\| ≤ 4p^{⌈k/2⌉}` for `k ≥ 2` |
| `norm_kloosterman_le_klMajor` | `KlAssembly.lean` | `\|S(1,n;c)\| ≤ 4^{ω(c)} c^{3/4}` for all `c`, `n` |
| `four_pow_omega_le` | `KlAssembly.lean` | `4^{ω(c)} ≤ K_δ c^δ` |
| `kloostermanBound_three_quarters` | `KlAssembly.lean` | **`KloostermanBound (3/4+δ)` for every `δ>0`** (hypothesis discharged) |
| `tau_isBigO_47_8_of_poincare` | `Main.lean` | `PoincareFormula → ∀ε>0, τ(n) = O(n^{47/8+ε})` |
| `poincareFormula_of_cuspForm` | `Reduction.lean` | a cusp form `f` with `HasPoincareCoeffs f` and `a₁(f) ≠ 0` gives `PoincareFormula` (via `S₁₂ = ℂΔ`) |
| `poincareFormula_of_hyps`, `tau_isBigO_47_8_of_poincare_hyps` | `Poincare.lean` | `PoincareIsCuspForm → PoincareUnfolding → PoincareFirstCoeffNeZero → ∀ε>0, τ = O(n^{47/8+ε})` |

| `unfold_c` | `UnfoldC.lean` | `∑_{d∈ℤ} ∫₀¹ e(-nw) T(c,d,w) du = c^{-12} S(1,n;c) K(n,c;y)` (HasSum), `c ≥ 1`, `y > 0` |
| `kloosterman_symm` | `UnfoldC.lean` | `S(m,n;c) = S(n,m;c)` |
| **`poincareUnfolding`** | `Unfold.lean` | **`PoincareUnfolding`: hypothesis discharged** (Mathlib coefficient integral + Eisenstein-dominated DCT + `unfold_c`) |
| `summable_poincareTerm`, `poincare_eq_tsum_prod` | `Honest.lean` | the double series in `poincare z` is absolutely summable for every `z ∈ ℍ` (no `tsum` junk) |
| `summable_firstCoeff` | `Honest.lean` | the series in `PoincareFirstCoeffNeZero` is absolutely summable (that hypothesis is not trivially true via `tsum = 0`) |
| `integral_lipInt` | `Lipschitz.lean` | `∫_ℝ (x+i)^{-(m+1)} e(-(x+i)) dx = (-2πi)^{m+1}/m!` for `m ≥ 11` (from Mathlib's `EisensteinSeries.qExpansion_identity`, computing `∫₀¹ e(-w)∑_d (w+d)^{-k} du` two ways) |
| `hasSum_kInt_one` | `KSeries.lean` | `K(1,1;1) = ∑_j (-4π²)^{6+j}/(j!(11+j)!)` (`= 2πJ₁₁(4π)`) |
| `kInt_one_one_ge` | `Numerics.lean` | `K(1,1;1) ≥ 1.8`: the partial sum over `j < 20` is `≥ 1.8254` (`norm_num` with `π ∈ (3.141592, 3.141593)`), and the tail is `≤ 40⁶e⁴⁰/31!` |
| `norm_kInt_one_le` | `Numerics.lean` | `‖K(1,c;1)‖ ≤ e^{2π}π` |
| **`poincareFirstCoeffNeZero`** | `Numerics.lean` | **`PoincareFirstCoeffNeZero`: hypothesis discharged**. `Re(…) ≥ 1 + 1.8 − 1.99 > 0`, with the `c ≥ 2` tail `≤ 3450(2^{-11} + 3^{-9}π²/6)` |
| `tau_isBigO_47_8_of_cuspForm` | `Final.lean` | `PoincareIsCuspForm → ∀ε>0, τ(n) = O(n^{47/8+ε})` (superseded by the unconditional headline) |
| **`tau_isBigO_47_8_of_cusp_and_coeff`** | `Honest.lean` | **`PoincareIsCuspForm → PoincareFirstCoeffNeZero → ∀ε>0, τ(n) = O(n^{47/8+ε})`** |
| `ee_smul_eq_of_bottom_row`, `pTerm_smul`, `pSeries_smul` | `CuspFormSlash.lean` | `e(gz)` depends only on the bottom row of `g ∈ SL₂ℤ`; with `pTerm v z = (cz+d)^{-12} e(γ_v z)` (`γ_v` from `bottom_row_surj`), `pSeries(γz) = j(γ,z)^{12} pSeries z` by re-indexing `v ↦ vγ` on `gammaSet 1 1 0` |
| `pInd_pos`, `pInd_neg`, `pF_zero`, **`pSeries_eq_two_mul_poincare`** | `CuspFormSum.lean` | `c>0` terms are `poincareTerm` (top-left entry `≡ d̄ mod c`), `pTerm(−v) = pTerm v`, `c=0` gives `2e(z)`; hence `∑_{(c,d)=1} pTerm = 2·poincare` |
| `mdiff_pSeries` | `CuspForm.lean` | holomorphy: `differentiableOn_tsum_of_summable_norm` on open strips, Eisenstein majorant |
| `norm_pTerm_le_decay`, `norm_pSeries_le`, `isZeroAtImInfty_pHalf` | `CuspForm.lean` | `‖pTerm v z‖ ≤ \|cz+d\|^{-10}/y` (from `e^{-t} ≤ 1/t`); `‖pSeries z‖ ≤ C/y` for `y ≥ 1` after a `T`-translate |
| **`poincareCuspForm`**, **`poincareIsCuspForm`** | `CuspForm.lean` | `pSeries/2 : CuspForm 𝒮ℒ 12`, equal to `poincare` on `ℍ`: **`PoincareIsCuspForm` discharged** |
| **`tau_isBigO_47_8_unconditional`** | `Unconditional.lean` | **`∀ε>0, τ(n) = O(n^{47/8+ε})`, no hypotheses.** This is the headline. |

Sanity check: `kloostermanBound_one`, the trivial bound `|S| ≤ c`, gives back only `O(n^{6+ε})`. All of the gain
comes from the proved Kloosterman bound.

### (2) Lean-proved, conditional on named hypotheses

**Update (round 3).** `PoincareIsCuspForm` is now proved (`poincareIsCuspForm`, `CuspForm.lean`), so
**no hypotheses remain**: the headline `tau_isBigO_47_8_unconditional` is in level (1). The text below
records the history.

**Update (round 2).** `PoincareUnfolding` and `PoincareFirstCoeffNeZero` are now proved (`poincareUnfolding`,
`poincareFirstCoeffNeZero`). The current headline is `tau_isBigO_47_8_of_cuspForm`. **Its only remaining
hypothesis is `PoincareIsCuspForm`.** The literal-truth checks are
proved: `summable_poincareTerm` and `summable_firstCoeff` show that no `tsum` in either remaining hypothesis is a
junk value.

The original headline `tau_isBigO_47_8_of_poincare_hyps` had three hypotheses, all about the explicit Poincaré series
`poincare z = e(z) + ∑_{c≥1} ∑_{(c,d)=1} (cz+d)^{-12} e(d̄/c − 1/(c(cz+d)))` (`Poincare.lean`):

1. **`PoincareIsCuspForm`**: `poincare` agrees on `ℍ` with some `f : CuspForm 𝒮ℒ 12`. This needs absolute and
   locally uniform convergence (dominated by the weight-12 Eisenstein series, since `|e(γz)| ≤ 1`), slash-invariance
   by re-indexing `Γ_∞\Γ`, and vanishing at `∞`.
2. **`PoincareUnfolding`** (**now proved**): such an `f` satisfies
   `a_n(f) = [n=1] + ∑_{c≥1} c^{-12} S(1,n;c) K(n,c;1/n)`. The steps are:
   * the Mathlib coefficient integral at height `1/n`;
   * swap `∫₀¹` with `∑_{c,d}` (Eisenstein domination);
   * write `d = d₀ + ct` and use `∑_t ∫₀¹ = ∫_ℝ`;
   * translate by `d₀/c`;
   * collect `∑_{d₀} e((d̄₀+nd₀)/c) = S(1,n;c)`.
3. **`PoincareFirstCoeffNeZero`** (**now proved**): `1 + ∑_{c≥1} c^{-12} S(1,1;c) K(1,c;1) ≠ 0`.

Intermediate interface: `PoincareFormula` (`Endgame.lean`), which says that `λτ(n) = [n=1] + ∑ c^{-12}S(1,n;c)K(n,c;1/n)` for some `λ ≠ 0`.

### (3) Paper proof only

All three hypotheses are classical: Poincaré, Petersson (1932); see Iwaniec, *Topics in Classical Automorphic Forms*,
§3.1–3.2 and Thm 3.4. A Lean proof would go as follows.

* (1) and (2) are routine but long: an estimated 800–1500 lines of Lean. Of the Mathlib infrastructure, only the
  Eisenstein-series summability and vertical-strip bounds (`EisensteinSeries.summand_bound_of_mem_verticalStrip`,
  `summable_one_div_norm_rpow`) and the `gammaSet` re-indexing pattern can be reused.
* (3), cheapest route:
  1. Prove the Lipschitz integral `∫_{ℝ+iy} w^{-k} e(-w) dx = (−2πi)^k/(k−1)!`. It follows from Mathlib's
     `EisensteinSeries.qExpansion_identity` together with the same `∑_t ∫₀¹ = ∫_ℝ` unfolding lemma.
  2. Expand `e(−1/w)` termwise. This gives `K(1,1;1) = (2π)^{12} ∑_j (−4π²)^j/(j!(11+j)!) = 2πJ₁₁(4π) ≈ 1.8305`.
  3. Certify the alternating series with `π ∈ (3.141592, 3.141593)`. The tolerance is loose (about ±0.8).
  4. Bound the tail `c ≥ 2` by `norm_kInt_le` with `y = 1`: it is at most about 0.2.
* Alternative for (3): Petersson positivity `⟨P₁,P₁⟩ > 0`. It needs fundamental-domain integration, which Mathlib
  lacks.

### (4) Numerical evidence only

These scripts use `mpmath`, at 20–30 digits.

* `scripts/taubound/check_kint.py`:
  * `c^{-12}K(n,c;1/n) = 2πn^{11/2}J₁₁(4π√n/c)/c`, checked to 12 digits at four `(n,c)` pairs;
  * the exact formula gives `p(n)/p(1) = τ(n)` for `n ≤ 5`, to about 10 digits;
  * `p(1) = 2.8402873751675`.
* `scripts/taubound/check_poincare_def.py`: the Lean definition `poincare` (truncated at `c ≤ 40`, `|d| ≤ 400`)
  equals `2.840287375·Δ(z)` at two test points. This confirms the normalisation, including the `e(d̄/c)` sign
  convention and the factor in `PoincareFirstCoeffNeZero`.

## What it would take to finish

The order of cost, cheapest first:

1. (2) `PoincareUnfolding`: DONE (about 450 lines, `UnfoldC.lean` and `Unfold.lean`).
2. (3) `PoincareFirstCoeffNeZero`: DONE (`Lipschitz.lean`, `KSeries.lean`, `Numerics.lean`).
3. (1) `PoincareIsCuspForm`: **DONE** (round 3, about 500 lines: `CuspFormSlash.lean`, `CuspFormSum.lean`,
   `CuspForm.lean`). The plan below was followed, except that slash invariance is proved for every
   `γ ∈ SL₂ℤ` at once via the cocycle `j(γ_v, γz) j(γ,z) = j(γ_vγ, z)` (as in Mathlib's
   `eisensteinSeries_slash_apply`), so the generators `S`, `T` were not needed, and the decay bound uses
   `e^{-t} ≤ 1/t` (giving `C/y`) instead of `y^{-6}`. Original plan:
   * Define `E(c,d,z) = (cz+d)^{-12} e((Bz−A)/(cz+d))` for coprime `(c,d) ∈ ℤ²`, where `cA + dB = 1` (`Int.gcdA`, `Int.gcdB`).
   * Prove well-definedness: if `ad − bc = 1` then `e((az+b)/(cz+d))` is the same, since `(a−a', b−b') ∈ ℤ(c,d)`.
   * The covariances `E(c,d,Sz)z^{-12} = E(d,−c,z)` and `E(c,d,z+1) = E(c,c+d,z)` then make slash-invariance a
     re-indexing of `∑_{ℤ²}`. Relate `∑_{ℤ²} E = 2·poincare` by splitting `c = 0`, `c > 0`, `c < 0`, using
     `E(−c,−d) = E(c,d)`.
   * Conclude with `slash_action_generators_SL2Z`, following the template of `CuspForm.discriminant`.
   * Holomorphy: `differentiableOn_tsum_of_summable_norm` on open vertical strips, with the bound from
     `summand_bound_of_mem_verticalStrip`.
   * Zero at `∞`: reduce to `|Re z| ≤ 1/2` by `poincare (z+n) = poincare z`, then bound by
     `e^{-2πy} + y^{-6}·R·∑‖v‖^{-6}`.
   * The original sketch: The pieces are a choice of `γ_v ∈ SL₂ℤ` for each coprime
   `v = (c,d)`, well-definedness of `e(γ_v z)` modulo `T`, slash-invariance by re-indexing, `MDifferentiable` via
   locally uniform convergence, and the value at `∞` (equivalently `a₀ = 0`, which follows from the unfolding with
   `n = 0` and letting `y → ∞`).

Nothing remains to be proved. All three former hypotheses are now theorems.

## Literature checked

* Kloosterman, *Asymptotische Formeln für die Fourierkoeffizienten ganzer Modulformen* (1927): exponent `k/2 − 1/8`
  via `S ≪ c^{3/4+ε}`.
* Salié (1931/33) and Davenport (1933): `c^{2/3}`, giving `6 − 1/6`.
* Rankin (1939): `29/5` via Rankin–Selberg (stronger than Salié's `35/6`, weaker than Weil's `23/4`).
* Weil (1948): `c^{1/2}`, giving `23/4`.
* Iwaniec, *Topics*, §3 and §4.3 (the elementary prime-power Kloosterman bound).

The framework here gives `11 − r` for every `r < (11−α)/2`. With Salié's `α = 2/3 + δ` it would give `6 − 1/6 + ε`,
and with Weil's `α = 1/2 + δ` it would give `23/4 + ε`. Only `α = 3/4 + δ` is proved in this directory; both
improvements were later supplied elsewhere through `WeilKloosterman.tau_isBigO_of_kloostermanFamily`
(`Stepanov.saliePrimeBound` for `35/6`, `StepanovAS.weilPrimeBound` for `23/4`).
