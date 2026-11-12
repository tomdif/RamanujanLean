# Lower bound for the mean square of L(Δ, s) on the critical line Re s = 6

> **Current status (2026-11-12).** The sharp leading asymptotic is proved by `CriticalMeanSquareAsymp.critical_mean_square_asymptotic`; see [CRITICAL_MEAN_SQUARE_ASYMP](CRITICAL_MEAN_SQUARE_ASYMP.md). The later [Good second-term proof](GOOD_SECOND_TERM.md#7-2026-11-06-offdiaghyp-1600-discharged-goods-asymptotic-is-unconditional) also gives the second term with a power-saving error.
> The earlier checkpoints and gap lists below describe the development at that stage.

Module: `RamanujanTau/CriticalMeanSquareLower/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.CriticalMeanSquareLower.Main` (exit 0).

## Evidence levels

| result | level |
|---|---|
| `∫_0^T |L(Δ,6+it)|² ≫ T log T` | **(1) Lean, axiom-clean** |
| `∫_0^T |L(Δ,6+it)|² ≍ T log T`, `=Θ[atTop] T log T` (with `CriticalMeanSquare` upper bound) | **(1) Lean, axiom-clean** |
| ray integral `∫ |Δ|²` along `Im τ = κ|Re τ|` is `≫ κ^{-12} log(1/κ)` | **(1) Lean, axiom-clean** |
| weighted asymptotic, `∫_0^T |L|² ~ 2c T log T` (Good 1982) | (3) literature only, not formalized |

`#print axioms` for every headline gives `[propext, Classical.choice, Quot.sound]`. There are
no named hypotheses, no `sorry`, no `native_decide` and no `axiom`.

## Headlines (`namespace RamanujanTau.CriticalMeanSquareLower`)

```lean
theorem critical_mean_square_lower : ∃ c T₀ : ℝ, 0 < c ∧ ∀ T ≥ T₀,
    c * T * Real.log T ≤ ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2

theorem critical_mean_square_order : ∃ c C T₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ T ≥ T₀,
    c * T * Real.log T ≤ ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ∧
      ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T

theorem critical_mean_square_isTheta :
    (fun T : ℝ => ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2) =Θ[atTop] fun T => T * Real.log T

/-- ray lower bound, κ = cot β -/
theorem ray_lower : ∃ a : ℝ, 0 < a ∧ ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ β : ℝ, 0 < β → β < π / 2 →
    ∀ N₂ : ℕ, N₁ ≤ N₂ → Real.cos β / Real.sin β * N₂ ≤ 1 →
      a / (Real.cos β / Real.sin β) ^ 12 * (Real.log N₂ - Real.log N₁) ≤
        ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t)
```

## Choice of route

The three candidates from the brief were weighed as follows.

* **(b) A Dirichlet polynomial plus `MeanSquareFull`.** This does not close at `σ = 6`. The
  `L²` remainder `X^{−2y}(1+T)^{1+4y}` needs a length `X = T^α` with `α > 2`. But the
  Montgomery–Vaughan main term only gives a lower bound when `X ≪ T`. Letting `y → 0` with `T`
  makes the constants blow up like a power of `1/y`.
* **(a) Cauchy–Schwarz against a short Dirichlet polynomial.** This needs a contour shift of
  `L·D*` with horizontal-segment bounds. It is workable but longer.
* **(c) The Parseval/ray route.** This is the one used. The Ford-circle (Diophantine) counting
  suggested in `CRITICAL_MEAN_SQUARE.md` turned out to be unnecessary; see below.

## Proof

1. **Exact identity** (`CriticalMeanSquare.weighted_parseval`).
   `∫|Λ(6+it)|²e^{2βt}dt = 2π∫ e^{12u}|Δ(ie^{u+iβ})|² du`.
2. **Change of variables** (`RayBlock.integral_Ru_eq`). Substitute `w = sin β·e^u`. On
   `[log(a/s), log(b/s)]` the ray integral equals `s^{-12} ∫_a^b w¹¹ |Δ(−w+iκw)|² dw`, where
   `κ = cot β` and `s = sin β ≤ 1`. Integrability of the `u`-integrand comes from the majorant
   of `CriticalMeanSquare.Upper` (`integrable_Ru`).
3. **Horizontal periods** (`Ray.exists_Hh_lower`). Parseval on `Im τ = y` gives
   `H(y) := ∫_0^1|Δ(x+iy)|²dx = Σ τ(n)² e^{-4πny}`. This is `RankinSelberg.hasSum_tau_sq`.
   Keeping only `n ≤ ⌊1/y⌋` and using `Σ_{n≤N} τ(n)² ≥ kN¹²` (`RankinSelberg.exists_sum_tau_sq_ge`)
   gives `H(y) ≥ k'/y¹²` for `0 < y ≤ 1`.
4. **Vertical Lipschitz bound** (`Ray.exists_Dc_lip`). The Cauchy estimate on a disc of radius
   `y₀/2`, together with `|Δ(τ)| ≤ M (Im τ)^{-6}`, gives
   `|Δ(x+iy₁) − Δ(x+iy₂)| ≤ A|y₁−y₂|/y₀⁷` for `y₁, y₂ ≥ y₀`. The mean value theorem is applied
   along the vertical line.
5. **One block** (`RayBlock.block_lower`). On `w ∈ [N, N+1]` the ray rises only by `κ`. So
   `|Δ(−w+iκw)|² ≥ ½|Δ(−w+iκN)|² − (Aκ/(κN)⁷)²`, and the first term integrates over a full
   period to `½H(κN)` (`Ray.integral_period`). This gives
   `∫_N^{N+1} w¹¹|Δ(−w+iκw)|² ≥ (k'/2) κ^{-12}/N − A² κ^{-12}/N³` whenever `κN ≤ 1`.
   The error is scale-invariant, so no Diophantine input is needed.
6. **Summation** (`RayBlock.sum_lower`). For `N ≥ N₁`, where `kN₁² ≥ 4A²`, each block is at
   least `(k'/4)κ^{-12}/N`. Since `log(n+1) − log n ≤ 1/n`, the blocks sum to
   `≥ (k'/4) κ^{-12} (log N₂ − log N₁)`.
7. **Stirling weight** (`Weight.exists_weight_bound`). With `δ = π/2 − β`,
   `|Λ(6+it)|²e^{2βt} ≤ C_Γ(1+|t|)¹¹ e^{−2δ|t|}|L(6+it)|²`. This uses
   `Stirling.norm_Gamma_le_stirling`. The symmetry `|L(6−it)| = |L(6+it)|` comes from
   `HeckeZeros.tauL_conj`. The convexity bound `HeckeConvex.tauL_convexity` gives integrability.
   Then `Tail.lhs_le` uses `integral_comp_abs` to show
   `LHS ≤ 2C_Γ∫_0^∞(1+t)¹¹e^{−2δt}|L|²`.
8. **Dyadic tail** (`Tail.ioi_le`). Split at `T` and `2ʲT`. On each block apply
   `CriticalMeanSquare.dyadic_upper`, which gives `∫_X^{2X}|L|² ≤ C X(1+log X)`. The pure
   inequality `tail_num` then gives
   `∫_0^∞ ≤ (1+T)¹¹ J(T) + D e^{−2δT} T¹²(1+log T)`, where `J(T) = ∫_0^T |L|²`. The `j`-th block
   carries a factor `2^{−j}`. Passing to `∫_{Ioi 0}` uses `intervalIntegral_tendsto_integral_Ioi`.
9. **Bookkeeping** (`Lower`). Take `δ = K/T`, `β = π/2 − δ`, `κ = tan δ ∈ (0, 2δ]`
   (`cot_bounds`), and `N₂ = ⌊1/κ⌋ ≥ T/(4K)`. Then
   `a(T/2K)^{12}(log T − L₀) ≤ 2C_Γ[(1+T)¹¹J(T) + D e^{−2K}T¹²(1+log T)]`.
   Choose `K = 1 + log(Q/a + 1)` so that the tail is at most a quarter of the main term
   (`hsmall`). Then `final_arith` gives `J(T) ≥ a/(2K)^{12}/(2^{13}C_Γ) · T log T` for
   `T ≥ max(4KN₁, e^{4L₀+1})`.

The constant `c` is effective in principle but is not computed; it is far from Good's `2c`.

## Gaps and next steps

* **Weighted asymptotic.** The block argument is almost sharp. Replace the inequality
  `|a|² ≥ ½|b|² − |a−b|²` by `|a|² = |b|² + O(|b||a−b| + |a−b|²)`, and bound the cross term by
  Cauchy–Schwarz. The block error then becomes `O(κ^{-12}/N²)`, which is summable. The main
  term becomes `Σ_N N¹¹ H(κN)` with `y¹²H(y) → Γ(12)(4π)^{-12}·c` (Rankin's constant, by
  partial summation from `RankinExact`). You also need an upper bound for the blocks with
  `κN > 1` (cusp decay) and for `w < N₁` (by `Dc_S`, this is again a cusp region). Together
  these give `ray integral = c″ κ^{-12} log(1/κ) + O(κ^{-12})`, that is, the weighted
  asymptotic with Good's constant. Estimate: 400–600 lines. This is more concrete than the
  equidistribution route sketched in `CRITICAL_MEAN_SQUARE.md`.
* **Sharp asymptotic `~ 2cT log T`.** On top of the weighted asymptotic, this needs a
  Karamata-type Tauberian step for the kernel `t¹¹e^{−2δt}` with a logarithmic factor. It is
  not in Mathlib.

## Files

| file | content |
|---|---|
| `CriticalMeanSquareLower/Ray.lean` | `pt`, `Hh`, `hasSum_Hh`, `exists_Hh_lower`, `integral_period`, `exists_Dc_lip` |
| `CriticalMeanSquareLower/RayBlock.lean` | `Gw`, `block_lower`, `sum_lower`, `Ru`, `ray_point`, `Ru_eq`, `integral_Ru_eq`, `integrable_Ru`, `ray_lower` |
| `CriticalMeanSquareLower/Weight.lean` | `Lsq_neg`, `Lsq_abs`, `exists_weight_bound`, `integrable_major` |
| `CriticalMeanSquareLower/Tail.lean` | `Phi0`, `lhs_le`, `tail_num`, `ioi_le` |
| `CriticalMeanSquareLower/Lower.lean` | `cot_bounds`, `final_arith`, `critical_mean_square_lower`, `critical_mean_square_order`, `critical_mean_square_isTheta` |
| `CriticalMeanSquareLower/Main.lean` | imports, `#print axioms` |

Reused: `CriticalMeanSquare` (`weighted_parseval`, `dyadic_upper`, `critical_mean_square_upper`,
`norm_gS_six_le`, `min_le_maj`, `maj_le_seven`, `integrable_gS_six`, `Lsq`,
`setIntegral_Icc_eq_interval`), `RankinSelberg` (`hasSum_tau_sq`, `exists_sum_tau_sq_ge`),
`HardyZeros` (`Dc`, `Dc_add_one`, `Dc_of_im_pos`, `Dc_differentiableOn`), `HardyCountHafner`
(`exists_Delta_bound_exp`, `gS`, `Gs`, `Phis_eq_strip`), `Stirling.norm_Gamma_le_stirling`,
`HeckeConvex.tauL_convexity`, `HeckeZeros.tauL_conj`, `HeckeL.heckeLambda_eq_tauL`.

## Literature

- R. A. Rankin, Proc. Camb. Phil. Soc. 35 (1939): `Σ τ(n)²/n^{11} ~ cN`, and mean values on
  vertical lines.
- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29
  (1982) 278–295: `∫_0^T |L_f(k/2+it)|² = 2c_f T(log(T/2πe) + C) + O((T log T)^{2/3})`.
- J. L. Hafner, Math. Ann. 264 (1983): the Fourier/Plancherel set-up.
