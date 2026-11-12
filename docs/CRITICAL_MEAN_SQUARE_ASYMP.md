# Asymptotic mean square of L(Δ, s) on the critical line Re s = 6

> **Current status (2026-11-12).** The later [Good second-term theorem](GOOD_SECOND_TERM.md) proves the second term with error `O(T^{599/600})`. [GENERAL_CUSP_MOMENTS](GENERAL_CUSP_MOMENTS.md) extends the leading asymptotic to general level-one cusp forms under its stated hypotheses.
> Earlier gap lists below describe the original method or checkpoint.

Module: `RamanujanTau/CriticalMeanSquareAsymp/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.CriticalMeanSquareAsymp.Main` (exit 0).

## Evidence levels

| result | level |
|---|---|
| (A) `∫_0^T |L(Δ,6+it)|² dt ~ 2c · T log T`, with `c` Rankin's constant (Good 1982) | **(1) Lean, axiom-clean** |
| (B) `κ¹² ∫ |Λ(6+it)|² e^{2βt} dt / log(1/κ) → 12‖Δ‖²` as `κ = cot β → 0⁺` | **(1) Lean, axiom-clean** |
| (B′) `λ¹² ∫_0^∞ t¹¹ e^{−λt} |L(6+it)|² dt / log(1/λ) → (2π)¹¹ 2¹² · 12‖Δ‖²` | **(1) Lean, axiom-clean** |
| Karamata's theorem for Laplace transforms with a `log(1/t)` factor | **(1) Lean, axiom-clean** |
| `c_Δ = 2c ≈ 0.768168` numerically | (4) PARI, `scripts/critical_mean_square/ms.gp` (see `CRITICAL_MEAN_SQUARE.md`) |

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every headline. There are
no named hypotheses, no `sorry`, no `native_decide` and no `axiom`. The secondary term
(`O(T)`, Good's `2c T(log(T/2πe) + C)`) is **not** formalized.

## Headlines (`namespace RamanujanTau.CriticalMeanSquareAsymp`)

```lean
/-- Rankin's constant, exactly as in `RankinExact.rankinSelberg_exact`. -/
noncomputable def rankinC : ℝ :=
  3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ)
noncomputable def cDelta : ℝ := 2 * rankinC

/-- (A) Good's theorem for Δ. -/
theorem critical_mean_square_asymptotic :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2) / (T * Real.log T)) atTop
      (𝓝 cDelta)

theorem cDelta_eq : cDelta = 2 * (3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq /
    (Nat.factorial 11 : ℝ))

/-- normalization check against RankinExact: cDelta/2 is Rankin's c -/
theorem rankin_normalization : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - cDelta / 2 * N| ≤
      C * (N : ℝ) ^ ((3 : ℝ) / 5)

/-- (B) the weighted asymptotic, κ = cot β -/
theorem weighted_asymptotic :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ 12 *
      (∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t)) /
        Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
      (𝓝 (12 * EisensteinReal.petNormSq))

/-- (B′) Laplace form; Lap l = ∫ x in Ioi 0, x^11 * Lsq x * exp (-(x*l)) -/
theorem laplace_asymptotic :
    Tendsto (fun l : ℝ => l ^ 12 / Real.log (1 / l) * Lap l) (𝓝[>] 0) (𝓝 Kc)
-- Kc = (2π)^11 * (2^12 * (12 * petNormSq)),  Kc / 11! = cDelta  (Kc_div_eq)
```

`Lsq t = ‖tauL (6 + t*I)‖²`. `EisensteinReal.petNormSq` is the Petersson norm `‖Δ‖²` over the
standard fundamental domain, the same constant used in `RankinExact`.

## Proof

### 1. The ray integral (`Block`, `Harmonic`, `RayAsymp`, `Weighted`)

`weighted_parseval` gives `∫|Λ(6+it)|²e^{2βt}dt = 2π∫_ℝ Ru β`.

* **Evenness** (`Ru_even`). `Φ₆(−w) = Φ₆(w)` (`Phis_six_neg`), together with `Φ₆ = 2πG₆` on the
  strip, gives `Ru β (−u) = Ru (−β) u`. So `∫_ℝ Ru β = ∫_0^∞ Ru β + ∫_0^∞ Ru (−β)`
  (`integral_Ru_split`). `Ru (−β)` is the integrand along the mirror ray `τ = +w + iκw`. No
  conjugation symmetry of `Δ` is needed.
* **Change of variables** `w = sin β · e^u` on both rays (`Ru_eq_gen`, `integral_change`).
  The `u`-range `[0, log((n+1)/s)]` becomes `w ∈ [s, n+1]`, with `n = ⌊1/κ⌋`.
* **Sharp blocks** (`block_sharp`). Put `a = Δ(σw+iκw)` and `b = Δ(σw+iκN)`. Then
  `|a|, |b| ≤ M(κN)^{-6}`, and the Cauchy estimate (`exists_Dc_lip`) gives
  `|a−b| ≤ Aκ(κN)^{-7}`. From `||a|²−|b|²| ≤ |a−b|(|a|+|b|)` and
  `(N+1)¹¹ − N¹¹ ≤ 2047N¹⁰`:
  `|∫_N^{N+1} w¹¹|Δ(σw+iκw)|² − N¹¹H(κN)| ≤ B/(κ¹²N²)`.
  Summing gives `|κ¹²∫_1^{n+1} − ∑_{N≤n} A(κN)/N| ≤ 2B` uniformly in `n` (`sum_sharp`). Here
  `A(y) = y¹²H(y) = ∫₀¹|Δ(x+iy)|²y¹²dx` (`Aint_eq`).
* **Horocycle limit.** `A(y) → (3/π)‖Δ‖²` as `y → 0⁺`. This is Zagier's theorem, already in
  the repo as `EisensteinReal.Horo.tendsto_Aint_zagier`. Rankin's error term
  `O(N^{3/5})` is not needed.
* **Logarithmic averages** (`harm_tendsto`). If `0 ≤ h ≤ H₀` and `h → c₀` at `0⁺`, then
  `∑_{N≤⌊1/κ⌋} h(κN)/N / log(1/κ) → c₀`. The proof uses `log(m+1) ≤ H_m ≤ 1 + log m`.
* **Edges** (`ray_decomp`). The piece `w ∈ [s,1]` contributes `≤ M²κ^{-12}`, and the cusp tail
  `w ≥ n+1 ≥ 1/κ` contributes `≤ M²κ^{-12}s^{-12}`, using `|Δ|y⁶ ≤ Me^{−πy}`
  (`tail_bound`).
* Each ray therefore gives `κ¹²∫_0^∞ Ru / log(1/κ) → (3/π)‖Δ‖²` (`ray_tendsto`). Hence (B):
  `2π · 2 · (3/π)‖Δ‖² = 12‖Δ‖²`.

### 2. Exact Gamma weight (`Gamma`)

From `Γ(1+it)Γ(1−it) = πt/sinh(πt)` (reflection plus `Gamma_conj`) and `Γ(s+1) = sΓ(s)`:

    |Γ(6+it)|² = (1+t²)(4+t²)(9+t²)(16+t²)(25+t²) · πt/sinh(πt)      (norm_Gamma_six_sq)

For `t ≠ 0` this gives `|Λ(6+it)|²e^{2βt} = kΓ(t) e^{−(π−2β)t}|L(6+it)|²` (`weight_eq`), with
`kΓ(t) ≥ t¹¹/(2π)¹¹` (`kG_ge`) and `kΓ(t)(2π)¹¹/t¹¹ → 1` (`tendsto_kG_ratio`).

### 3. Laplace transform (`Laplace`)

Put `λ = π − 2β`. Then `W(β) = N(β) + ∫_0^∞ kΓ e^{−λt}|L|²`, where the left half-line part
satisfies `0 ≤ N(β) ≤ N(0) < ∞`. The cotangent is `κ = tan(λ/2)`, and `λ/κ → 2` (via
`Real.sinc`). With the sandwich `t¹¹/(2π)¹¹ ≤ kΓ ≤ (1+η)t¹¹/(2π)¹¹ + C_η 1_{t≤T_η}`
(`Lap_le_KGL`, `KGL_le`), this gives (B′) with `Kc = (2π)¹¹2¹²·12‖Δ‖²`.

### 4. Karamata with a slowly varying factor (`KarC`)

`KarHypC m ρ K` means: `m ≥ 0`, `∫_0^∞ m e^{−xt} < ∞`, and `t^ρ/log(1/t) · ∫ m e^{−xt} → K`.
Set `S_t(f) = ∫ m(x)e^{−xt}f(e^{−xt})`. The repo's discrete Karamata
(`EisensteinReal/Karamata.lean`) is redone for integrals, keeping its limit functional `Lam`
and its ramp/bump lemmas:

* for `x^j`, use `log(1/((j+1)t))/log(1/t) → 1` (`tendsto_log_ratio`, `convC_pow`);
* extend to polynomials, then to continuous functions by Weierstrass (`convC_of_continuous`);
* extend to the weighted step `gK·Q`, with `Q` continuous and `0 ≤ Q ≤ B` (`convC_gKQ`).

### 5. Sharp cutoff (`Final`)

Take `m(x) = x¹¹|L(6+ix)|²` and `Q_ε(e^{−u}) = max(u,ε)^{−11}` for `u ∈ [0,1]`. At `t = 1/T`:

    T¹¹(F(T) − F(εT)) ≤ S_{1/T}(gK·Q_ε) ≤ T¹¹F(T)        (SC_bounds)
    (1−ε)/11! ≤ Lam 12 (gK·Q_ε) ≤ 1/11!                   (Lam_gQ_bounds)

Together with the a-priori bound `F(εT) ≤ C εT log T` (`critical_mean_square_upper`), this gives
`|F(T)/(T log T) − Kc/11!| < e` for large `T`, where `Kc/11! = 2c` (`Kc_div_eq`).

## Constant

`c_Δ = 2c = (6/π)(4π)¹²‖Δ‖²/11! ≈ 0.768168`, where `‖Δ‖² ≈ 1.0353620568·10⁻⁶`. This is the
constant predicted in `CRITICAL_MEAN_SQUARE.md` and seen numerically there for `T ≤ 400`. The
same `2c` arises in two ways:

* the two mirror rays, which are the two cusp passages of the closed geodesic-like path;
* `|Γ(6+it)|² e^{πt} ~ 2π t¹¹` at `λ = 2δ`.

## Gaps

* The secondary term is not formalized. Good's `∫_0^T = 2cT(log(T/2πe) + C) + O((T log T)^{2/3})`
  would need an effective error in (B), and a Tauberian remainder theorem in place of Karamata.
  The block errors are already `O(κ^{-12})`; the missing piece is a rate for Zagier's horocycle
  limit `A(y) → (3/π)‖Δ‖²`, which `RankinExact`'s `N^{3/5}` would supply.
* Other weights `k` and other level-one cusp forms are not covered. The ray, Gamma and Karamata
  steps are uniform; `RankinSelbergGeneral.horocycle_tendsto` gives the horocycle limit for
  every `f`, but `weighted_parseval` is proved only for `Δ`.

## Files

| file | content |
|---|---|
| `Block.lean` | `Gsig`, `integral_period_sig`, `exists_Dc_bounds`, `block_sharp`, `Aint_eq`, `sum_sharp` |
| `Harmonic.lean` | `harm_sandwich`, `harm_tendsto` |
| `RayAsymp.lean` | `Ru_even`, `ray_point_neg`, `Ru_eq_gen`, `integral_change`, `tail_bound`, `ray_decomp`, `tendsto_cot`, `c0`, `ray_tendsto` |
| `Weighted.lean` | `integral_Ru_split`, `integrable_Ru_neg`, `weighted_asymptotic` |
| `Gamma.lean` | `norm_Gamma_one_add_sq`, `Pq`, `norm_Gamma_six_sq`, `kG`, `norm_heckeLambda_sq`, `weight_eq`, `kG_ge`, `kG_le`, `tendsto_kG_ratio` |
| `KarC.lean` | `KarHypC`, `SC`, `ConvC`, `tendsto_log_ratio`, `convC_pow`, `convC_poly`, `convC_of_sandwich`, `convC_of_continuous`, `convC_gKQ` |
| `Laplace.lean` | `fW`, `integrable_fW`, `Lap`, `KGL`, `W_split`, `N_bounds`, `Lap_le_KGL`, `KGL_le`, `weighted_lambda`, `Kc`, `laplace_asymptotic` |
| `Final.lean` | `mL`, `karHyp_mL`, `Qe`, `Lam_gQ_bounds`, `SC_bounds`, `rankinC`, `cDelta`, `Kc_div_eq`, `critical_mean_square_asymptotic`, `cDelta_eq`, `rankin_normalization` |
| `Main.lean` | imports, `#print axioms` |

Reused: `CriticalMeanSquare` (`weighted_parseval`, `Phis_six_neg`, `critical_mean_square_upper`,
`Lsq`), `CriticalMeanSquareLower` (`pt`, `Hh`, `integral_period`, `exists_Dc_lip`, `Ru`,
`ray_point`, `integrable_Ru`, `exists_weight_bound`, `integrable_major`),
`EisensteinReal.Horo.tendsto_Aint_zagier` (Zagier), `EisensteinReal.Karamata` (`Lam`, `gK`,
ramps, `Lam_bump_le`), `HardyCountHafner.Phis_eq_strip`, `HardyZeros.Dc_*`,
`RankinExact.rankinSelberg_exact` (normalization only).

## Literature

- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29
  (1982) 278–295.
- R. A. Rankin, Proc. Camb. Phil. Soc. 35 (1939).
- D. Zagier, *Eisenstein series and the Riemann zeta function* (1981): equidistribution of long
  horocycles.
- J. Karamata, *Neuer Beweis und Verallgemeinerung der Tauberschen Sätze…*, J. reine angew.
  Math. 164 (1931).
