# Mean square of L(Δ, s) on the critical line Re s = 6

Module: `RamanujanTau/CriticalMeanSquare/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.CriticalMeanSquare.Main` (exit 0).

## Evidence levels

| result | level |
|---|---|
| `∫_0^T |L(Δ,6+it)|² ≪ T log T`, `∫_T^{2T} ≪ T log T` | **(1) Lean, axiom-clean** |
| exact weighted Parseval identity (ray integral of `|Δ|²`) | **(1) Lean, axiom-clean** |
| lower bound `≫ T log T`, asymptotic `~ c_Δ T log T` | (3) literature only (Rankin 1939, Good 1982) |
| constant `c_Δ = 2c ≈ 0.76817` | (3) heuristic derivation below + (4) numerics, T ≤ 400 |

`#print axioms` for every headline gives `[propext, Classical.choice, Quot.sound]`. There are
no named hypotheses, no `sorry`, no `native_decide` and no `axiom`.

## Headlines (`namespace RamanujanTau.CriticalMeanSquare`)

```lean
theorem critical_mean_square_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T

theorem dyadic_mean_square_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T

theorem dyadic_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * (1 + Real.log T)

theorem cumulative_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * (1 + Real.log T)

/-- weighted mean square of Λ(Δ,·) on the critical line = L² norm of Δ along a ray -/
theorem weighted_parseval {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) =
      2 * π * ∫ u : ℝ, ‖cexp (6 * ((u : ℂ) + β * I)) * Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2

/-- Plancherel for continuous integrable F with integrable Fourier transform -/
theorem parseval {F : ℝ → ℂ} (hc : Continuous F) (hi : Integrable F) (hFi : Integrable (𝓕 F)) :
    ∫ ξ, ‖𝓕 F ξ‖ ^ 2 = ∫ t, ‖F t‖ ^ 2
```

Here `tauL` is `L(Δ,s) = Σ τ(n) n^{-s}` (entire continuation), `heckeLambda` is
`Λ(s) = (2π)^{-s} Γ(s) L(s)`, and `Dc` is `Δ` extended by `0` off `ℍ`.

## Proof of the upper bound (`Upper.lean`)

This is the Hecke–Hafner Plancherel route of `HardyCountHafner.MeanSquare`, taken at `x = 0`.
Fix `T ≥ 1`, `β = π/2 − 1/T`, `c = cos β ≥ 2/(πT)`. By `HardyCountHafner.Fs_eq_fI`, which already
covers `σ = 6`,

    F(t) := Λ(6+it) e^{βt} = ∫ Φ_6(−2πξ+iβ) e^{−2πiξt} dξ,   Φ_6(w) = 2π e^{6w} Δ(ie^w).

1. **Evenness** (`Zs_six_neg`, `Phis_six_neg`). `Λ(12−s) = Λ(s)` gives `Φ_6(−w) = Φ_6(w)`.
   This plays the role of `Δ(−1/τ) = τ¹²Δ(τ)`, as the Gaps section of
   `HARDY_COUNT_HAFNER.md` suggests.
2. **Two cusp bounds** (`norm_gS_six_le`). `norm_Gs_le` applied at `(u, β)` and `(−u, −β)` gives
   `|Φ_6(u+iβ)| ≤ 2πMc^{−6} min(e^{−πce^{u}}, e^{−πce^{−u}})`.
3. **Majorant** (`maj`, `min_le_maj`). Write `L = log(1/c)`. Then
   `min(…) ≤ 1_{|u| ≤ L} + 3/(1+(u−L)²) + 3/(1+(u+L)²)`; the tails use `exp_tail_le`.
   The majorant is at most `7` (`maj_le_seven`), and its integral in `ξ` is
   `L/π + 3` (`integral_maj`).
4. **Schur test** (`HardyCountHafner.integral_tri_norm_fI_sq_le_gen`). It gives
   `∫_T^{2T} |F|² ≤ 14 (2πM c^{−6})² (L/π + 3)` (`mean_sq_Fs_six`).
5. **Stirling from below** (`HardyCountHafner.Fs_lower` at `x = 0`). On `[T, 2T]`,
   `|F(t)| ≥ c_H T^{11/2} |L(6+it)|`. Here `c^{−12} ≤ (πT/2)^{12}` and
   `L ≤ 1 + log T`, so the total is `T^{12}·log T / T^{11} = T log T` (`dyadic_upper`).

`Cumulative.lean` sums the dyadic pieces by induction on `n` with `T ≤ 2ⁿ`. This gives
`∫_1^T ≤ 2C T(1+log T)`, plus the constant `∫_0^1`.

## The exact identity (`Parseval.lean`)

`parseval` is Plancherel for `F ∈ L¹ ∩ C` with `𝓕F ∈ L¹`. It follows from Mathlib's
`VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip` with `M = innerSL ℂ`, together with
`Continuous.fourierInv_fourier_eq`; Mathlib's `L²` Plancherel is not needed. For
`F(t) = Λ(6+it)e^{βt}` we have `𝓕F(ξ) = Φ_6(2πξ+iβ)`, which is integrable by the majorant above
(`integrable_gS_six`). Substituting `u = 2πξ` gives `weighted_parseval`:

    ∫_ℝ |Λ(6+it)|² e^{2βt} dt = 2π ∫_ℝ e^{12u} |Δ(i e^{u+iβ})|² du.

The ray `τ = ie^{u+iβ}` is the Euclidean line `Im τ = cot(β)·|Re τ|`, `Re τ < 0`. Writing
`g(τ) = |Δ(τ)|² (Im τ)^{12}`, which is `SL₂(ℤ)`-invariant, and `κ = cos β`, the right side is
exactly `2π κ^{−12} ∫_0^∞ g(r e^{i(π/2+β)}) dr/r`. So the weighted critical mean square is a
**pure modular-surface problem**: it is the integral of `g` along a long closed-horocycle-like
path, of hyperbolic length `≈ 2 log(1/κ)`.

## The constant c_Δ (derivation; not formalized)

Let `c` be Rankin's constant: `Σ_{n≤N} τ(n)²/n^{11} = cN + O(N^{3/5})`, with
`c = (3/π)(4π)^{12}‖Δ‖²/11! = 0.384084054468…` (`RankinExact.rankinSelberg_exact`,
`docs/RANKIN_SELBERG.md`). Then

    ∫_0^T |L(Δ,6+it)|² dt ~ c_Δ T log T,   c_Δ = 2c = (6/π)(4π)^{12}‖Δ‖²/11! ≈ 0.768168.

There are two independent heuristics, and they agree.

* *Approximate functional equation.* `L(6+it) ≈ Σ_{n≤t/2π} a(n)n^{−1/2−it} + χ(t)·(dual sum)`,
  with `a(n) = τ(n)n^{−11/2}`. The two pieces have equal mean squares, and the cross terms are
  negligible. Since `Σ_{n≤x}|a(n)|²/n ~ c log x`, this gives `∫_0^T 2c log(t/2π) dt ~ 2c T log T`.
  This is Good's theorem (Mathematika 29, 1982): `∫_0^T|L_f(k/2+it)|² = 2c_f T(log T + O(1))`.
* *Parseval + equidistribution.* Put `β = π/2 − δ`. Stirling gives
  LHS `≈ (2π)^{−11} ∫ t^{11}e^{−2δt}|L|² ≈ (2π)^{−11} c_Δ 11! (2δ)^{−12} log(1/δ)`. If the long
  ray equidistributes on `SL₂(ℤ)\ℍ`, then RHS `≈ 2π δ^{−12}·2log(1/δ)·(3/π)‖Δ‖²`.
  Equating the two gives `c_Δ = 2(3/π)(4π)^{12}‖Δ‖²/11! = 2c`.

**Numerics (level 4).** PARI `lfunmf`, trapezoid rule with step `1/20`, script at
`scripts/critical_mean_square/ms.gp`.
The quantity `(∫_0^T|L|² − 2cT log(T/2πe))/T` is

| T | 50 | 100 | 200 | 300 | 400 |
|---|---|---|---|---|---|
| value | 1.578 | 1.592 | 1.607 | 1.633 | 1.546 |

It stays flat at about 1.6. A wrong leading constant, for example `c_Δ = c`, would make it drift
by `≈ 0.8` over this range. So the data support
`∫_0^T|L(6+it)|² = 2cT log T + O(T)`, with a secondary constant near `1.6 − 2c log(2πe) ≈ −0.58`.

## Gaps and what would finish the asymptotic

* **Lower bound `≫ T log T`.** This is not formalized. The cheapest Lean route seems to be the
  Parseval identity above, plus a lower bound for the ray integral of `g`. For that, one shows
  that the line `Im τ = κ|Re τ|` spends a positive proportion of its log-length
  (`≫ log(1/κ)`) outside the Ford horoballs of height `Y`, where `g ≥ δ_Y > 0`. That is a
  Diophantine counting argument. Then one converts from the weight `t^{11}e^{−2δt}` to `[0,T]`
  using the upper bound proved here, which controls `t ≪ T/K`, while `t ≫ KT` is exponentially
  damped. Estimate: 400–700 lines. A Dirichlet-polynomial / Cauchy–Schwarz route, which shifts
  `∫ L·D*` to `Re s = 7.5` using `HeckeConvex` and `RankinExact` partial sums, is comparable.
* **Weighted asymptotic.** This needs the equidistribution of the long ray, that is, the
  Rankin–Selberg unfolding along the ray as in Good's method. It is much heavier.
* **Sharp asymptotic from the weighted one.** This needs a Karamata-type Tauberian step for
  `t^{11}e^{−2δt}` weights with a `log` factor. It is standard, but it is not in Mathlib.

## Files

| file | content |
|---|---|
| `CriticalMeanSquare/Upper.lean` | `Zs_six_neg`, `Phis_six_neg`, `norm_gS_six_le`, `exp_tail_le`, `midI`, `maj`, `integrable_maj`, `integral_maj`, `maj_le_seven`, `min_le_maj`, `mean_sq_Fs_six`, `dyadic_upper` |
| `CriticalMeanSquare/Cumulative.lean` | `Lsq`, `cum_aux`, `cumulative_upper`, `critical_mean_square_upper`, `dyadic_mean_square_upper` |
| `CriticalMeanSquare/Parseval.lean` | `parseval`, `integrable_gS_six`, `weighted_parseval` |
| `CriticalMeanSquare/Main.lean` | headlines, `#print axioms` |

Reused: `HardyCountHafner` (`Fourier`: `Zs`, `Phis`, `Gs`, `Phis_eq_strip`, `Fs`, `gS`,
`fourier_Fs`, `Fs_eq_fI`, `integrable_Fs`; `MeanSquare`: `exists_Delta_bound_exp`,
`norm_Gs_le`, `exp_neg_le_three_div`, `integral_lorentz`, `integrable_lorentz`, `cH`,
`Fs_lower`; `Schur`: `integral_tri_norm_fI_sq_le_gen`), and
`HeckeL.heckeLambda_functional_equation`.

## Literature

- R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n)…*, Proc. Camb.
  Phil. Soc. 35 (1939): this gives `Σ τ(n)²/n^{11} ~ cN`, and mean-square bounds on the line.
- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29
  (1982) 278–295: `∫_0^T|L_f(k/2+it)|² = 2c_f T(log(T/2πe) + const) + O((T log T)^{2/3})`.
- J. L. Hafner, Math. Ann. 264 (1983): the Fourier/Plancherel set-up used here.
