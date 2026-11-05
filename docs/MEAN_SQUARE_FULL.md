# Carlson–Potter mean square of `L(Δ,s)` on the full range `σ > 6`

**Status: proved in Lean and axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`). There is
no `sorry`, no `native_decide`, and no named hypothesis. The work is in `RamanujanTau/MeanSquareFull/`,
built with `lake build RamanujanTau.MeanSquareFull.Main`.

```lean
theorem RamanujanTau.MeanSquareFull.mean_square_tauL_full {σ : ℝ} (hσ : 6 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))))
```

This is the classical theorem (Carlson 1922, Potter 1940) in the unnormalized coordinates, where the
critical line is `Re s = 6`. It extends `MeanSquare.mean_square_tauL`, which covered `σ > 37/6`.

## Why `37/6` was the barrier

`MeanSquare` approximated `L(Δ,σ+it)` pointwise by a Riesz-smoothed Dirichlet polynomial. The remainder
lives on a shifted line `Re = σ − δ`. There it was bounded by the pointwise convexity bound
`|L| ≪ |t|^{13/2−σ'+ε}`, which forces `x = σ − 6 > 1/6`.

## The bootstrap: functional equation plus `L²` control

Write `x = σ − 6`. Choose `y > 0`, set `δ = x + y` (so the shifted line is `Re = 6 − y`, left of the
critical line), and use a polynomial of length `X = T^α`.

1. **Exact identity** (`Identity.tauL_identity`). Perron (`perron_c`) and the contour shift
   (`shift_identity`) give

       λ_δ(X)·L(σ+it) − P_X(t) = −(1/2π) ∫ X^{−δ+iv} P₃(−δ+iv) L(σ−δ+i(t+v)) dv,

   with `λ_δ(X) = φ₃(1/X) − (1/2π)∫X^{−δ+iv}P₃(−δ+iv)dv`. This constant does not depend on `t`, and
   `λ_δ(X) → 1` (`tendsto_lam`). Moving the residue term `L(σ+it)·(…)` to the left removes every
   pointwise appearance of `L` on the line being studied.
2. **`L²` assembly** (`L2Assembly.mean_sq_of_L2approx`). Suppose `∫₀ᵀ|λ_T f − P_T|² ≤ B(T)·T` with
   `B → 0`, the diagonal sums tend to `S`, and the Montgomery–Vaughan error is `o(T)`. Then
   `(1/T)∫₀ᵀ|f|² → S`. The proof uses the pointwise inequality
   `|‖u‖²−‖v‖²| ≤ (1+1/η)‖u−v‖² + η‖v‖²` with `η = √(B⁺+1/T)`.
3. **Functional equation with uniform Stirling** (`LeftLine.norm_tauL_left_le`). For `0 ≤ y ≤ 1/2`,

       |L(6−y+iu)| ≤ 6e¹⁰ (1+|u|)^{2y} |L(6+y+iu)|.

   This comes from `L(s) = (2π)^{2s−12} Γ(12−s)/Γ(s) L(12−s)`, with `12 − s = s̄ + 2y` and
   `Stirling.norm_Gamma_add_le_one`. The `t ↦ −t` symmetry comes from `HeckeZeros.tauL_conj`.
4. **Mean square on the left line** (`LeftLine.left_line_mean_bound`). If `∫₀ᵁ|L(6+y+iu)|² ≤ C(1+U)`,
   then `∫_{−U}^{U}|L(6−y+iu)|² ≤ 2(6e¹⁰)²C(1+U)^{1+4y}`.
5. **`L²` remainder** (`Remainder.L2_remainder`). Use the weighted Cauchy–Schwarz inequality
   `(∫wG)² ≤ (∫w)(∫wG²)` with weight `w = (1+|v|)^{−4}`. Then apply Fubini on `[0,T]×ℝ`. The
   integrability needed for Fubini comes from the convexity bound `|L(6−y+iu)| ≪ 1+|u|`. Finally use
   the translation bound `∫₀ᵀ g(t+v)² ≤ ∫_{−(T+|v|)}^{T+|v|} g²`. Together these give

       ∫₀ᵀ|λf − P|² ≪ X^{−2δ} (1+T)^{1+4y}.

6. **One step** (`Step.step_core`). The remainder is `o(T)` when `4y < 2α(x+y)`. The off-diagonal error
   `log T · T^{α(1+η−2x)}` is `o(T)` when `α(1+η−2x) < 1`. `exists_params` shows that such `α, η` exist
   exactly when `y < x(1+4y)`, that is, when `x > y/(1+4y)`.
7. **Induction** (`Main.mean_square_tauL_range`). Set `y_n = 1/(6+4n)`, so `y_0 = 1/6` and
   `y_{n+1} = y_n/(1+4y_n)`. The claim for `σ > 6 + y_n` is proved by induction on `n`:
   * The base case `n = 0` is `mean_square_tauL` (`σ > 37/6`).
   * In the inductive step, take `6 + y_{n+1} < σ ≤ 37/6`. Choose `y = y_n + min(m/2, 1/12)`, where
     `m = x(1+4y_n) − y_n > 0`. Then `y_n < y ≤ 1/4` and `y < x(1+4y)`.
   * The induction hypothesis on `Re s = 6+y` gives `∫₀ᵁ ≤ C(1+U)` (`bound_of_tendsto`), and
     `step_core` concludes.

   Since `y_n → 0`, every `σ > 6` is reached (`mean_square_tauL_full`).

## Files

| file | content |
|---|---|
| `MeanSquareFull/L2Assembly.lean` | `norm_sq_sub_norm_sq_le`, `mean_sq_of_L2approx` |
| `MeanSquareFull/LeftLine.lean` | `norm_tauL_neg`, `norm_tauL_left_le`, `bound_of_tendsto`, `left_line_mean_bound` |
| `MeanSquareFull/Remainder.lean` | weight `wt`, `cs_weighted`, `L2_remainder` (Fubini) |
| `MeanSquareFull/Identity.lean` | `IX`, `lam`, `Ig`, `tendsto_lam`, `tauL_identity`, `norm_Ig_le` |
| `MeanSquareFull/Step.lean` | `step_core`, `exists_params` |
| `MeanSquareFull/Main.lean` | `yth`, `mean_square_tauL_range`, `mean_square_tauL_full`, `summable_mean_square_limit_full` |

The proof reuses `MeanSquare` (`mv_poly` through `poly_mean_tendsto`, `perron_c`, `shift_identity`,
`bsm`, `sum_bsm_eq_tsum`, `sum_tau_sq_rpow_le`), `HeckeConvex` (`tauL_convexity_strip`,
`twelve_sub_eq_conj_add`), `HeckeL` (the functional equation), `HeckeZeros.tauL_conj`, and
`Stirling.norm_Gamma_add_le_one`.

## Remarks

* The approximate functional equation is not needed. The functional equation is only used to obtain
  an upper bound for the mean square on the reflected line, and that bound enters only through `L²`.
* The same scheme should apply to any degree-2 `L`-function that has a convexity bound and
  Rankin–Selberg control `∑_{n≤N}|a_n|² ≪ N^{k}`.
