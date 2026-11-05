# Mean values of `L(Δ,s)`: the Carlson–Potter theorem for `σ > 37/6`

Module: `RamanujanTau/MeanSquare/` (8 files, about 1600 lines). Entry point `MeanSquare/Main.lean`.
It is not imported by the root `RamanujanTau.lean`. Build it with
`lake build RamanujanTau.MeanSquare.Main`.

Coordinates are unnormalized: `tauL` is the entire continuation of `∑ τ(n) n^{-s}`
(`HeckeL/Main.lean`). The critical line is `Re s = 6`, and the series converges absolutely for
`Re s > 13/2`.

## Headline (evidence level 1: Lean, axiom-clean)

```lean
theorem RamanujanTau.MeanSquare.mean_square_tauL {σ : ℝ} (hσ : 37 / 6 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))))
```

This combines two cases:

* `mean_square_abs` (`σ > 13/2`, `AbsConv.lean`);
* `mean_square_strip` (`37/6 < σ ≤ 13/2`, `Strip.lean`).

`summable_mean_square_limit` shows the limit converges for every `σ > 6`.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for `mean_square_tauL`,
`mean_square_abs`, `mean_square_strip`, `summable_mean_square_limit`, `mv_poly`, `approx_tauL`,
`shift_identity`, `perron_c` and `mean_sq_of_approx`. There is no `sorry`, no `native_decide` and no
new axiom. No named hypotheses remain.

## What is proved, and what is not

* **Proved: `σ > 37/6 ≈ 6.1667`.** The classical theorem (Carlson 1922; H. S. A. Potter, *The mean
  values of certain Dirichlet series I*, Proc. LMS 1940) holds for every `σ > 6`.
* **Gap: `6 < σ ≤ 37/6`.** The method below stops exactly at `37/6`.
  **Update (2026-11-05): closed.** `MeanSquareFull.mean_square_tauL_full` proves the full range
  `σ > 6` by the functional-equation bootstrap sketched below; see [MEAN_SQUARE_FULL](MEAN_SQUARE_FULL.md).

## Proof architecture

| file | content |
|---|---|
| `Poly.lean` | `mv_poly`: `|∫₀ᵀ|∑_{n≤N} bₙ n^{-it}|² − T∑|bₙ|²| ≤ 6 H_N ∑ n|bₙ|²`, with `H_N = ∑_{d≤N} 1/d ≤ 1 + log N` |
| `Assembly.lean` | `mean_sq_of_approx`: suppose `sup_{[0,T]}|f − P_T| → 0`, `∑|b_T(n)|² → S` and `H·∑ n|b_T(n)|²/T → 0`. Then `(1/T)∫₀ᵀ|f|² → S` |
| `Sums.lean` | `summable_tau_sq` (`∑ τ² n^{-β}` converges for `β > 12`); `sum_tau_sq_rpow_le` (`∑_{n≤N} τ² n^{-γ} ≤ N^{β−γ} RS(β)`) |
| `AbsConv.lean` | case `σ > 13/2`: partial sums of length `⌊T⌋`, error is the tail |
| `Shift.lean` | `perron_c` (Riesz-smoothed Perron formula with complex coefficients); `shift_identity` (contour shift past the pole at `w = 0`) |
| `Approx.lean` | `approx_tauL`: `|L(Δ,σ+it) − ∑_{n≤X} τ(n)(1−n/X)³ n^{-σ-it}| ≤ C X^{-δ}(1+|t|)^{13/2−σ+δ+ε}` |
| `Strip.lean` | case `37/6 < σ ≤ 13/2`, with `X = T^{3/2}` |

**Mean value theorem for Dirichlet polynomials (`mv_poly`).**
1. Expand `|P|²`. The diagonal terms give `T∑|bₙ|²`.
2. Each off-diagonal term is bounded by `2|b_m b_n|/|log n − log m|`.
3. Use `1/|log n − log m| ≤ 1 + min(m,n)/|n−m|`, which follows from `log x ≥ 1 − 1/x`.
4. Apply Cauchy–Schwarz: `(∑|bₙ|)² ≤ H_N ∑ n|bₙ|²`.
5. Use `|b_m b_n| min(m,n) ≤ (m|b_m|² + n|b_n|²)/2` and `∑_{n≠m} 1/|n−m| ≤ 2H_N`.

This is the Montgomery–Vaughan theorem with an extra `log N` factor.

**Smoothed approximation (`approx_tauL`).**
1. Fix `s = σ + it` with `6 ≤ σ ≤ 13/2`.
2. Apply Mellin inversion of the Riesz kernel `φ₃(u) = (1−u)₊³`, whose Mellin transform is
   `P₃(w) = 6/(w(w+1)(w+2)(w+3))`. On the line `Re w = c = 7 − σ` this gives
   `2π ∑ τ(n)n^{-s}φ₃(n/X) = ∫ X^w P₃(w) L(Δ,s+w)`.
3. Remove the pole at `w = 0` by hand. Set `h(w) = X^w · 6/((w+1)(w+2)(w+3)) · dslope(L(Δ,s+·),0)(w)`. It is
   holomorphic on `Re w > −1` and equals `X^w P₃(w)(L(Δ,s+w) − L(Δ,s))` off `0`.
4. Shift `h` from `Re w = c` to `Re w = −δ` using `Stirling.integral_line_eq_rpow`. In the strip,
   `|L(Δ,z)| ≪ (1+|Im z|)²` for `5 ≤ Re z ≤ 7` (from `HeckeConvex.tauL_line` with `ε = 1/2`), and
   compactness handles `|Im w| ≤ 1`.
5. On `Re w = −δ`, `Re(s+w) = σ−δ ∈ [11/2, 13/2]`, so `HeckeConvex.tauL_convexity_strip` gives
   `|L| ≪ (1+|t|)^θ(1+|v|)^θ` with `θ = 13/2 − σ + δ + ε`. This is integrable against
   `|P₃| ≪ (1+|v|)^{-4}`.
6. Collect the terms. The pole term is `L(Δ,s)φ₃(1/X)`, and `1 − φ₃(1/X) ≤ 3/X`. The left-line
   integrals are `≪ X^{-δ}(1+|t|)^θ`.

**Exponents (`Strip.lean`).** Write `x = σ − 6` and `g = x − 1/6 > 0`. Take `δ = 7/12 + x/2`,
`ε = g/2` and `X = T^{3/2}`. Then:

* `σ − δ ≥ 11/2`, `δ < 1` and `θ = 1`.
* The approximation error is `≪ T^{1 − 3δ/2}`, and `1 − 3δ/2 = 1/8 − 3x/4 < 0`.
* The polynomial error is `H_X ∑ n|bₙ|² ≪ (1 + log T)·X^{13+g/2−2σ} = (1 + log T)·T^p`, with
  `p = 11/8 − 9x/4 < 1`.

Both conditions reduce to `x > 1/6`, that is `σ > 37/6`.

## Why the method stops at `37/6`

Use the convexity bound pointwise on the shifted line `Re = σ − δ ≥ 11/2`, and the
Dirichlet-polynomial mean value for length `X`. The two constraints are:

* `X^{-δ} T^{13/2−σ+δ} → 0`;
* `X^{13−2σ} = o(T)`.

Both can hold only if `13 − 2σ < σ − 11/2`, that is `σ > 37/6`. Moving the line to the left of
`11/2` with the functional equation makes the pointwise exponent worse.

## Route to the full range `σ > 6` (not done)

One route is to bootstrap with the functional equation. Suppose `∫₀ᵀ|L(Δ,6+y+it)|² ≪ T` is
already known for `y > y₀`. Then `L(Δ,σ'+it) ≍ |t|^{12−2σ'} L(Δ,12−σ'+it)` gives
`∫₀ᵀ|L(Δ,6−y+it)|² ≪ T^{1+4y}`.

Feed this mean-square bound into the remainder by Cauchy–Schwarz in `v`, in place of the pointwise
convexity bound. This proves the theorem for `x > y₀/(1+4y₀)`. Iterating from `y₀ = 1/6` gives
`1/10, 1/14, 1/18, …`, which tends to `0`. Each step would need:

* the functional equation with uniform Stirling bounds for `Γ(12−s)/Γ(s)` on vertical lines;
* a mean-square (not limit) version of `mean_sq_of_approx`;
* an induction on the range.

The classical alternative is an approximate functional equation, with two Dirichlet polynomials of length `≍ |t|`,
combined with the full Montgomery–Vaughan theorem.

## Literature

* F. Carlson, *Contributions à la théorie des séries de Dirichlet*, Ark. Mat. 16 (1922).
* H. S. A. Potter, *The mean values of certain Dirichlet series I*, Proc. London Math. Soc. (2)
  46 (1940), 467–478.
* H. L. Montgomery, R. C. Vaughan, *Hilbert's inequality*, J. London Math. Soc. (2) 8 (1974).
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §7.9 and §9.51 (Carlson's theorem).
