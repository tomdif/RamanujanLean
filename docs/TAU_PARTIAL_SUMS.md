# Cancellation in `∑_{n≤x} τ(n)`: exponent `181/30 + ε` (unconditional)

Lean: `RamanujanTau/TauPartialSums/` (3 files, 562 lines, no `sorry`, no `native_decide`, no new
axiom). Build with `nice -n 10 lake build RamanujanTau.TauPartialSums.Main` (exit 0).
`#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
**Evidence level (1).**

## 1. Statements

```lean
-- RamanujanTau.TauPartialSums
theorem tau_partial_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((181 : ℝ) / 30 + ε)

theorem cuspForm_partial_sum_bound (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ≤ C * x ^ (((k : ℝ) - 1) / 2 + 8 / 15 + ε)
```

`181/30 = 11/2 + 8/15 ≈ 6.0333`. Compare the Rankin/Cauchy–Schwarz bound
`∑_{n≤x}|τ(n)| ≪ x^{13/2}` (`HeckeConvex.exists_sum_abs_tau_le`). The new bound saves
`x^{7/15−ε}`. The general statement holds for every level-one cusp form of every weight
(`coef f n` is the `n`-th q-coefficient). For `k < 12` it is trivial because `f = 0`.

**This is not the classical `35/6 = 11/2 + 1/3`.** §3 explains why that exponent is out of reach
without a Deligne-strength input on short sums.

## 2. Proof

Everything is unnormalized. `a = coef f`, `F = fL f` (entire), `β = k − 1`.

1. **Perron, order 1** (`Riesz.lean`, `riesz_one_bound`). `MeanSquare.perron_c` (complex
   coefficients) on `Re s = k/2 + 1` gives
   `2π ∑ aₙ(1−n/x)₊ = ∫ x^s P₁(s) L(f,s)` with `P₁(s) = 1/(s(s+1))`.
2. **Contour shift without residues.** The integrand `x^s P₁(s) F(s)` is holomorphic on
   `Re s > 0`. It is moved to `σ₁ = (k−1)/2 + 2ε` with `Stirling.integral_line_eq_rpow`.
   The strip bound `‖F(s)‖ ≤ K(1+|t|)^{1−ε}` on `σ₁ ≤ Re s ≤ k/2+1` is `fL_strip_bound`
   (`Main.lean`). It is assembled from three facts:
   - the Phragmén–Lindelöf bound `HeckeConvexGeneral.fC_bound`;
   - `fL_line`, which gives `‖L(f,s)‖ ≤ 2e¹⁰C‖s/2‖^{(k+1)/2+ε−σ}`;
   - `fL_bounded_of_gt` for `Re s ≥ (k+1)/2 + ε`.

   The result is `F₁(x) := ∑_{n≤x} aₙ(x−n) = O(x^{(k+1)/2+2ε})` (`F1_bound`, with `tsum_phi_eq`).
3. **One difference** (`Differencing.lean`). Write `A(x) = ∑_{n≤x} aₙ`. For `h ≥ 0`,
   `F₁(x+h) − F₁(x) = hA(x) + ∑_{x<n≤x+h} aₙ(x+h−n)` (`F1_diff`), so
   `h‖A(x)‖ ≤ ‖F₁(x+h)‖ + ‖F₁(x)‖ + h∑_{x<n≤x+h}‖aₙ‖` (`main_ineq`).
4. **Short sums without Deligne** (`short_sq`). Cauchy–Schwarz and Rankin's theorem with the
   exact error `O(N^{3/5})` (`RankinExact.rankinSelberg_exact_general`) give
   `(∑_{N<n≤M}‖aₙ‖)² ≤ (M−N)·M^β·(|c|(M−N) + 2C M^{3/5})`.
   For `h ≤ x^{3/5}` this is `∑_{x<n≤x+h}‖aₙ‖ ≪ x^{β/2} h^{1/2} x^{3/10}`.
5. **Choice of `h`** (`partial_sum_bound`). Take `h = x^{7/15}`. Then
   - `x^{β/2+1+2ε}/h = x^{β/2+8/15+2ε}`;
   - `x^{β/2}h^{1/2}x^{3/10} = x^{β/2+8/15}`.

   Finally `ε ↦ min(ε/2, 1/4)` (`cuspForm_partial_sum_bound_aux` → `cuspForm_partial_sum_bound`),
   and `f = Δ` with `coef_discriminant` gives `tau_partial_sum_bound`.

## 3. Why `35/6` is not reached

Normalize `aₙ = τ(n)n^{−11/2}`, so the target is `∑_{n≤x} aₙ ≪ x^{1/3}`. Landau's method trades a
dual-sum term `D(h)` against a short-interval term `E(h) = ∑_{x<n≤x+h}|aₙ|`. The table gives the
exponent of `x` in the resulting bound for each route. `E(h) = h^{1/2}x^{3/10}` is the
Rankin–Selberg + Cauchy–Schwarz bound (used here). `E(h) = h·x^{ε}` would need Deligne in the form
`|τ(n)| ≤ d(n)n^{11/2}`.

| route (`D(h)`) | `E(h) = h^{1/2}x^{3/10}` (unconditional) | `E(h) = h·x^{ε}` (Deligne) |
|---|---|---|
| no dual sum, Riesz order 1 + convexity (`D = x^{1+ε}/h`), **this file** | **8/15** | 1/2 |
| dual sum, bottom kernel `J₁ ≪ y^{3/4}` (`D = x^{3/4}/h`) | 9/20 | 3/8 |
| dual sum, bottom kernel `J₀ ≪ y^{1/4}` (`D = x^{1/2}h^{−1/2}`), Landau/Walfisz | 2/5 | **1/3** |

- **The classical `x^{35/6}`.** This needs both the Voronoi/Bessel analysis of the dual sum and
  short sums `∑_{x<n≤x+h}|τ(n)| ≪ h x^{11/2+ε}` for `h ≈ x^{1/3}`.
- **The short-sum input is the bottleneck.** Rankin–Selberg only controls `∑|aₙ|²` on intervals
  of length `≥ x^{3/5}`. The repo's best pointwise bound, `τ(n) ≪ n^{23/4+ε}` (Weil), gives
  `E = h x^{1/4+ε}`, which is worse here.
- **What a dual-sum route would buy.** Even with a full dual-sum formalization for `L(Δ,s)`, the
  unconditional exponent would improve only to `11/2 + 2/5 = 59/10`. That route needs four pieces:
  - the degree-2 analogue of `RankinLandau.dual_rep`;
  - the bent-contour kernel bounds of `KernelPhase`/`RankinExact`, using
    `Q_j(s+1)(11−s)(s+j+1) = 4π²Q_j(s)`;
  - a signed-coefficient Landau core;
  - for `2/5`, the conditionally convergent `J₀`.

  This is estimated at 2000–3000 lines and was **not attempted**.

The exponent `8/15` is the optimum of the route used here. With Riesz order `k` and the
functional-equation bound `|L(σ+it)| ≍ |t|^{12−2σ}` below `σ = 11/2`, the exponent is
`3/10 + (k/2+1/5)/(2k+1)`, which is minimized at `k = 1`. Order `k = 1` cannot leave the
convexity strip, because it needs `σ > 11/2` for integrability.

## 4. Files

| file | content | lines |
|---|---|---|
| `Riesz.lean` | `riesz_one_bound` (Perron + residue-free shift), `F1`, `tsum_phi_eq`, `F1_bound` | 153 |
| `Differencing.lean` | `A`, `F1_diff`, `norm_tail_term`, `main_ineq`, `short_sq`, `partial_sum_bound` | 229 |
| `Main.lean` | `fL_strip_bound`, `cuspForm_partial_sum_bound(_aux)`, `tau_partial_sum_bound`, `exponent_lt`, `#print axioms` | 180 |

## 5. Gaps

- The exponent is `181/30 + ε`, not `35/6`. See §3. **Update (2026-11-05):** improved to `59/10 + ε` in [TAU_PARTIAL_SUMS_SHARP](TAU_PARTIAL_SUMS_SHARP.md).
- The `ε` comes from the convexity bound (`fC_bound` degenerates as `ε → 0`).
- Not attempted:
  - a conditional version under a Deligne-type short-sum hypothesis (this route would give
    `11/2 + 1/2 + ε`);
  - the degree-2 dual expansion.
- The directory is not imported by the root `RamanujanTau.lean`. README, STATUS and RESULTS are not
  updated, per instructions.

## 6. Literature

- **Landau's method.** Landau (1915/1924), and Chandrasekharan–Narasimhan, Ann. of Math. 76
  (1962).
- **The exponent `(k−1)/2 + 1/3`.** For partial sums of cusp-form coefficients it is classical:
  Walfisz (1933) and Hafner–Ivić, Enseign. Math. 35 (1989). The latter removes the `ε` and gains a
  log power.
- **The input used here.** The proof uses only Hecke's functional equation, convexity,
  Phragmén–Lindelöf and Rankin's `O(N^{3/5})`.
