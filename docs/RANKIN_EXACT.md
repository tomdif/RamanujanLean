# Rankin's theorem exactly: error `O(N^{3/5})`, no `ε`

Lean: `RamanujanTau/RankinExact/` (8 files, about 2000 lines, no `sorry`, no new axiom).
Build with `nice -n 10 lake build RamanujanTau.RankinExact.Main`.

**Result.** For `τ`, and for every level-one cusp form of any weight, the Rankin–Selberg
partial sums satisfy `|∑_{n≤N} |a(n)|²/n^{k−1} − cN| ≤ C N^{3/5}`, with Rankin's exponent
(1939) exactly. This improves `RankinLandau`/`KernelPhase`, which give `N^{1−δ}` for every
`δ < 2/5`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every
headline (evidence level (1)).

## 1. Statements

```lean
-- RamanujanTau.RankinExact
theorem kernel_sharp (hm : 1 ≤ m) (r : ℕ) :
    ∃ C, ∀ y ≥ 1, ‖Jc m (r + 1) (1 / 2) y‖ ≤ C * y ^ (((9 + 6 * r : ℕ) : ℝ) / 8)
theorem landau_sharp (H : LandauHyp b k J c d A σ α ε) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hσ1 : σ ≤ -1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hμ : 0 ≤ μ)
    (h1 : 1 + α + μ * α ≤ 2 * θ) (h2 : k + σ + μ * σ ≤ (k + 1) * θ) :
    ∃ C, ∀ X ≥ 1, |W b 0 X - c * X| ≤ C * X ^ θ
theorem landau_exact_of_RSDataM (hm : 2 ≤ m) … (d : RSDataM m a κ) (habs : …) :
    ∃ C, ∀ N ≥ 1, |∑_{n∈Icc 1 N} a n - κ * rsConstM m * N| ≤ C * N ^ (3/5)
theorem rankinSelberg_exact_general (f : CuspForm 𝒮ℒ k) :      -- every k, no hypothesis
    ∃ C, ∀ N ≥ 1, |∑_{n≤N} coeffSq f n / n^(k−1) − rsConst f · N| ≤ C · N^(3/5)
theorem rankinSelberg_exact :
    ∃ C, ∀ N ≥ 1, |∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C · N^(3/5)
```

## 2. The sharp top kernel: `J_j(y) ≪ y^{3j/4+3/8}`

**Heuristic exponent.** `|Q_j(σ+it)| ≍ |t|^{1−4σ−j}`, the phase has second derivative
`≍ 4/t`, and the saddle is at `|t| = T ≍ y^{1/4}`. Stationary phase gives
`y^{σ+j}·T^{1−4σ−j}·√T = y^{3j/4+3/8}`. This is `(A−1)/(2A) + j(A−1)/A` for degree `A = 4`.
For `j = 1` the exponent is `9/8`, matching `kernelOne_sharp`.

**Proof.** The proof reuses the `KernelPhase` bent contour unchanged and generalizes every
estimate from `j = 1` to `j = r+1`. Notation: `y = Y⁸`, `τ = 2πY²`, `n = ⌈Y⌉`, `U = Y⁸`.

- **Shift (`Shift.lean`).** `‖G_j(w+1)‖‖P_j(w)‖ = 16π⁴y‖G_j(w)‖` with
  `P_j(w) = (−w)(m−w)(w+j+1)(w+m)` (`Qk_add_one` was already general in `j`). Two bounds
  control `P_j`:
  - lower: `‖P_j‖ ≥ |Im w|⁴`;
  - upper: `‖P_j‖ ≤ (‖w+c‖²+c²)(‖w‖²+m²)`, with `c = (j+1)/2`.

  For left shifts this gives the factor `B = (K+j+1)²+m²+t²`.
- **Strip input.** `Qk_bound_sharp` was already stated for general `j`:
  `‖Q_j(s)‖ ≤ K(1+|t|)^{1−4Re s−j}` on `|Re s| ≤ 1/2`.
- **Pointwise bounds (`Bounds.lean`).**
  - On `Re s = 1/2`: `K Y^{12+8r}(1+|t|)^{−(r+2)}`.
  - At height `±τ`: `64K Y^{8+6r}` (times `e^{D}`, `D = (r+4)²+m²`, on the left half).
  - At height `±U`: `4KY^{28}` before the shift and `64π⁴KY⁴` after it. This is independent
    of `r`, because `(1+U)^{−r} ≤ Y^{−8r}` cancels `Y^{8r}`.
- **Pieces (`Pieces.lean`).** Every piece is `≪ Y^{9+6r}`:

  | piece | bound |
  |---|---|
  | tail `\|t\| ≥ U` | `K Y⁸ ∫(1+\|t\|)^{−3/2}` |
  | left line | `2K(2^{r+1}e^{D/2π} + 2π(5+2r)!)Y^{9+6r}` |
  | right lines | `K Y^{9+6r}` |
  | horizontals at `±τ` | `128K e^{D} Y^{9+6r}` and `128K Y^{9+6r}` |
  | horizontals at `±U` | `128π⁴K Y^{9+6r}` |

- **Contour and small `y` (`Contour.lean`).** Cauchy is applied on three rectangles
  (`rect_diff`), giving `integral_Gj_le` and `kernel_sharp`. For `Y < D` the phase-free
  `norm_Jc_le` is enough.

## 3. The ε-free Landau core

The `ε` in `RankinLandau.landau_core` comes from Rankin's trick
`n^{α−1} ≤ M^{α+ε}n^{−1−ε}`. With sharp kernels at `θ = μ = 3/5` both constraints are
*equalities*, so any `ε > 0` breaks them.

`Core.lean` and `Summation.lean` replace the trick by exact partial summation:

- **`linear_bound`.** `∑_{n≤N} bₙ ≤ LN`. This is bootstrapped from `landau_core` itself at
  `θ = 1`, `μ = 0`, where there is room for `ε`.
- **`majorize`.** Abel summation as an induction: for nonincreasing `w ≥ 0`,
  `∑ bₙwₙ ≤ L∑wₙ`.
- **`sum_wS_le` and `sum_vT_le`.** These telescope by Bernoulli's inequality:
  - `∑_{n≤M} n^{α−1} ≤ M^α/α`;
  - `∑_{n>M} n^{σ−1} ≤ ∑ max(n, ⌊M⌋+1)^{σ−1} ≤ (1+1/|σ|)M^σ` (for `σ ≤ −1`).
- **`landau_sharp`.** This is `landau_core` with these two exact sums in place of the
  `ε`-weighted one.

## 4. Parameters (`Final.lean`)

- `k = 18`: the minimum allowed by `dual_rep`. Any `k` works, since the bookkeeping is an
  identity in `k`.
- `α = 1/8`: from `J₁ ≪ y^{9/8}`.
- `σ = −33/8`: from `J₁₈ ≪ y^{111/8}`.
- `θ = μ = 3/5`.

The two constraints then hold with equality:

- `1 + α + μα = 1 + 1/8 + 3/40 = 6/5 = 2θ`;
- `k + σ + μσ = 18 − 33/8 − 99/40 = 57/5 = 19·3/5 = (k+1)θ`.

In general, with `σ_k = (3−2k)/8`, the second constraint is `3(k+1)/5 = (k+1)·3/5` for every
`k`. This is Landau's `x^{(A−1)/(A+1)}` for `A = 4`. Finally, `mobius_transfer` with
`δ = 2/5` (it needs `δ < 1/2`) moves the result from `b = χ*a` back to `a`. The
`ε = 1/8` still present in `LandauHyp` is used only for summability and the bootstrap. It
does not enter the exponent.

## 5. Files

| file | content | lines |
|---|---|---|
| `Shift.lean` | `Gj`, `norm_Gj_add_one`, `norm_Pk_le_gen`, `norm_Gj_add_nat_le`, `norm_Gj_sub_nat_le`, `differentiableAt_Gj` | 158 |
| `Bounds.lean` | `StripBoundJ`, `Dc`, the pointwise bounds `bound_*J`, `factor_leJ`, `left_pointwiseJ` | 415 |
| `Pieces.lean` | `piece_*J` (tail, left, right top/bot, the horizontals) | 351 |
| `Contour.lean` | `integral_Gj_le`, `kernel_sharp` | 143 |
| `Summation.lean` | `majorize`, `bern_conc`, `bern_conv`, `wS`, `wL`, `vT`, `sum_wS_le`, `sum_vT_le` | 212 |
| `Core.lean` | `linear_bound`, `term_bound'`, `Dk_W_bound'`, `sumS_le`, `sumL_le`, `landau_sharp` | 385 |
| `Final.lean` | `landau_exact_of_RSDataM` | 214 |
| `Main.lean` | `landau_exact_RSFn`, `rankinSelberg_exact_general`, `rankinSelberg_exact`, `#print axioms` | 107 |

## 6. Gaps

- None for the stated theorems.
- `RankinExact.Main` is included in the root import graph and the [result catalog](RESULTS.md).
- The constant `C` is not explicit: it comes from `∃` statements such as `Qk_bound_sharp` and
  `landau_core`.
- Not attempted:
  - a better exponent than `3/5` (that would need exponent-pair or spectral methods);
  - levels other than one.
