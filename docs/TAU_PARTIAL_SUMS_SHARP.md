# Cancellation in `∑_{n≤x} τ(n)`: exponent `59/10 + ε` (unconditional)

Lean: `RamanujanTau/TauPartialSumsSharp/` (7 files, about 2450 lines, no `sorry`, no
`native_decide`, no new axiom). Build with
`nice -n 10 lake build RamanujanTau.TauPartialSumsSharp.Main` (exit 0). `#print axioms` on every
headline gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1).**

## 1. Statements

```lean
-- RamanujanTau.TauPartialSumsSharp
theorem tau_partial_sum_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((59 : ℝ) / 10 + ε)

theorem cuspForm_partial_sum_sharp (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ≤ C * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε)
```

`59/10 = 11/2 + 2/5`. This improves `TauPartialSums.tau_partial_sum_bound` (`181/30 = 11/2 + 8/15`)
by `x^{2/15}`, and the Rankin bound `∑|τ(n)| ≪ x^{13/2}` by `x^{3/5−ε}`. It holds for every
level-one cusp form of every weight. The classical `35/6 = 11/2 + 1/3` is **not** reached; see §3.

Reusable intermediate results (all level (1)):

```lean
theorem dual_rep (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 0 < x) :
    WC (coef f) r x = (I ^ k)⁻¹ * ((2 * π : ℂ) ^ k)⁻¹ *
      ∑' n : ℕ, coef f n / (n : ℂ) ^ (k + r) * Jc k r ((2 * (k : ℝ) - 3) / 4) (n * x)
theorem kernelZero_sharp (hk : 3 ≤ k) :
    ∃ C, ∀ y ≥ 1, ‖Jc k 0 (((k : ℝ) + 1) / 2) y‖ ≤ C * y ^ ((k : ℝ) / 2 - 1 / 4)
theorem bracket_signed (a : ℕ → ℂ) (r : ℕ) (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ‖(r! h^r) * A a x − DkC h r (WC a r) x‖ ≤ r! h^r * ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + r h⌋₊, ‖a n‖
theorem landau_ineq ...   -- abstract Landau inequality, complex coefficients and kernels
```

Here `WC a r x = ∑_{n≤x} aₙ(x−n)^r`,
`Q_j(s) = j!(2π)^{2s}Γ(k−s)/Γ(s+j+1)` and `J_j^{(σ)}(y) = (1/2π)∫ y^{σ+it+j}Q_j(σ+it) dt`.
`kernelZero_sharp` is the Bessel-size bound `J_0 ≍ y^{k/2}·y^{−1/4}`. It beats the phase-free
bound `y^{(k+1)/2}` by `y^{1/4}`.

## 2. Proof

Unnormalized: `a = coef f`, `b = (k+1)/2`.

1. **Exact dual expansion** (`Dual.lean`, `dual_rep`), for any order `r ≥ 2`.
   - Perron (`MeanSquare.perron_c`) on `Re s = k/2+1`.
   - Shift the holomorphic integrand `x^s P_r(s) L(f,s)` to `σ_m = (2k−3)/4`. The bound
     `‖L(f,s)‖ ≪ (1+|t|)^{3/2}` on the strip comes from `HeckeConvexGeneral.fC_bound`/`fL_line`.
   - On `σ_m`, the functional equation gives
     `P_r(s)L(f,s) = i^{−k}(2π)^{−k}Q_r(s)L(f,k−s)` (`Pk_fL_eq`), where `L(f,k−s)` converges
     absolutely.
   - Fubini.

   There are no residues: `L(f,s)` is entire, and the contour stays in `Re s > 0`.
2. **Kernels** (`Kernel.lean`).
   - The strip bound `‖Q_j(s)‖ ≤ K(1+|t|)^{k−1−2Re s−j}` is a single application of
     `RankinLandau.norm_Gamma_ratio_unif'`.
   - Also proved: the phase-free bound `norm_Jc_le`, the contour shift `Jc_shift`, the relation
     `J_{j+1}(u+v)−J_{j+1}(u) = (j+1)∫₀^v J_j` (`Jc_rel`, for all `j ≥ 0` on `Re s = b`), and
     continuity.
3. **Sharp bottom kernel** (`Phase.lean`, `Contour.lean`). This is a degree-two port of the
   `KernelPhase` bent contour.
   - Recursion: `Q_0(w+1)(k−1−w)(w+1) = 4π²Q_0(w)` (`Q_add_one`), hence
     `‖G(w+1)‖‖P(w)‖ = 4π²y‖G(w)‖`.
   - `P` is bounded below by `|P(w)| ≥ (Im w)²`, and above by
     `|P(w)| ≤ ((k−1−Re w)²+(Re w+1)²)/2 + (Im w)²` (AM–GM).
   - Parameters: `y = Y⁴`, `τ = 2πY²` (stationary height, `τ² = 4π²y`), `n = ⌈Y⌉`, `U = Y⁶`.
   - Contour pieces: `Re s = b−n` for `|t| ≤ τ`; `Re s = b+n` for `τ ≤ |t| ≤ U`; horizontals at
     `±τ` and `±U`; the original line for `|t| ≥ U`.
   - Every piece is `≪ Y^{2k−1} = y^{k/2−1/4}`. For `Y < k+3` the phase-free bound is used.
4. **Landau differencing, complex version** (`Core.lean`).
   - `DkC h r` is `Δ_h^r` for functions `ℝ → ℂ`.
   - The signed bracket: `‖r!h^rA(x) − Δ_h^rW_r(x)‖ ≤ r!h^r∑_{x<n≤x+rh}‖aₙ‖`. It is
     `RankinError.bracket` applied to each single coefficient `δ_n`.
   - `Δ_h^r` commutes with the dual series (`DkC_tsum_on`).
   - Head `n ≤ M`: `r` integrations down to `J_0` (`DkC_family_bound`, applied to the scaled
     family `J_j(n·)/n^j`, `scaled_rel`), giving `‖Δ^r J_r(n·)‖ ≤ r!h^r n^r sup‖J_0(n·)‖`.
   - Tail `n > M`: `2^r sup‖J_r‖`.
   - Rankin's trick with `γ = (k+1)/2 + ε/8` gives `landau_ineq`.
5. **Parameters** (`Main.lean`).
   - Bottom kernel: `β₀ = k/2 − 1/4`, from `kernelZero_sharp`.
   - Top kernel: `β_r = (k+r)/2 + ε/8`. This is the phase-free bound on `σ_t = (k−r)/2 + ε/8`,
     moved there by `Jc_shift`.
   - Choices: `h = x^{1/5}`, `M = x^{3/5+ε}`, `r = ⌈1/ε⌉ + 2`.
   - Short sums: `short_bound` (Cauchy–Schwarz with `RankinExact.rankinSelberg_exact_general`)
     gives `∑_{x<n≤x+rh}‖aₙ‖ ≪ h^{1/2}x^{(k−1)/2+3/10} = x^{(k−1)/2+2/5}`.
   - Exponents after normalizing by `(k−1)/2`:
     - head: `1/4 + (3/5+ε)(1/4+ε/8) ≤ 2/5 + ε`;
     - tail: `4/5 − ε(r−1)/2 + O(ε) ≤ 2/5 + ε` (`exps_ok`).

## 3. The arithmetic check (task items (a), (b))

Normalize `αₙ = aₙ n^{−(k−1)/2}`. Landau's method with Riesz order `r` gives, for any cut `M`:

- head (sharp bottom kernel): `x^{1/4}∑_{n≤M}|αₙ|n^{−3/4} ≍ x^{1/4}M^{1/4}`;
- tail (top kernel): `x^{(r+1)/2}M^{(1−r)/2}h^{−r}` with a sharp `J_r`. The phase-free `J_r` adds
  `x^{η}`, and the `r → ∞` limit removes that.

Optimizing `M` gives `D(h) = x^{1/2}h^{−1/2}` **for every `r`**. Higher Riesz order does not help.
The order only has to be large enough that the phase-free top kernel costs nothing.

- With Rankin–Selberg short sums `E(h) = h^{1/2}x^{3/10}`, balancing gives `h = x^{1/5}` and
  **`2/5`**. This is the optimum of the method with this input.
- Weil's pointwise bound gives `E = h x^{1/4+ε}`. Mixing it in does not help: at `h = x^{1/5}`
  the Rankin–Selberg bound is already smaller.
- The first-kernel route (head `x^{3/4}/h`, `J_1 ≪ y^{3/4}` normalized) gives only `9/20`.

`35/6` (i.e. `1/3`) needs either:

1. `E(h) ≪ h x^{ε}` at `h ≈ x^{1/3}`, a Deligne-strength short-interval bound; or
2. nontrivial cancellation in the head sum `∑_{n≤M} αₙ n^{−3/4} e(2√(nx))` (exponential-sum or
   spectral methods).

Neither is in the repository. An improvement of Rankin's `3/5` (for example Huang 2021,
`3/5 − 1/560`) would give `2/5 − δ/4` (corrected 2026-11-06; see [VORONOI_POINTWISE](VORONOI_POINTWISE.md) §2, which also proves `35/6` conditionally on `DeligneBound`). No shortcut was found that reaches `1/3` unconditionally
from the existing infrastructure.

I did not verify the literature attribution of an unconditional `x^{(k−1)/2+1/3}`. The previous
doc cites Walfisz (1933). The commonly cited proofs (Hafner–Ivić 1989) use Deligne.
`x^{k/2 − 1/10}` is the natural exponent of Landau's method with Rankin's mean value. It is
probably classical, but this was not checked against sources.

## 4. Files

| file | content | lines |
|---|---|---|
| `Kernel.lean` | `Q`, `Jc`, `Q_succ_mul`, `differentiableAt_Q`, `Q_bound`, `norm_Jc_le`, `Jc_shift`, `Jc_rel`, `continuousOn_Jc` | 339 |
| `Dual.lean` | `WC`, `tsum_phi_eq`, `fL_strip_bound'`, `Pk_fL_eq`, `integral_cpow_Q`, `dual_rep` | 352 |
| `Phase.lean` | `P2`, `Q_add_one`, `G0`, shift recursions, `StripB`, pointwise bounds on every piece, `left_pointwise` | 468 |
| `Contour.lean` | piece integrals, `integral_G0_le`, `kernelZero_sharp` | 465 |
| `Core.lean` | `DkC` and its lemmas, `DkC_family_bound`, `delta`, `W_delta`, `bracket_signed`, `scaled_rel`, `landau_ineq` | 474 |
| `Main.lean` | `short_bound`, `exps_ok`, `cuspForm_partial_sum_sharp(_aux)`, `tau_partial_sum_sharp`, `#print axioms` | 354 |

The generic helpers `KernelPhase.rect_diff`, `integral_symm_abs`, `integral_shift_pow_le` and
`integral_rpow_tail_le` are reused. So are `RankinError.bracket`/`W_rel`/`W_mono`,
`TauPartialSums.short_sq`/`A`, `MeanSquare.perron_c`, `Stirling.integral_line_eq_rpow` and
`HeckeConvexGeneral` (functional equation, convexity, summability).

## 5. Gaps

- The exponent has `+ε`. It has two sources: the phase-free top kernel, which needs `r ≍ 1/ε`,
  and Rankin's trick. Exact `x^{59/10}` is likely reachable with two further pieces:
  - the bent contour for `J_r` (as `RankinExact` did for degree 4);
  - exact partial summation (`RankinExact.Summation`).

  Not attempted.
- `35/6` is not reached (§3). That needs a stronger short-sum or exponential-sum input.
- The directory is not imported by `RamanujanTau.lean`. README, STATUS and RESULTS are not
  updated, per instructions.
