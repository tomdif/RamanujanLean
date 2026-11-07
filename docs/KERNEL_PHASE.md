# `KernelOneBound` proved: the first dual kernel is `≪ y^{9/8}`

Lean: `RamanujanTau/KernelPhase/` (5 files, about 1360 lines, no `sorry`). Build with
`nice -n 10 lake build RamanujanTau.KernelPhase.Main`.

**Result.** `KernelOneBound m` holds for every `m ≥ 1`, and the bound is sharp: there is no
`η` loss. So `rankinSelberg_landau` (every `δ < 2/5`, for `τ`) and its general cusp-form
version are now **unconditional**. `#print axioms` for every headline gives
`[propext, Classical.choice, Quot.sound]`.

## 1. Statements

```lean
-- RamanujanTau.KernelPhase
theorem kernelOne_sharp (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Jc m 1 (1 / 2) y‖ ≤ C * y ^ ((9 : ℝ) / 8)
theorem kernelOneBound (hm : 1 ≤ m) : KernelOneBound m
theorem rankinSelberg_landau_uncond {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C, ∀ N ≥ 1, |∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1−δ}
theorem rankinSelberg_landau_61_100_uncond : … ≤ C N^{61/100}
theorem rankinSelberg_landau_general_uncond (hk : 2 ≤ k) (f : CuspForm 𝒮ℒ k) … (every δ < 2/5)
```

## 2. Why no Stirling phase is needed (route (b): a bent contour)

Write `G(s) = y^{s+1}Q_1(s)`, so that `J_1(y) = (1/2π)∫ G(1/2+it) dt`.

**The exact real shift.** From `Γ(z+1) = zΓ(z)`:

    Q_j(w+1)·P(w) = 16π⁴·Q_j(w),     P(w) = (−w)(m−w)(w+j+1)(w+m)

(`Qk_add_one`). Taking norms gives `‖G(w+1)‖·‖P(w)‖ = 16π⁴y·‖G(w)‖`. Two elementary
inequalities then control `‖G‖` at any distance from the strip `|Re s| ≤ 1/2`:

- `‖P(w)‖ ≥ |Im w|⁴`;
- `‖P(w)‖ ≤ (‖w+1‖²+1)(‖w‖²+m²)`.

This uses only the modulus. It needs no `log Γ` asymptotics and no phase.

**Parameters.** Let `Y = y^{1/8}`, `τ = 2πY²` (so `τ⁴ = 16π⁴y`, the stationary height),
`n = ⌈Y⌉ ≍ √τ` and `U = Y⁸`.

**The contour.**

- Keep `Re s = 1/2` for `|t| ≥ U`.
- Move to `Re s = 1/2 − n` for `|t| ≤ τ`.
- Move to `Re s = 1/2 + n` for `τ ≤ |t| ≤ U`.
- Join these by horizontal segments at `t = ±τ` and `t = ±U`.

This is a discretised steepest-descent path. Near the saddle `s₀ = 1/2 + iτ`,
`log|G(s₀+a+ib)| ≈ −4ab/τ`. The path therefore leaves the saddle through the quadrants
`ab > 0`, where the modulus decays, and stays on them.

**Piece bounds.** Each piece is `≪ Y⁹ = y^{9/8}` (`Pieces.lean`).

| piece | pointwise bound used | contribution |
|---|---|---|
| tail `\|t\| ≥ U` on `Re = 1/2` | `KY¹²(1+\|t\|)^{−2}` | `≪ Y⁸` |
| left line `Re = 1/2−n`, `\|t\| ≤ τ` | `KY¹²(1+\|t\|)^{−2}·ρ^{2n}`, with `ρ = ((n+1)²+m²+t²)/τ²` | `≪ Y¹²/(τn) + Y¹⁴e^{−Y} ≪ Y⁹` |
| right lines `Re = 1/2+n`, `τ ≤ \|t\| ≤ U` | `KY¹²τ^{−2}(τ/\|t\|)^{4n}` | `≪ Y¹²/(τn) ≪ Y⁹` |
| horizontals at `±τ` (length `2n`) | `‖G‖ ≤ 64KY⁸·e^{9+m²}` (`\|P\| ≥ τ⁴` to the right, a bounded product to the left) | `≪ nY⁸ ≪ Y⁹` |
| horizontals at `±U` | `≤ 64π⁴KY⁴` | `≪ Y⁵` |

The only Γ input is `Qk_bound_sharp`: `‖Q_1(s)‖ ≤ K(1+|t|)^{−4Re s}` on `−1/2 ≤ Re s ≤ 1/2`.
This is the existing `Qk_bound` proof, with the exponent kept as `1 − 4 Re s − j` instead of
being weakened to the strip's lower end. The integer shifts then transport this bound to
every point of the contour. Cauchy's theorem is applied on three finite rectangles
(`rect_diff`, a difference form of Mathlib's `integral_boundary_rect_eq_zero_of_differentiableOn`).
`Q_1` is holomorphic off the real axis (`differentiableAt_Qk_of_im_ne`), and this covers the
right rectangles, which contain the poles' abscissae `Re s ≥ 1` but none of the poles.

**Small y.** For `Y < 9 + m²` the phase-free bound `norm_Jc_le` (`≪ y^{3/2}`) is enough.

**Why this beats the "1/3 obstruction".** As I understand it, that obstruction concerns moving
the whole line to another fixed vertical line, with modulus-only bounds. The bent contour uses a different abscissa on either side of
the stationary height, at a distance `≍ √τ` that grows with `y`. The exact recursion makes
growing distances cost nothing.

## 3. Files

| file | content | lines |
|---|---|---|
| `Shift.lean` | `Pk`, `Qk_add_one`, `G`, `norm_G_add_one`, `norm_G_add_nat_le`, `norm_G_sub_nat_le`, `differentiableAt_Qk_of_im_ne`, `differentiableAt_G`, `Qk_bound_sharp` | 346 |
| `Bounds.lean` | `StripBound`, pointwise bounds on every piece (`bound_tau_left/right`, `bound_U`, `bound_left_line`, `bound_right_line`, `left_pointwise`) | 374 |
| `Pieces.lean` | `rect_diff`, `integral_symm_abs`, `integral_shift_pow_le`, `integral_rpow_tail_le`, `piece_tail/left/right_top/right_bot/h_left/h_right/h_top` | 418 |
| `Contour.lean` | `integral_G_le`, `kernelOne_sharp`, `kernelOneBound` | 158 |
| `Main.lean` | unconditional headlines and `#print axioms` | 65 |

## 4. Evidence levels

- **(1) Lean, axiom-clean:**
  - everything in `KernelPhase/`, including `kernelOneBound`;
  - `rankinSelberg_landau_uncond`, `rankinSelberg_landau_61_100_uncond` and
    `rankinSelberg_landau_general_uncond`, which state Rankin–Selberg with error `O(N^{1−δ})`
    for every `δ < 2/5`.
- `docs/RANKIN_LANDAU.md` §4 still lists `KernelOneBound` as level (3)+(4). It is now (1).
  The doc was not edited, per instructions.

## 5. What remains

- **`δ = 2/5` exactly.** This needs `J_k ≪ y^{k+(2−k)/4}` with the phase for the top kernel
  (§5 of `RANKIN_LANDAU.md`). The same bent-contour method probably handles `J_k` too, since
  its saddle is at the same height, but this has not been attempted.
- **`m = 0`.** It is not covered (`Qk_bound` assumes `m ≥ 1`), but it is irrelevant here,
  because every nonzero level-one cusp form has `k ≥ 12`.
