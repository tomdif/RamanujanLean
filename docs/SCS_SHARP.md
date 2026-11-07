# Sharpening the shifted-convolution bound: `SCS(1/22, 1/2)` and `δ = 1/231`

> **Update (2026-11-06):** sharpened to SCS(1/21, 1/21) and δ = 1/134 in `SCSSharp2.tauL_subconvex_sharp2`; see [SCS_SHARP2](SCS_SHARP2.md).

**Status (2026-11-06): DONE, evidence level 1 (Lean, axiom-clean, no hypotheses).**
Directory `RamanujanTau/SCSSharp/` (9 files, about 1.85k lines). It imports `SCSProof` and
`SubconvexityCond` and modifies neither.

    nice -n 10 lake build RamanujanTau.SCSSharp.Main      # exit 0

Every `#print axioms` in `SCSSharp/Main.lean` gives `[propext, Classical.choice, Quot.sound]`.
`grep` finds no `sorry`/`admit`/`native_decide`/`axiom` in `RamanujanTau/SCSSharp/`.

| | `η` | `B` | `δ`, old reduction `η/(10B+24)` | `δ`, new reduction `η/(5B+8)` |
|---|---|---|---|---|
| `SCSProof` (before) | `1/8000` | `8` | `1/832000` (proved) | `1/384000` (not stated) |
| **`SCSSharp`** | **`1/22`** | **`1/2`** | `1/638` (proved) | **`1/231`** (proved) |

Headlines (`RamanujanTau.SCSSharp`):

```lean
instance shiftedConvolutionBound_sharp : ShiftedConvolutionBound (1 / 22) (1 / 2)
--  |Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/22} h^{1/2}   for all h ≥ 1, N

theorem tauL_subconvex_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 231 : ℝ)

theorem tauL_subconvex_of_SCS' {η B : ℝ} [ShiftedConvolutionBound η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - η / (5 * B + 8))

theorem tauL_subconvex_sharp_oldReduction :   -- the same input through SubconvexityCond
    ∃ C, 0 ≤ C ∧ ∀ t, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 638 : ℝ)
```

## 1. Exponent bookkeeping (paper, all exponents as parameters)

Notation: `a_n = τ(n)τ(n+h)`, `G_h(W) = Σ a_n e^{−nW}`, trivially `|G_h(W)| ≪ (Re W)^{−12}`.
Write `σ = Re W`, `θ = 2 Im W/σ`, `A = |θ| + 3`, `Y = σ/4π`.

### 1a. Pointwise bound (`pointwise_par'` → `pointwise_G'`)

The two-point Poincaré argument of `docs/SCS_PROOF.md` §2 has these parameters: box size `ε`, the
Weil exponent `δ_W` (`|S(h,h;c)| ≪ h c^{1/2+δ_W}`), and a ball-measure exponent `m`
(`μ{w : Dh(z,w) ≤ R} ≪ R^m`). The ingredients are:

* `‖Ψ 1_{supp P}‖₂ ≤ M R⁶ (cR^m)^{1/2}` with `R = 2A²`;
* `‖P‖₂² ≪ h ε³ Y^{−3/2−2δ_W}`;
* `μ(I)μ(B) ≍ ε³/Y`;
* the prefactor `|Y(i − ζ̄₀)|¹² ≥ (YA/2)¹²`;
* the Lipschitz error of the horocycle coefficient over the box, `≪ (YA)¹² A ε Y^{−12}`.

Cauchy–Schwarz then gives

    Y¹² |G_h| ≪ A^{m} √h ε^{−3/2} Y^{1/4−δ_W}  +  A ε.

Optimizing in `ε = Y^e` gives `e = (1/4 − δ_W)·2/5` and

    |G_h(σ+iv)| ≪ √h · A^{a} · σ^{−12+s},   a = max(m,1),   s = (1 − 4δ_W)/10.

| | `SCSProof.pointwise_G` | `SCSSharp.pointwise_G'` |
|---|---|---|
| Cauchy–Schwarz | AM–GM `(λa + b/λ)/2`, so the Weil saving is not square-rooted cleanly | `√a √b` |
| ball measure | box `[−R,R]×[1/R,R]`: `4R⁴` (`m = 4`) | exact widths `2√(Ry)` against `dy/y²`: `4R` (`Ball.lean`, `m = 1`) |
| prefactor | `|Y(i−ζ̄₀)| ≥ 2Y` (the `A¹²` is lost) | `≥ YA/2`, which cancels `R⁶ = 64A¹²` |
| `θ`-loss `a` | `32` | **`1`** |
| `h`-loss | `h` | **`√h`** |
| saving `s` | `3/40` (`δ_W = 1/40`, `ε = Y^{1/10}/2`) | **`12/125`** (`δ_W = 1/100`, `ε = Y^{12/125}/2`) |

### 1b. Tauberian step (`laplace_rieszK`, `Rmean2_le`, `Rmean2_bound`)

The smoothed sum `R_k(x) = Σ a_n (1 − e^{(n−x)/L})₊^k` is computed by the kernel
`P_k(s) = k!/∏_{j≤k}(s+j)` on `Re s = σ₀ = L/x`, with `W = s/L` and `Re W = 1/x`. Then
`θ = 2y/σ₀`, and `|P_k(σ₀+iy)| ≤ k! 2^{k+1}/((σ₀+|y|)(1+|y|)^k)`. If `k ≥ a+1`:

    ∫ |P_k(σ₀+iy)| (2|y|/σ₀ + 3)^a dy ≪ σ₀^{−a},   so   |R_k(x)| ≪ √h x^{12−s} σ₀^{−a}.

(`SCSProof` used `k = 1` with the crude bound `(2/σ₀)²(1+|y|)^{−2}`, losing `σ₀^{−2}`, plus a
`Y₀`-split whose tail decays only like `Y₀^{−1/2}`.) `SCSSharp` uses `k = 2`, `a = 1`:
`|P₂|(|2y/σ₀|+3) ≤ 48 σ₀^{−1}(1+|y|)^{−2}` (`Pk2_mul_le`).

**Unsmoothing** (`Asum_bound_large'`). We have `0 ≤ 1 − (1−u)^k ≤ k u`, so the defect is
`≤ k Σ_{n<x} |a_n| e^{−(x−n)/L}`. Write `L = x^{1−κ}` and cut at `D = x^{1−κ+ι}`. The near range
costs `x^{11}(D + x^{3/5})` (Rankin short sums, `RankinExact`). The far range costs
`x^{12} e^{−x^ι} ≤ j! x^{12−jι}`. Hence

    η = min( s − aκ,  κ − ι,  jι,  2/5 )  →  sup = s/(a+1)   (ι → 0, j → ∞).

| | `a` | `s` | `s/(a+1)` | chosen `(κ, ι, j)` | `η` |
|---|---|---|---|---|---|
| `SCSProof` | 32 | 3/40 | 1/440, before its extra `σ₀^{−2}` and `Y₀`-split losses | `σ₀ = x^{−1/4000}` | `1/8000` |
| `SCSSharp` | 1 | 12/125 | 6/125 = 0.048 | `(1/20, 1/220, 10)` | **`1/22` = 0.04545** |

The check is `s − κ = 12/125 − 1/20 = 0.046 ≥ 1/22`, `κ − ι = 1/22` and `jι = 1/22`.

### 1c. Abel summation (`shiftSum_bound'`)

`λ(n)λ(n+h) = w(n) a_n` with `w(t) = t^{−11/2}(t+h)^{−11/2}` and `|w'| ≤ 11 t^{−13/2}(t+h)^{−11/2}`.
`SCSProof` fed the bound `|A(t)| ≪ h (t+h)^{12−η}` into all of `t ∈ [1,N]`, and lost
`((t+h)/t)^{13/2} ≤ (1+h)^{13/2}`, which gives `B = 8`. Now:

* For `t ≥ h`, `(t+h)/t ≤ 2`, so the contribution is `≪ √h t^{−η}`.
* For `t < h`, Cauchy–Schwarz with Rankin gives `|A(t)| ≤ A t⁶(t+h)⁶` (`Asum_cs`), so the
  contribution is `≪ t^{−1/2}(t+h)^{1/2} ≤ 2√h t^{−1/2}`, whose integral is `≪ √h N^{1/2}`.

So **`B = 1/2`**, the `h`-exponent of the pointwise bound.

### 1d. The reduction `SCS(η,B)` ⇒ subconvexity (`Reduction.lean`)

`SubconvexityCond` uses the window `H = T^{1−θ}`, length `X = T^{1+α}` and Gaussian cutoff
`ρ = T^r`. The off-diagonal term relative to `H` is `T^{(α+θ+r)(1+B) + θ + r − (1−θ−r)η}`. The
approximation `MeanSquare.approx_tauL` has error `X^{−1/2}T^{1+ε}`, which forces `α = 2δ + 2ε`.
The diagonal and logarithms force `θ > 2δ`. The optimum (`ε, r, θ − 2δ → 0`) is

    δ_max = η / (4B + 6).

`SubconvexityCond` took `ρ = T^{2δ}`, `X = T^{1+4δ}`, `H = T^{1−4δ}`, `ε = δ`, giving `η/(10B+24)`.
`Reduction.lean` takes `ρ = T^{δ/10}`, `X = T^{1+11δ/5}`, `H = T^{1−21δ/10}`, `ε = δ/10`. Then
the off-diagonal exponent is `(δ/5)(11η − 7 − 3B) ≤ 0` for `η ≤ 1/2`, which gives **`δ = η/(5B+8)`**.
With `(η,B) = (1/22, 1/2)` this is `1/231`; the old formula gives `1/638` and the method limit is
`1/176`. The reduction was cheap: it is a parameter-only copy of `Assembly`/`Final`, about 380
lines.

## 2. Files

| file | content |
|---|---|
| `Ball.lean` | `lintegral_ball_le'` (`μ{Dh ≤ R} ≤ 4R`), `lintegral_U_ball'` (`≤ 8R` on `U × ℍ`) |
| `NormQ.lean` | `norm_Q_le'` (Hölder with the sharp ball) |
| `Point.lean` | `norm_G0_le'` (prefactor `≥ (YA/2)¹²`), `pointwise_par'`, **`pointwise_G'`** |
| `RieszK.lean` | `laplace_rieszK` (Mellin inversion for `P_k`, all `k ≥ 1`) |
| `Rmean.lean` | `Pk2_mul_le`, `Rmean2_le`, `Rmean2_bound` (`≪ √h x^{12−1/22}`) |
| `Asum.lean` | `rankin_short'` (exponent `1−1/22`), `Asum_bound_large'` |
| `Final.lean` | `Asum_cs`, **`shiftSum_bound'`** |
| `Reduction.lean` | `subconvexDelta'`, `rpoly_bound'`, **`tauL_subconvex_of_SCS'`** |
| `Main.lean` | instance `shiftedConvolutionBound_sharp`, `tauL_subconvex_sharp`, `#print axioms` |

`SCSSharp` reuses from `SCSProof`: the Bruhat/Kloosterman `‖P‖²` bound (`norm_tsum_Iγ_le`), unfolding
(`two_Q_eq`, `Q_eq`, `main_term_le`), the Lipschitz bound `cf_sub_le`, `abs_laplace_le`,
`sum_aabs_le`, Abel-summation helpers (`wf`, `abs_wf'_le`, `shiftSum_eq_abel`), and
`RankinExact.rankinSelberg_exact`. From `SubconvexityCond` it reuses `mean_value_bound`,
`norm_sq_le_window`, `gBound_gX*`, `dpoly_bsm_eq` and `exp_poly_bound`.

## 3. What limits further progress

1. **Pointwise saving `s ≤ 1/10`.** This comes from indicator boxes with a first-order
   Lipschitz error `Aε` against the Weil term `ε^{−3/2}Y^{1/4}`. Two improvements are possible:
   * Averaging over a box symmetric about `ζ₀` (with a symmetric `y`-window) kills the linear
     Taylor term. That would give `ε²` and hence `s → 1/7`. It needs a second-order bound for `cf`
     (`Σ n²|a_n|e^{−nY}`), roughly 300 lines.
   * The Selberg/Weil exponent `1/4` would need a smooth test function with rapidly decaying
     Fourier transform, or the spectral expansion.
2. **The Tauberian loss `η ≤ s/(a+1)`.** With `a = 1` this halves the saving. `a = 0` would need a
   pointwise bound uniform in `θ = Im W/Re W`. Here `A^1` comes both from the ball measure
   `R^{1/2}·R⁶/A¹²` and from the Lipschitz error. A sector-adapted box (width `ε/A` in `Re ζ`)
   moves the loss but does not remove it: the term `ε^{−3/2}` becomes `(ε²·ε/A)^{−1/2}`.
3. **`B = 1/2`.** It comes from the uniform Kloosterman bound `|S(h,h;c)| ≤ A h c^{1/2+δ}`
   (`Kloost.lean`). The gcd form `(h,c)^{1/2} c^{1/2+δ}`, summed over `c ≤ 1/Y`, would give
   `B = δ_W` and then `δ → η/8 ≈ 1/176`.
4. **The reduction.**
   * `η/(5B+8)` against the method limit `η/(4B+6)`. Closing the gap needs `ε, r, θ−2δ` all tiny.
   * The method itself (Gaussian window, sharp SCS, Abel summation) is far from Good's
     `δ = 1/6`, which uses spectral large-sieve / mean-value input.
5. **Overall.** With all of the above at their limits (`s = 1/7`, `a = 1`, `B → 0`, `δ = η/6`),
   this route gives `η = 1/14` and `δ ≈ 1/84`. The literature exponent `|L(Δ,6+it)| ≪ t^{1/3+ε}`
   (Good 1982; cited from memory) is out of reach without spectral theory.

## 4. Evidence levels

* Level 1 (Lean, axiom-clean, unconditional): everything in §2.
* Level 3 (paper only): the limits in §3 (`s → 1/7`, `δ_max = η/(4B+6)`, gcd-Kloosterman `B → 0`).

Literature: Selberg (1965) and Good (1981–83) for shifted sums and `t^{1/3}`; Weil (1948) for
Kloosterman sums; Korevaar, *Tauberian Theory*, Ch. VII, for the real-Laplace obstruction
(`SCS_PROOF.md` §1).
