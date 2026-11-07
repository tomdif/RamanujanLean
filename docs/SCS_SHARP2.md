# SCSSharp2: pushing `δ` in `|L(Δ,6+it)| ≪ (1+|t|)^{1/2−δ}` beyond `1/231`

**Status (2026-11-06): DONE for (3)+(4)+δ_W-retune, evidence level 1 (Lean, axiom-clean, no hypotheses).**
`SCS(1/21, 1/21)` and **`δ = 1/134`** (was `SCS(1/22, 1/2)`, `δ = 1/231`). The box improvement (1)
is paper-only (§4), with a corrected analysis: the useful version is a *sheared* box, not a symmetric one.

    nice -n 10 lake build RamanujanTau.SCSSharp2.Main      # exit 0

Every `#print axioms` in `SCSSharp2/Main.lean` gives `[propext, Classical.choice, Quot.sound]`;
`grep` finds no `sorry`/`admit`/`native_decide`/`axiom` in `RamanujanTau/SCSSharp2/`.
Directory `RamanujanTau/SCSSharp2/`; imports `SCSSharp`, `SCSProof`, `SubconvexityCond`, modifies none.

Starting point (`SCSSharp`, see `SCS_SHARP.md`): `SCS(η,B) = SCS(1/22, 1/2)`, reduction
`δ = η/(5B+8)`, so `δ = 1/231`.

## 1. Where `B = 1/2` comes from and how to remove it (limit (3))

`B` is the `h`-exponent of the pointwise bound `|G_h(W)| ≪ h^b A σ^{−12+s}`, carried unchanged
through the Tauberian step and Abel summation. `b = 1/2` because `‖P‖² ≪ h ε³ Y^{−3/2−2δ_W}`
used the uniform Kloosterman bound `|S(h,h;c)| ≪ h c^{1/2+δ_W}`.

* **gcd Kloosterman.** The proof of `SCSProof.norm_kloosterman_hh_le` already gives
  `|S(h,h;c)| ≤ g·|S(h',h';c')| ≤ A g c'^{1/2+δ}` with `g = (h,c)`, `c = gc'`. Since
  `g c'^{1/2+δ} = g^{1/2−δ} c^{1/2+δ} ≤ g^{1/2} c^{1/2+δ}`, we get
  `|S(h,h;c)| ≤ A (h,c)^{1/2} c^{1/2+δ}` for free.
* **Summing over `c ≤ K ≍ 1/Y`.** `(h,c)^{1/2} ≤ Σ_{d|h, d|c} d^{1/2}`; swapping,
  `Σ_{c≤K} (h,c)^{1/2} c^{1/2+δ}/c ≤ K^{1/2+δ} Σ_{d|h} d^{1/2} Σ_{c'≤K} 1/(dc')
  ≤ τ(h) K^{1/2+δ}(1+log K)`.
* **Divisor bound** `τ(h) ≤ C_β h^β` (not in Mathlib; standard proof prime by prime:
  `e+1 ≤ (p^e)^β` once `p ≥ 2^{1/β}`, and `e+1 ≤ (1+1/(β log 2)) 2^{eβ}` always).

Result: `‖P‖² ≪ h^{β} ε³ Y^{−3/2−2δ_W}`, hence `|G_h(W)| ≪ h^{β/2} A σ^{−12+s}`, same `s`.
We take `β = 1/11`, so the pointwise `h`-exponent is `b = 1/22`.

**Abel summation, range `t < h`.** There `SCSSharp` used `|A(t)| ≤ A t⁶(t+h)⁶`, giving the
integrand `≪ t^{−1/2}(t+h)^{1/2}` and `≪ √h N^{1/2}` — another `B = 1/2`. Write instead
`(t+h)^{1/2} ≤ (2h)^{η}(N+h)^{1/2−η}` (as `t + h ≤ 2h` and `t + h ≤ N + h`); then the integral is
`≪ h^{η} (N+h)^{1/2−η} N^{1/2} ≤ h^{η}(N+h)^{1−η}`. The boundary term at `N < h` is handled the
same way (`N^{1/2} ≤ h^{1/2} ≤ h^η (N+h)^{1/2−η}`).

**`B ≥ η` is forced** by the formulation: for `N < h` the true size of the sum is `≍ N` (no
cancellation is available from the method, since the pointwise bound needs `hσ ≤ 1`), and
`N ≤ C(N+h)^{1−η}h^{B}` at `N ≍ h` needs `B ≥ η`. So the target is `B = max(b, η) = η = 1/22`.

Target: **`SCS(1/22, 1/22)`**.

## 2. The reduction (limit (4)), redone with a free parameter

`SubconvexityCond`/`SCSSharp.Reduction` choose `ρ = T^{r}`, `X = T^{1+α}`, `H = T^{1−θ}` and the
approximation exponent `ε`. Constraints (all in the existing proof):

* approximation error `X^{−1/2}T^{1+ε} = T^{1/2−δ}` ⇒ `α = 2δ + 2ε`;
* diagonal + logarithms cost `T^{c·(small)}`, absorbed if `θ ≥ 2δ + (that small)`;
* Gaussian tail: `ρ = T^{r}`, any `r > 0` (constant `M1` depends on `r`);
* off-diagonal: `T^{(α+θ+r)(1+B) + θ + r − (1−θ−r)η} ≤ 1`.

Take `ε = r = uδ`, `θ = 2δ + uδ` (logs/diagonal cost `T^{3uδ/4}`). Then `α+θ+r = 4δ(1+u)`,
`θ + r = 2δ(1+u)`, `1 − θ − r = 1 − 2δ(1+u)`, and the off-diagonal exponent is

    δ(1+u)(4 + 4B + 2) − η + 2δ(1+u)η = δ(1+u)(4B + 6 + 2η) − η.

So **`δ = η / ((1+u)(4B + 6 + 2η))`** for any `0 < u ≤ 1` (the `2η` is the cost of
`(H/ρ)^{−η}` with `H < T`; the doc's earlier "limit `η/(4B+6)`" drops it). `SCSSharp` is the case
`u = 1/10` rounded up to `5B+8`.

## 3. Target exponents

| step | `η` | `B` | reduction | `δ` |
|---|---|---|---|---|
| `SCSSharp` | 1/22 | 1/2 | `η/(5B+8)` | 1/231 |
| (3) gcd Kloosterman + Abel fix | 1/22 | 1/22 | `η/(5B+8)` | 1/180.9 (`(1/22)/(5/22+8) = 1/181`) |
| (3) + (4) new reduction, `u = 1/69` | 1/22 | 1/22 | `η/((1+u)(4B+6+2η))` | **1/140** |
| (4) at `u → 0` | 1/22 | 1/22 | | 1/138 |
| **+ `δ_W = 1/400` (`s = 99/1000`), `(κ,ι,j) = (2/39, 1/273, 13)`, `u = 1/66`** | **1/21** | **1/21** | same | **1/134** (proved) |
| `δ_W → 0`, `ι → 0` (limit of this step) | → 1/20 | → 1/20 | `u → 0` | → 1/126 |
| sheared box, first order (§4, paper) | → 1/14 | → 1/14 | | → 1/90 |
| sheared box, second order (§4, paper) | → 1/11 | → 1/11 | | → 1/72 |

Tauberian check for `η = 1/21`: `s − κ = 99/1000 − 2/39 = 0.04772 ≥ 1/21 = 0.04762`,
`κ − ι = 2/39 − 1/273 = 1/21`, `jι = 13/273 = 1/21`; in Lean this is
`11901/1000 + 2/39 = 466139/39000 ≤ 12 − 1/21`. Pointwise: `t = Y^{1/1000}`, `ε = t⁹⁹/2`,
`Y^{−3/2−2/400} = t^{−1505}`.

Check for the headline: `4B + 6 + 2η = 6 + 6/22 = 138/22`, so `η/(4B+6+2η) = 1/138`, and
`(1/138)·(69/70) = 1/140`.

## 4. The box (limit (1)) — paper analysis (evidence level 3)

The pointwise error budget is `Y¹²|G_h| ≪ A h^{b} ε^{−3/2} Y^{1/4−δ_W} + E(ε)` for the box
`[Y, Y(1+ε)] × {|Re ζ − θ| ≤ ε, |Im ζ − 1| ≤ ε}`, `A = |θ|+3`.

* **First order (formalized):** `E = A ε`. The `A` comes from the `y`-direction:
  `W = 2πy(1 + iζ̄)` moves radially by `ε|W| ≍ εYA` when `y` moves by `εY`. Optimum
  `ε = Y^{1/10}` (independent of `A`), `s = 1/10`, `θ`-loss `a = 1`, `η → s/2 = 1/20`.
* **Symmetric box (as suggested in `SCS_SHARP.md` §3.1): does not help by itself.** It kills the
  linear Taylor term up to the asymmetry of `dy/y²`, `dμ(ζ)` (relative `ε`), but the quadratic term
  is `(Aε)²` (the second `y`-derivative carries `A²`). Then `s = 1/7` but `a = 2`, and
  `η = s/(a+1) = 1/21`: no gain over first order. The `SCS_SHARP.md` ceiling `δ ≈ 1/84`
  (which combined `s = 1/7` with `a = 1`) is therefore **not** what the symmetric box gives.
* **What does help: a sheared box.** The diagonal horocycle coefficient of
  `Ψ(z,w) = (z − w̄)¹²Δ(z)conj Δ(w)` is
  `(−t + i s)¹² e^{−2πh Im z} G_h(2π(s + it))` with `s = Im z + Im w`, `t = Re w − Re z`:
  apart from the harmless `e^{−2πh y}` (variation `≤ 2πhYε ≤ ε`), **it depends only on `(s, t)`**.
  Take the box `y ∈ [Y, Y(1+ε)]`, `s ∈ [s₀, s₀(1+ε)]`, `|t − t₀| ≤ εs₀` (`s₀ = 2Y`, `t₀ = Yθ`).
  Its measure is still `≍ ε³/Y`, it lies in `Dh ≤ R ≍ A²` once `εA ≤ 1`, and in `ζ`-coordinates it
  is a parallelogram of width `≍ εA` in `Re ζ` (so the `‖P‖²`/Bruhat support bookkeeping is the
  same as for the product box up to constants). The Lipschitz error is now `E = ε` **with no `A`**.
  - First order: `A ε^{−3/2}Y^{1/4−δ_W} + ε`, optimized with an `A`-dependent box
    `ε = A^{2/5}Y^{(1−4δ_W)/10}` (trivial bound when this exceeds `1`): `|G_h| ≪ h^b A^{2/5} σ^{−12+s}`,
    `s → 1/10`, `a = 2/5`. Tauberian with `k = 2` still works for fractional `a`
    (`|P₂(σ₀+iy)| (|2y/σ₀|+3)^{a} ≪ σ₀^{−a}(σ₀+|y|)^{a−1}(1+|y|)^{−2}`, integrable uniformly).
    `η = s/(1+a) → 1/14`, `δ = η/(6+6η) → 1/90`.
  - Second order (symmetric sheared box): `A ε^{−3/2}Y^{1/4} + ε²`, `ε = A^{2/7}Y^{1/14}`:
    `s = 1/7`, `a = 4/7`, `η → 1/11`, `δ → 1/72`.
  - (A non-sheared anisotropic box, `y`-width `ε/A`, gives `A^{3/2}ε^{−3/2}Y^{1/4} + ε`, i.e.
    `a = 3/5`, `η → 1/16`: also a gain, but the sheared box is better.)
* **Why not formalized here.** Every box variant changes the test function `ft P`
  (`SCSProof.Test`), hence the unfolding `Q_eq`, the measure bounds `mI_ge`/`mB_ge`/`lintegral_ft_le`,
  the Bruhat support bound `Jp_le`, the ball bound `Dh_le_of_suppF` and `cf_sub_le`: a parallel copy
  of the `Par`-dependent part of `SCSProof` (≈ 20 files, ≈ 3.5k lines), plus the fractional-`a`
  kernel bound. Not attempted in this session; estimate 2–4k new lines.

## 5. Formalized (`RamanujanTau/SCSSharp2/`, 12 files, ≈ 2.6k lines)

| file | content |
|---|---|
| `Divisor.lean` | `card_divisors_le_rpow`: `τ(n) ≤ C_β n^β` (not in Mathlib) |
| `KloostGcd.lean` | `norm_kloosterman_hh_gcd_le` (`|S(h,h;c)| ≤ A (h,c)^{1/2} c^{1/2+δ}`), `sum_inv_dvd_le`, `sum_gcd_le`, **`norm_tsum_Iγ_le_gcd`** (`‖P‖² ≪ h^β ε³ Y^{−3/2−2δ}`) |
| `Point.lean`, `Rmean.lean`, `Asum.lean`, `Final.lean` | `η = 1/22` chain with `h^{1/22}`: `pointwise_G2`, `Rmean2_boundG`, `Asum_bound_largeG`, `shiftSum_boundG` |
| `Point21.lean`, `Rmean21.lean`, `Asum21.lean`, `Final21.lean` | `η = 1/21` chain (`δ_W = 1/400`, `κ = 2/39`, `ι = 1/273`, `j = 13`, `h^{1/21}`): `pointwise_G21`, `Rmean2_bound21`, `rankin_shortT`, `Asum_bound_large21`, `shiftSum_bound21` |
| `Reduction.lean` | `subconvexDelta2 η B u = η/((1+u)(4B+6+2η))`, `delta2_facts`, `rpoly_bound2`, **`tauL_subconvex_of_SCS2`** |
| `Main.lean` | headlines + `#print axioms` |

Headlines (`RamanujanTau.SCSSharp2`):

```lean
instance shiftedConvolutionBound_sharp2 : ShiftedConvolutionBound (1 / 21) (1 / 21)
--  |Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/21} h^{1/21}   for all h ≥ 1, N

theorem tauL_subconvex_of_SCS2 {η B : ℝ} [ShiftedConvolutionBound η B] (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta2 η B u)

theorem tauL_subconvex_sharp2_family {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / (132 * (1 + u)))

theorem tauL_subconvex_sharp2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ)
```

Intermediate (also proved): `shiftedConvolutionBound_22 : SCS(1/22, 1/22)`, `tauL_subconvex_140`
(`δ = 1/140`), `tauL_subconvex_22_oldReduction` (`δ = 1/181` via `SCSSharp.tauL_subconvex_of_SCS'`).

Reused by import (unchanged): `SCSProof` (Bruhat/unfolding/`Par`, `norm_kl_scale_le`, `kl_unit_eq`,
`norm_tsum_Iγ_le_gK`, Abel helpers), `SCSSharp` (`norm_Q_le'`, `norm_G0_le'`, `laplace_rieszK`,
`Pk2_mul_le`, `Rmean2`, `Asum_cs`, `integral_rpow_neg_le`, `diag`/`region` structure of `Reduction`),
`SubconvexityCond`, `MeanSquare.approx_tauL`, `RankinExact.rankinSelberg_exact`.

## 6. What limits further progress

1. **Within the formalized box: `η < s/2 < 1/20`.** `δ_W → 0` and `ι → 0` give at most
   `η → 1/20`, `δ → 1/126` (vs `1/134` now): ≤ 6% more, not worth the exponent churn.
2. **`B = η` is forced** by the statement shape (`N < h` regime), and costs only `4η` in the
   denominator (`1/134` vs `1/132·(1+u)` at `B = 0`).
3. **The reduction** is at its limit `η/(4B+6+2η)` up to the free `(1+u)`; beyond that the Gaussian
   window method itself must change.
4. **Main lever: the sheared box (§4)**, `δ → 1/90` (first order) or `1/72` (second order); it
   needs a new test function and a copy of the `Par`-dependent core of `SCSProof`.
5. Literature: Good (1982) `t^{1/3+ε}` (δ = 1/6, spectral theory) remains far away.
