# Mean square of `∑_{n≤x} τ(n)` at the critical exponent `25/2` (unconditional, Lean)

Lean: `RamanujanTau/Voronoi/` (6 files, about 1600 lines). No `sorry`, no `native_decide`, no new
axiom, no named hypothesis. Build with `nice -n 10 lake build RamanujanTau.Voronoi.Main` (exit 0).
`#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
**Evidence level (1).** Deligne is not used.

The directory name follows the brief. The truncated Voronoi formula itself (item (1)) was **not**
proved. Item (2) was proved by a Mellin–Landau route instead, in two forms: a logarithmic mean
square, and a dyadic upper bound that loses a `log`. Item (3), exact `Ω±(x^{23/4})`, was **not**
proved. §4 says what is missing for each.

## 1. Statements

Write `S(x) = ∑_{1≤n≤x} τ(n)`. In Lean `S(x)` is written out as
`∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)`.

```lean
-- namespace RamanujanTau.Voronoi   (Main.lean)
theorem tau_critical_mean_square_convergent {σ : ℝ} (hσ : 23 / 4 < σ) :
    IntegrableOn (fun x => S x ^ 2 * x ^ (-2 * σ - 1)) (Ioi 1)

theorem tau_critical_mean_square_mellin : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
      c / δ ≤ ∫ x in Ioi 1, S x ^ 2 * x ^ (-(25/2) - 2 * δ) ∧
      ∫ x in Ioi 1, S x ^ 2 * x ^ (-(25/2) - 2 * δ) ≤ C / δ

theorem tau_log_mean_square : ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ X0 ∧ ∀ X ≥ X0,
    c * log X ≤ ∫ x in Ioc 1 X, S x ^ 2 * x ^ (-(25/2)) ∧
    ∫ x in Ioc 1 X, S x ^ 2 * x ^ (-(25/2)) ≤ C * log X

theorem tau_mean_square_upper : ∃ C > 0, ∀ X ≥ exp 16,
    ∫ x in Ioc 1 X, S x ^ 2 ≤ C * X ^ (25/2) * log X

theorem tau_mean_square_omega : ∃ c > 0, ∀ Y, ∃ X ≥ Y,
    c * X ^ (25/2) ≤ ∫ x in Ioc 1 X, S x ^ 2

theorem tau_mellin_identity {w : ℂ} (hw : 23 / 4 < w.re) :
    MellinConvergent (fun x => (S x : ℂ)) (-w) ∧ mellin (fun x => (S x : ℂ)) (-w) = tauL w / w
```

In words:

- **Convergence.** `∫₁^∞ S(x)² x^{−2σ−1} dx` converges for **every** `σ > 23/4`. This is the
  mean-square form of `S(x) ≪ x^{23/4+ε}`, which is the conjectured sup bound. The best proved sup
  bound, `x^{59/10+ε}` (`TauPartialSumsSharp`), only gives convergence for `σ > 59/10`.
- **Two-sided Mellin bound.** `∫₁^∞ S² x^{−25/2−2δ} ≍ 1/δ`, with constants independent of `δ`.
- **Logarithmic mean.** `∫₁^X S(x)² x^{−25/2} dx ≍ log X`.
- **Upper bound.** `∫₁^X S² ≪ X^{25/2} log X`. The Cramér-type asymptotic is `∼ C X^{25/2}`, so
  this is off by one `log` (§4).
- **Lower bound.** `∫₁^X S² ≥ c X^{25/2}` for arbitrarily large `X`, i.e. `∫₁^X S² ≠ o(X^{25/2})`.
  Together with the previous item, the exponent `25/2` is exact up to a `log`.
- **Mellin identity.** `∫₁^∞ S(x) x^{−w−1} dx = L(Δ,w)/w` converges absolutely on `Re w > 23/4`.
  `TauOmegaPartial` and `TauOmegaPM` had this only under a growth hypothesis, or under a one-sided
  hypothesis inside a proof by contradiction.

Reusable intermediate results (all level (1)):

| name | statement |
|---|---|
| `block_bound` | `∫_T^{2T} |L(Δ,6−y+iu)/(6−y+iu)|² du ≤ K T^{4y−1}/y`, uniformly for `0 < y ≤ 1/4`, `T ≥ 1` |
| `tail_of_blocks` | generic dyadic summation: block bounds `B T^{−p}` give `∫_R^∞ ≤ B R^{−p}/(1−2^{−p})` |
| `tail_bound` | `∫_R^∞ Ψ_{6−y} ≤ K R^{−(1−4y)} / (y(1−2^{−(1−4y)}))` |
| `even_split` | splitting an even function into `[−R,R]` and `|u| > R` |
| `differentiableOn_intervalIntegral` | holomorphy of `w ↦ ∫_a^b F(w,ξ) dξ` when `F` and `∂_wF` are jointly continuous |
| `differentiableOn_P` | `P(w) = ∫ G(w−2πiξ) G(w+2πiξ) dξ` is holomorphic on `23/4 < Re w < 6`, where `G = L(Δ,·)/·` |
| `mellin_eq_P_strip` | `∫ S² x^{−s−1} = P(s/2)` on `2θ < Re s < 12`, `θ = 237/40` |
| `mc_all` | `∫ S² x^{−s−1}` converges for every real `s > 23/2` (Landau) |
| `mellin_sq` | for `23/4 < σ < 6`: `∫ S² x^{−2σ−1} = ∫ |L(Δ,σ−2πiξ)/(σ−2πiξ)|² dξ` |
| `Phi_upper`, `Phi_lower` | that integral is `≤ C/δ` and `≥ K/(4δ)`, where `σ = 23/4 + δ` |
| `fL_Dl` | `HeckeConvexGeneral.fL Δ = HeckeL.tauL` (bridge between the general and the `τ` L-functions) |

## 2. Proof

Write `g(x) = S(x)²`, `M(s) = ∫₁^∞ g(x) x^{−s−1} dx`, `G(s) = L(Δ,s)/s`, and
`Ψ_σ(u) = |G(σ+iu)|²`.

1. **Uniform tails** (`Tail.lean`). For `σ = 6 − y` with `0 < y < 1/4`:
   - The functional equation with uniform Stirling (`MeanSquareFull.norm_tauL_left_le`) gives
     `|L(6−y+iu)| ≤ 6e¹⁰(1+|u|)^{2y}|L(6+y+iu)|`.
   - The uniform mean value `HardyCountHafner.mean_square_uniform` gives
     `∫_T^{2T}|L(6+y+it)|² ≤ CT/y`, with `C` independent of `y`.
   - Together these give `∫_T^{2T}Ψ_{6−y} ≤ K T^{4y−1}/y`.
   - Dyadic summation then gives `∫_R^∞ Ψ_{6−y} ≤ (K/y) R^{−(1−4y)}/(1−2^{−(1−4y)})`. The bound is
     uniform on compact `y`-ranges inside `(0, 1/4)`, i.e. on `σ ∈ [23/4+d, 6−d]`.
2. **Holomorphy of `P`** (`Holo.lean`).
   - Define `P_N(w) = ∫_{−N}^{N} G(w−2πiξ)G(w+2πiξ) dξ`. Each `P_N` is holomorphic, by
     differentiation under the integral sign with a compactness bound.
   - `|G(w−2πiξ)G(w+2πiξ)| ≤ (Ψ_σ(η−2πξ)+Ψ_σ(η+2πξ))/2`, where `w = σ+iη`.
   - A change of variables then gives `|P(w) − P_N(w)| ≤ (2π)⁻¹∫_{|u|>N}Ψ_σ`, once `N ≥ |η|`.
   - By step 1 this tends to `0` uniformly on small balls. `TendstoLocallyUniformlyOn.differentiableOn`
     then shows `P` is holomorphic on the strip `23/4 < Re w < 6`.
3. **Real-axis Plancherel** (`MeanSq.lean`, `mellin_g_real`).
   - `|S(x)| ≪ x^θ` with `θ = 237/40 = 11/2+2/5+1/40` (`TauPartialSumsSharp`).
   - For real `σ > θ`, `TauOmegaPartial.plancherel_of_integrable` and `fourier_hfun` give
     `M(2σ) = ∫|h_σ|² = ∫|𝓕h_σ|² = ∫|G(σ−2πiξ)|² dξ`.
   - The last integral equals `P(σ)`, because `G(s̄) = conj G(s)` (`tauL_conj`).
4. **Identity theorem** (`mellin_eq_P_strip`).
   - `M(s)` is holomorphic on `Re s > 2θ` (`TauOmegaPM.differentiableOn_mellin_neg`).
   - `P(s/2)` is holomorphic on `23/2 < Re s < 12`.
   - The two agree at the real points of the strip `2θ < Re s < 12`, hence on the whole strip.
   - This step relies on `θ < 6`, that is, on the sharp exponent `59/10 < 6`. With it, the region
     where `M` is known to converge overlaps the region where `P` is known to be holomorphic.
     That overlap lets us avoid proving holomorphy of `P` across the critical line `Re w = 6`,
     where `mean_square_uniform` degenerates like `1/y`.
5. **Landau** (`mc_all`).
   - Define `F(s) = M(s)` for `Re s > 119/10` and `F(s) = P(s/2)` otherwise. By step 4, `F` is
     holomorphic on `Re s > 23/2`.
   - `g ≥ 0`, so `TauOmegaPM.landau_mellin` shows that `M(σ)` converges for every real
     `σ > 23/2`.
   - `mellin_eq_of_eventually` then gives `M(2σ) = P(σ)` for `23/4 < σ < 6` (`mellin_sq`).
6. **Two-sided `1/δ`** (`Bounds.lean`). Take `σ = 23/4+δ`.
   - Upper bound: `P(σ) = (2π)⁻¹∫Ψ_σ`. Use step 1 with `y = 1/4−δ` and `1−2^{−4δ} ≥ δ` on the
     tail, and a compactness bound on `|u| ≤ 1`.
   - Lower bound: the dyadic blocks `TauOmegaPartial.block_lower` / `dyadic_weight`, as in
     `TauOmegaPartial.Omega`. They are now applied to a quantity that is known to be finite.
7. **Consequences** (`Final.lean`).
   - Upper: take `δ = 1/log X`. Then `x^{−25/2} ≤ e²x^{−25/2−2δ}` on `[1,X]`.
   - Lower: split `∫₁^∞ S²x^{−25/2−2δ}` at `X = e^{L/δ}`. The tail is
     `≤ X^{−δ}·∫S²x^{−25/2−δ} ≤ 2Ce^{−L}/δ`, using the upper bound at `δ/2`.
   - Ω: if `∫₁^X S² < cX^{25/2}` for all large `X`, every dyadic block of `∫S²x^{−25/2}` is
     `≤ c2^{25/2}`. That contradicts the `log` lower bound when `c < c_low·log 2/(2·2^{25/2})`.
   - Mellin identity: AM–GM gives `|S|x^{−σ−1} ≤ (S²x^{−2σ'−1} + x^{2σ'−2σ−1})/2`. Then
     `TauOmegaPM.mellin_A_eq_of_conv`.

## 3. Files

| file | content | lines |
|---|---|---|
| `Tail.lean` | `Psi`, `block_bound`, `tail_of_blocks`, `tail_bound`, `even_split`, `integrable_Psi` | 250 |
| `Holo.lean` | `differentiableOn_intervalIntegral`, `Gt`, `Qd`, `P`, `PN`, `norm_Qd_le`, `tail_sub/add`, `norm_P_sub_PN`, `uniform_tail`, `differentiableOn_P` | 391 |
| `MeanSq.lean` | `fL_Dl`, `P_real`, `sharp_bound`, `mellin_g_real`, `mellin_eq_P_strip`, `FL`, `differentiableOn_FL`, `mc_all`, `mellin_sq` | 253 |
| `Bounds.lean` | `integral_Fs_sq`, `one_sub_two_rpow_ge`, `Phi_upper`, `Phi_lower` | 159 |
| `Final.lean` | real-integral forms, `log_mean_upper/lower`, `mean_square_upper`, `mean_square_omega`, `mc_A`, `tau_mellin_uncond` | 478 |
| `Main.lean` | headlines with explicit sums, `#print axioms` | 86 |

Reused:
- `HardyCountHafner.mean_square_uniform`;
- `MeanSquareFull.norm_tauL_left_le`, `norm_tauL_neg`;
- `TauPartialSumsSharp.cuspForm_partial_sum_sharp`;
- `TauOmegaPartial`: `A`, `hfun`, `hfun_L1L2`, `fourier_hfun`, `plancherel_of_integrable`, `Fs`,
  `block_lower`, `dyadic_weight`, `exists_first_coef`;
- `TauOmegaPM`: `landau_mellin`, `mellin_eq_of_eventually`, `differentiableOn_mellin_neg`,
  `mc_of_bound`, `mc_mono`, `mellin_A_eq_of_conv`;
- `HeckeZeros.tauL_conj`;
- `HardyZerosGeneral.discriminant_ne_zero'`.

The directory is not imported by `RamanujanTau.lean`.

## 4. Gaps and what remains

- **(1) Truncated Voronoi: not done.** The repository has the exact dual expansion only for Riesz
  means of order `r ≥ 2` (`TauPartialSumsSharp.dual_rep`), and its kernels are Mellin–Barnes
  integrals `J_r`. Getting the Voronoi main term needs three things:
  - identify `J_r(y)` with `c·y^{(k+r)/2}J_{k+r}(4π√y)`, either by a residue series (shifting
    right, past the poles of `Γ(k−s)`) or by the Bessel ODE;
  - prove the Bessel asymptotic `J_ν(z) = √(2/πz)cos(z−νπ/2−π/4) + O(z^{−3/2})`. Mathlib has no
    Bessel functions. Stationary phase on `J_n(z) = π⁻¹∫cos(nθ−z sinθ)dθ` is the shortest route
    to the constant;
  - descend from order `r` to order `0` with an `L²` error. This is Landau differencing at scale
    `h ≍ √x`, plus a Montgomery–Vaughan bound for frequencies `√n`.

  The expected normalization (weight `k`, level one, `i^k = 1` for `k = 12`, not formalized) is
  `S(x) = (x^{k/2−1/4}/(π√2)) ∑_{n≤N} τ(n) n^{−k/2−1/4} cos(4π√(nx) − π/4) + R(x,N)`, i.e.
  `x^{23/4}/(π√2)·∑ τ(n) n^{−25/4} cos(4π√(nx) − π/4)`. This is evidence level (3).
- **(2) Exact Cramér constant: not done.** The expected constants are
  `∫₁^X S(x)² dx ∼ (1/(50π²)) ∑ τ(n)²/n^{25/2} · X^{25/2}` and
  `∫₁^X S²x^{−25/2} ∼ (1/(4π²)) ∑ τ(n)²/n^{25/2} · log X`. These are level (3); see §5 for the
  numerical check. On the Mellin side, the second is equivalent to
  `δ·∫|G(23/4+δ−2πiξ)|²dξ → B/(8π²)`, where `B = ∑τ²n^{−25/2}`.
  - This needs a mean-value **asymptotic** for `∫_0^T|L(6+y+it)|²`, `∼ RS(12+2y)T`, that is
    uniform for `y` near `1/4`, together with a uniform Stirling asymptotic for `|χ|²`.
    `MeanSquareFull` only gives the asymptotic for each fixed `σ`, and `mean_square_uniform` only
    gives an upper bound.
  - With that input, Karamata's Tauberian theorem would give the exact constant in the
    logarithmic mean. (A log-weighted Karamata is in `CriticalMeanSquareAsymp`.)
- **Dyadic upper bound without `log`.** `∫_X^{2X} S² ≪ X^{25/2}` does not follow from Mellin
  information at `σ → 23/4` alone. Choosing `δ = 1/log X` is optimal, and it costs `log X`. The
  bound needs either the truncated Voronoi formula with an `L²` remainder, or the off-diagonal
  analysis of `∫ S² w(x/X)` with a smooth weight `w`.
- **Dyadic lower bound.** `∫_X^{2X} S² ≫ X^{25/2}` for **all** large `X` is not proved. What is
  proved is the lower bound for the logarithmic mean, and the lower bound for `∫₁^X S²` along a
  sequence of `X`.
- **(3) Exact Ω±(x^{23/4}): not done.** The mean-square information does not improve
  `TauOmegaPM`'s `28/5`. Under a one-sided hypothesis `S ≥ −cx^β` with `β < 23/4`, we know that
  `S₊` has bounded `L¹(x^{−σ−1})` norm while its `L²(x^{−2σ−1})` norm is `≍ 1/δ`. These two facts
  are consistent unless one also has a sup bound or an `L^p` bound with `p > 2`. For example, the
  fourth-moment bound `∫S⁴x^{−4σ−1} ≪ 1/δ` together with Hölder would give
  `Ω±(x^{23/4})` with an explicit constant. The fourth moment (Tong) is again a Voronoi-type
  input.
- The results are stated for `τ` only. The uniform mean value `mean_square_uniform` exists only for
  `L(Δ,s)`. The argument works verbatim for any level-one Hecke eigenform once that input is
  generalized.

## 5. Numerical check (evidence level (4))

The check uses PARI `ramanujantau` for `n ≤ 2·10^4`. It computes `J(X) = ∫₁^X S(x)²x^{−25/2}dx`
exactly on the step function `S`, and `B = ∑_{n≤2·10^4} τ(n)²n^{−25/2} = 1.58281`. The prediction
is `B/(4π²) = 0.040093`.

| X | J(X) | slope of J against log X |
|---|---|---|
| 10³ | 0.34653 | |
| 10⁴ | 0.43934 | (J(10⁴)−J(10³))/log 10 = 0.04031 |
| 2·10⁴ | 0.46717 | (J(2·10⁴)−J(10⁴))/log 2 = 0.04014 |

The slope agrees with the predicted Cramér constant `(1/4π²)∑τ(n)²n^{−25/2}` to about 0.1%. This
supports `∫₁^X S²x^{−25/2} ∼ (B/4π²) log X`, the unproved exact form of `tau_log_mean_square`.
Equivalently it supports `∫₁^X S² ∼ (B/50π²) X^{25/2}`.

## 6. Literature (from memory, not checked against sources)

- H. Cramér (1922): mean square of the error term in the divisor problem.
- R. A. Rankin (1939), A. Walfisz: mean values of cusp-form coefficient sums.
- K.-C. Tong (1956): mean square and higher moments of the Voronoi error terms.
- J. L. Hafner, A. Ivić (1989), *On sums of Fourier coefficients of cusp forms*: these use
  Deligne and the Voronoi formula.
- A. Ivić, *Large values of certain number-theoretic error terms* (1990): the Cramér–Tong constants.

The classical asymptotic `∫₁^X S² ∼ C X^{25/2}` is due to the Cramér–Tong theory. The
unconditional, Deligne-free, Mellin–Landau route used here was not checked against the
literature, and no novelty claim is made.


The PARI script used for the numerics above was not preserved (session scratchpad); the numerics are evidence level (4) only.
