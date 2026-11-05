# A power-saving error term for the Rankin–Selberg mean square of `τ` (`RamanujanTau/RankinError/`)

**Status (2026-11-04, evening).** The theorem

    S(N) = ∑_{n≤N} τ(n)²/n¹¹ = c·N + O(N^{1−1/84}),   c = (3/π)(4π)¹²‖Δ‖²/11! = 0.384084…,

is now **proved unconditionally**:

* **Evidence level 1 (Lean, axiom-clean, no hypotheses).**
  * **`rankinSelberg_power_saving_84`** (`PowerSaving84.lean`):
    `∃ C, ∀ N ≥ 1, |S(N) − c·N| ≤ C·N^{1 − 1/84}`, with Zagier's constant `c`.
  * `rankinSelberg_power_saving_unconditional` (`RSUnfoldProof.lean`): the same with the older
    exponent `1 − 2^{−22}` (halving descent).

  Both rest on `rsUnfold : RSUnfold`, the Rankin–Selberg unfolding identity

      mellin(Φ − ‖Δ‖²)(s) = γ(s) ζ(2s) ∑ τ(n)² n^{−s−11}     (Re s > 2),
      Φ(t) = ∫_𝓕 |Δ|²y¹² Θ_z(t) dμ,

  proved in five new files (F4–F6 below, about 1000 lines): `HMeasure`, `Coset`,
  `UnfoldTheta`, `RSMellin`, `RSUnfoldProof`. The exponent `1/84` comes from `RieszK.lean`
  (one 20-th order difference instead of 20 halvings, about 410 lines).
* Everything upstream (continuation, functional equation, strip bounds, Phragmén–Lindelöf,
  Perron/Riesz) was already axiom-clean; see the tables below.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`. Build only these files:
`nice -n 10 lake build RamanujanTau.RankinError.PowerSaving84` (all 23 files of the directory,
about 4200 lines). `RankinError/Main.lean` (unchanged) still prints the older headlines.
Nothing outside `RankinError/` and this write-up was modified. The root file does not import
this directory.

**Superseded:** the conditional `rankinSelberg_power_saving_of_unfold` (evidence level 2 until
today) is now only an intermediate step.

## Route A (horocycle with a rate, then a Tauberian theorem) cannot give a power saving

The brief suggested Route A first, since it reuses the horocycle machinery. It fails, and the
reason is structural.

1. **What route A can deliver.** Equidistribution of horocycles for `G = |Δ|²y¹²` (and for
   any other invariant test function) controls only

       F(t) = ∑ τ(n)² e^{−nt}   for real t > 0.

   This is a Laplace transform at real arguments. Parseval turns `∫₀¹ G(x+iy) dx` into
   `F(4πy)y¹²`. Twisting by other invariant functions such as `ΔG` or Hecke translates gives
   only derivatives `F^{(k)}` and rescalings `F(at)`, which are still real-axis data.
2. **Freud's theorem.** Suppose aₙ ≥ 0 and `F(t) = t^{−ρ}(K + O(t^η))`. Real-axis Laplace data
   of this kind gives only `A(x) = x^ρ(K/Γ(ρ+1) + O(1/log x))`, and this is sharp. The
   counterexample works on dyadic blocks `x ~ X`. Put an oscillation `1 + cos(λ log n)` on each
   block, with `λ = c·log X`. The Laplace transform sees this oscillation only through
   `Γ(1+iλ) ≈ e^{−πλ/2} = X^{−cπ/2}`, which is a power of `t`, while the partial sums move by
   about `X/λ = X/(c log X)`.

   Approximating the step function `1[n ≤ N]` by combinations of `e^{−nt}` needs coefficients
   of size `e^{O(1/ε)}` to reach accuracy `ε`. That is exactly where the logarithm is lost.
3. **The same obstruction seen from the Mellin side.** A rate `O(y^η)` for the horocycle mean
   does continue `D(s) = ∑ τ(n)² n^{−s−11}` to `Re s > 1 − η`. However, it gives
   `D(s) = (4π)^{s+11}Γ(s+11)^{−1}·(bounded)`, which grows like `e^{π|t|/2}`, and Perron's
   formula cannot be used with that growth.

   Polynomial growth needs the functional equation, that is, information in complex
   directions. Equivalently it needs `∑ τ(n)² e^{−n(y−iu)}` for `u ≠ 0`. That is a horocycle
   integral of `Δ(z+u)·conj Δ(z−u)·y¹²`, which is not Γ-invariant.

So route A yields at best `O(N/log N)`, which is not a power saving (paper argument, evidence
level 3). **Route B** (the functional equation) is therefore the cheapest route. It is the one
implemented here, arranged to need as little as possible:

* no K-Bessel functions: the Eisenstein series is continued with Riemann's theta method;
* no residue calculus: the main term comes from a second Mellin inversion;
* no Stirling formula: the Γ-ratios are exact on half-integer lines.

## Headline theorems

### Evidence level 1: the unconditional theorem and the unfolding identity (new)

| Theorem | File | Statement |
|---|---|---|
| **`rankinSelberg_power_saving_84`** | `PowerSaving84` | `∃ C, ∀ N ≥ 1, \|∑_{n=1}^N τ(n)²/n¹¹ − (3/π)(4π)¹² petNormSq/11! · N\| ≤ C N^{1−1/84}` |
| `power_saving_84_of_RSData` | `PowerSaving84` | `power_saving_of_RSData` with exponent `1 − 1/84` |
| **`riesz_kdiff`** | `RieszK` | `aₙ ≥ 0`, `c ≥ 0`, `0 < θ ≤ 1`: `RieszAsymp a c k θ → RieszAsymp a c 0 (θ/(k+1))` |
| `bracket` | `RieszK` | if `F_{j+1}(x+h) − F_{j+1}(x) = (j+1)∫₀^h F_j(x+s)ds` and `F_0` is monotone, then `k!h^kF_0(x) ≤ Δ_h^k F_k(x) ≤ k!h^kF_0(x+kh)` |
| `W_rel`, `psi_ftc` | `RieszK` | `W_{j+1}(x+h) − W_{j+1}(x) = (j+1)∫₀^h W_j(x+s)ds`, from `ψ_{j+1}(b) − ψ_{j+1}(a) = (j+1)∫_a^b ψ_j`, `ψ_j(u) = u_+^j` |
| `abs_Dk_le` | `RieszK` | `\|Δ_h^k f(x)\| ≤ 2^k sup_{[x,x+kh]}\|f\|` |
| `rankinSelberg_power_saving_unconditional` | `RSUnfoldProof` | `∃ C, ∀ N ≥ 1, \|∑_{n=1}^N τ(n)²/n¹¹ − (3/π)(4π)¹² petNormSq/11! · N\| ≤ C N^{1−1/2²²}` |
| **`rsUnfold`** | `RSUnfoldProof` | `RSUnfold` |
| `RSUnfold_real` | `RSUnfoldProof` | `RSUnfold` at real `σ > 2` |
| `lintegral_mellin_Phi` | `RSMellin` | for real `σ > 0`, in `[0,∞]`: `∫₀^∞ t^{σ−1}(Φ(t)−‖Δ‖²)dt = 2Γ(σ)π^{−σ}·∑_{g≥1}g^{−2σ}·∑ₙ τ(n)²Γ(σ+11)(4πn)^{−σ−11}` |
| `lintegral_hfun` | `RSMellin` | `∫₀^∞ t^{σ−1} ∑_{g≥1} e^{−πtg²/v} dt = Γ(σ)π^{−σ}v^σ ∑_{g≥1} g^{−2σ}` |
| **`unfold_theta`** | `UnfoldTheta` | for `t > 0`, in `[0,∞]`: `∫_𝓕 G(z)(Θ_z(t)−1) dxdy/y² = 2∫₀^∞ I(v) ∑_{g≥1}e^{−πtg²/v} dv/v²`, `I(v) = ∫₀¹ G(x+iv)dx` |
| `lintegral_Psi` | `UnfoldTheta` | `∫_ℍ 1_{0≤Re<1}(w) G(w) h_t(Im w) dμ = ∫₀^∞ I(v)h_t(v) dv/v²` (Tonelli) |
| **`theta_coset`** | `Coset` | `∑_{(m,n)∈ℤ²} e^{−πtQ_z(m,n)} = 1 + ∑_{γ∈SL₂(ℤ)} 1_{0≤Re<1}(γz) h_t(Im γz)` |
| `tsum_strip_eq` | `Coset` | for `T`-invariant `H ≥ 0`: `∑_γ 1_{strip}(γz)H(γz) = ∑_{(a,c) coprime} H(M(a,c)⁻¹z)` |
| `tsum_theta_split` | `Coset` | `ℤ²∖0 = ℕ₊ × {coprime}`: `∑_{(m,n)} e^{−πtQ} = 1 + ∑_{g≥1}∑_{(a,c)} e^{−πtg²Q(−c,a)}` |
| `im_inv_mat_smul` | `Coset` | `Im(M(a,c)⁻¹z) = 1/Q_z(−c,a)` |
| **`lintegral_unfold_U`** | `HMeasure` | for measurable `Ψ ≥ 0` on `ℍ`: `∫_ℍ 1_U(z)∑_γ Ψ(γz) dμ = 2∫_ℍ Ψ dμ`, `U = {−½≤Re<½, \|z\|≥1}` |
| `ae_tsum_ind_U` | `HMeasure` | for a.e. `w ∈ ℍ`: `∑_γ 1_U(γw) = 2` |
| `volume_circ` | `HMeasure` | the unit circle is null for the invariant measure |
| `measurePreserving_sl` | `HMeasure` | `w ↦ γw` preserves `dxdy/y²` (from Mathlib's `SMulInvariantMeasure (GL(2,ℝ)) ℍ`) |
| `lintegral_H` | `HMeasure` | `∫_ℍ φ dμ = ∫_{y>0} φ(x+iy) dxdy/y²` |

### Evidence level 2 (conditional; now discharged by `rsUnfold`)

```lean
def RSUnfold : Prop :=
  ∀ s : ℂ, 2 < s.re → mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s =
    gam s * riemannZeta (2 * s) * LSeries (fun n => (aTau n : ℂ)) s
-- Phi t = ∫ p in Freg, gR p * theta p.1 p.2 t,  aTau n = τ(n)²/n¹¹
```

| Theorem | Statement |
|---|---|
| **`rankinSelberg_power_saving_of_unfold`** | `RSUnfold → ∃ C, ∀ N ≥ 1, \|∑_{n=1}^N τ(n)²/n¹¹ − (3/π)(4π)¹² petNormSq/11! · N\| ≤ C N^{1−1/2²²}` |
| `rsData_of_unfold` | `RSUnfold → RSData aTau petNormSq` (constructs `Λ₀ = rsFE.Λ₀`) |

The intermediate interface `RSData` is the following.

```lean
structure RSData (a : ℕ → ℝ) (κ : ℝ) where
  Λ₀ : ℂ → ℂ
  diff : Differentiable ℂ Λ₀
  L₀ : ℝ
  bdd : ∀ s : ℂ, -3/2 ≤ s.re → s.re ≤ 5/2 → ‖Λ₀ s‖ ≤ L₀
  fe : ∀ s : ℂ, Λ₀ (1 - s) = Λ₀ s
  unfold : ∀ s : ℂ, 2 < s.re →
    gam s * riemannZeta (2*s) * LSeries (fun n => (a n : ℂ)) s = Λ₀ s + κ * (1/(s-1) - 1/s)
-- gam s = 2 π^{-s} Γ(s) Γ(s+11) (4π)^{-s-11}
```

For `aₙ = τ(n)²/n¹¹` and `κ = ‖Δ‖²`, `RSData` is the classical Rankin–Selberg theorem (Rankin
1939, Selberg 1940):

    Λ(s) = ∫_{SL₂(ℤ)\ℍ} |Δ|² y¹² E*(z,s) dμ = ξ(2s)·2Γ(s+11)(4π)^{−s−11} ∑ τ(n)² n^{−s−11},

where `E*(z,s) = π^{−s}Γ(s)·½∑'_{(m,n)} y^s|mz+n|^{−2s}` satisfies `E*(z,1−s) = E*(z,s)` and
has simple poles at `s = 0, 1`. Then `Λ₀ = Λ − κ(1/(s−1) − 1/s)` is entire and symmetric.

| Theorem | Statement |
|---|---|
| **`rankinSelberg_power_saving_of_RSData`** | `RSData aTau petNormSq → ∃ C, ∀ N ≥ 1, \|∑_{n=1}^N τ(n)²/n¹¹ − (3/π)(4π)¹² petNormSq/11! · N\| ≤ C N^{1−1/2²²}` |
| `power_saving_of_RSData` | the same for any `a ≥ 0` with `a 0 = 0`, `∑ aₙ n^{−5/2} < ∞` and `RSData a κ` (`κ ≥ 0`); main term `κ·3(4π)¹²/(π 11!)·N` |

### Evidence level 1 (axiom-clean, unconditional)

| Theorem | File | Statement |
|---|---|---|
| `pow_succ_sub_bounds` | `Riesz` | `(k+1)h u^k ≤ (u+h)^{k+1} − u^{k+1} ≤ (k+1)h(u+h)^k` |
| `W_diff_bounds` | `Riesz` | for `aₙ ≥ 0`, `W_k(x) = ∑_{n≤x} aₙ(x−n)^k`: `(k+1)h W_k(x) ≤ W_{k+1}(x+h) − W_{k+1}(x) ≤ (k+1)h W_k(x+h)` |
| `riesz_step` | `Riesz` | `W_{k+1} = c x^{k+2}/(k+2) + O(x^{k+2−θ})` ⇒ `W_k = c x^{k+1}/(k+1) + O(x^{k+1−θ/2})` |
| `riesz_descend`, `partial_sum_of_riesz0` | `Riesz` | iterating: saving `θ` at order `k` ⇒ `∑_{n≤N} aₙ = cN + O(N^{1−θ/2^k})` |
| `mellin_phi`, `beta_eq_Pk` | `RieszKernel` | `∫₀¹ u^{s−1}(1−u)^k du = k!/(s(s+1)⋯(s+k))` |
| `norm_Pk_le` | `RieszKernel` | `‖P_k(s)‖ ≤ k!(2/m)^{k+1}(1+\|Im s\|)^{−(k+1)}`, `m = min(σ₁,1)`, for `Re s ≥ σ₁ > 0` |
| `mellinInv_Pk` | `RieszKernel` | Mellin inversion `mellinInv σ P_k u = (1−u)_+^k` (`k ≥ 1`, `σ > 0`, `u > 0`) |
| `integral_line_eq` | `Contour` | if `g` is holomorphic on `a ≤ Re s ≤ b` and `‖g‖ ≤ C/(1+\|Im s\|)²` there, then `∫ g(b+iy)dy = ∫ g(a+iy)dy` |
| `perron_riesz` | `Perron` | `2π ∑ aₙ (1−n/x)_+^k = ∫ x^{c+iy} P_k(c+iy) D(c+iy) dy` (`c > 1`) |
| `rieszAsymp_of_continuation` | `PerronShift` | `D = F + c₀/(s−1)` on `Re s = c`, `F` holomorphic on `Re s > σ₀`, `‖F‖ ≤ B(1+\|t\|)^K` on `[σ₁,c]` ⇒ `W_{K+1}(x) = c₀x^{K+2}/(K+2) + O(x^{K+1+σ₁})` |
| `norm_Gamma_le_Gamma_re` | `GammaBound` | `‖Γ(w)‖ ≤ Γ(Re w)` for `Re w > 0` |
| `exists_norm_inv_Gamma_le` | `GammaBound` | `‖1/Γ(w)‖ ≤ C e^{π\|Im w\|}` for `Re w ≥ −A`, `\|Im w\| ≥ 1` |
| `gamma_ratio_le` | `Landau` | on `Re s = −3/2`: `‖γ(1−s)/γ(s)‖ ≤ 2⁹(‖s+2‖+13)^{17}`, an exact computation via `Γ(ū) = conj Γ(u)` at `Re u = ½` |
| `fPL_bound` | `Landau2` | Phragmén–Lindelöf: `(s(s−1)Λ₀(s)+κ)/(γ(s)(s+3)¹⁹)` is bounded on `−3/2 ≤ Re s ≤ 5/2` (given `RSData`) |
| `Ffun_bound`, `LSeries_eq_Ffun` | `Landau3` | `D(s) − c₀/(s−1)` extends holomorphically to `Re s > ½`, with `O((1+\|t\|)^{19})` on `[¾, 5/2]` (given `RSData`) |
| **`theta_inv`** | `Theta` | `Θ(1/t) = tΘ(t)` for `Θ(t) = ∑_{(m,n)∈ℤ²} exp(−πt\|mz+n\|²/y)` |
| `Qf_ge`, `theta_one_le`, `theta_sub_one_le` | `ThetaBound` | on `𝓕`: `\|mz+n\|²/y ≥ (m²+n²)/(2y)`, `Θ(1) ≤ 2yϑ₀²`, `Θ(t) − 1 ≤ e^{−π(t−1)/(2y)}Θ(1)` |
| `exists_G_exp_le` | `ThetaBound` | `G(z) ≤ Ke^{−c Im z}` for `Im z ≥ ½` (Mathlib `CuspFormClass.exp_decay_atImInfty'`) |
| `Phi_inv`, `Phi_sub_le` | `ThetaInt` | `Φ(1/t) = tΦ(t)`; `0 ≤ Φ(t) − ‖Δ‖² ≤ C_R(t−1)^{−R}` for `t > 1` |
| `rsFE` | `RSFE` | `WeakFEPair ℂ` with `f = g = Φ`, `k = 1`, `ε = 1`, `f₀ = g₀ = ‖Δ‖²` |
| `rsFE_Λ₀_bdd`, `rsFE_symm_Λ₀` | `RSFE` | `Λ₀` is bounded on every vertical strip; `Λ₀(1−s) = Λ₀(s)` |
| `poisson_shift`, `tsum_gauss_le` | `Theta` | `∑ₙ e^{−πa(n+c)²} = a^{−1/2}∑ₖ e^{−πk²/a}e^{2πikc}` and the uniform bound |

## The proof (route B)

1. **Riesz–Perron.** The kernel is `φ_k(u) = (1−u)_+^k`, with Mellin transform
   `P_k(s) = k!/∏_{j≤k}(s+j)`, computed from Mathlib's Beta integral.
   * Mellin inversion (`mellinInv_mellin_eq`) applied termwise gives `perron_riesz`.
   * On the line `Re s = c` write `D = F + c₀/(s−1)`.
   * The pole term needs no residue: `P_k(s)/(s−1) = P_{k+1}(s−1)/(k+1)`, so its integral is
     again a Mellin inversion. It equals `c₀ x (1−1/x)^{k+1}/(k+1)`.
   * The `F` term moves to `Re s = σ₁` by Cauchy's theorem on rectangles
     (`integral_boundary_rect_eq_zero_of_differentiableOn` plus decay). It is then
     `O(x^{σ₁})`, provided `k = K+1`.
2. **Descent.** With `aₙ ≥ 0` the Riesz sums are monotone in the right sense, so
   `W_{k+1}(x+h) − W_{k+1}(x)` brackets `(k+1)hW_k`. Choosing `h ≍ x^{1−θ/2}` halves the saving
   at each step. After 20 steps the saving is `(1/4)/2²⁰ = 2^{−22}`.
3. **Convexity (Phragmén–Lindelöf).** Apply Mathlib's `PhragmenLindelof.vertical_strip` to
   `f(s) = (s(s−1)Λ₀(s)+κ)/(γ(s)(s+3)¹⁹)` on the strip `[−3/2, 5/2]`.
   * Right edge: `f = s(s−1)ζ(2s)D(s)/(s+3)¹⁹` is bounded, by absolute convergence at `Re s = 5/2`.
   * Left edge: by the functional equation `f(s)` equals the right-edge expression at `1−s`
     times `γ(1−s)/γ(s)`. Write `u = s+2`, so `Re u = ½`. Then
     `Γ(1−s)/Γ(s) = ū(ū+1)(u−1)(u−2)·Γ(ū)/Γ(u)`, and similarly at `s+11` with 13 and 9
     factors. Since `|Γ(ū)| = |Γ(u)|`, the ratio is a polynomial of degree 17.
   * Growth inside: `‖1/Γ(w)‖ ≤ Ce^{π|Im w|}`, from reflection and `|Γ(w)| ≤ Γ(Re w)`.
     This gives order `e^{(2π+2)|t|}`, well inside the admissible `exp(B e^{|t|/2})`.
4. **Back to `D`.** Put `F(s) = (Λ₀(s) − κ/s)g(s) + κ·dslope g 1 s`, where
   `g = 1/(γ(s)ζ(2s))` is holomorphic on `Re s > ½` (`ζ ≠ 0` for `Re > 1`). Then
   `D = F + c₀/(s−1)`, `c₀ = κ g(1) = 3κ(4π)¹²/(π 11!)`, and on `[¾, 5/2]` we have
   `‖F‖ ≤ B(1+|t|)¹⁹`, using `‖1/ζ(w)‖ ≤ ∑ |μ(n)| n^{−3/2}`.

The halving descent gives `δ = 2^{−22}`. It is now superseded by the single 20-th order
difference (`riesz_kdiff`, below), which gives `δ = (1−σ₁)/(k+1) = 1/84`. With convexity done
sharply (Stirling) one would get Rankin–Selberg's `δ = 2/5`.

## Numerical evidence (level 4)

`scripts/rankinerror/error_term.gp` (PARI, `nbthreads = 1`, `N = 10⁶`, 6 s). It reports the
maximum of `|S(x) − cx|` over each decade.

| decade | max \|S(x)−cx\| | at x | /x^{3/5} | /x^{1/2} |
|---|---|---|---|---|
| [10, 100) | 1.78 | 68 | 0.142 | 0.216 |
| [10², 10³) | 4.97 | 926 | 0.082 | 0.163 |
| [10³, 10⁴) | 16.1 | 9197 | 0.067 | 0.168 |
| [10⁴, 10⁵) | 41.2 | 94038 | 0.043 | 0.134 |
| [10⁵, 10⁶] | 96.1 | 949447 | 0.025 | 0.099 |

The error grows roughly like `x^{0.4}` (`/x^{1/2}` slowly decreasing). That is consistent with
Rankin–Selberg's `O(x^{3/5})` and with the conjectured `x^{3/8+ε}`. Horocycle numerics are in
`docs/EISENSTEIN_REAL.md`: `(I(y)/L − 1)/√y` stays bounded.

## The unfolding identity `RSUnfold` (proved 2026-11-04)

The unfolding is done **before** the Mellin transform, so the measure-theoretic part is a
nonnegative (`[0,∞]`) identity for each fixed `t`:

    Φ(t) − ‖Δ‖² = 2 ∫₀^∞ I(v) ∑_{g≥1} e^{−πt g²/v} dv/v²,     I(v) = ∫₀¹ G(x+iv) dx.     (U)

| Piece | Content | Lines |
|---|---|---|
| F1 ✅ | `theta_inv` | (earlier) |
| F2 ✅ | `Φ_inv`, local integrability (`Φ` is antitone), cusp decay of `G` | (earlier) |
| F3 ✅ | `Φ − κ = O(t^{−R})` | (earlier) |
| F7 ✅ | `rsFE`, `Λ₀` bounded and symmetric, `rsData_of_unfold` | (earlier) |
| F5a ✅ | `HMeasure`: real coordinates for Mathlib's invariant measure on `ℍ`; null unit circle; a.e. `∑_γ 1_U(γw) = 2` (from `exists_smul_mem_U`, `smul_mem_S_unique`, `two_le_tsum`, `tsum_le_two`); the abstract unfolding `∫ 1_U ∑_γ Ψ∘γ = 2∫Ψ` | 215 |
| F5b ✅ | `Coset`: `ℤ²∖0 = ℕ₊ × coprime` (`latMap`, via `Int.gcd_div_gcd_div_gcd`), the coset sum via `slEquiv` applied to `γ⁻¹`, `Im(M⁻¹z) = 1/Q(−c,a)` | 210 |
| F5c ✅ | `UnfoldTheta`: (U), with `𝓕` replaced by `{−½ ≤ x < ½}` up to the null line `x = ½` | 176 |
| F4 ✅ | `RSMellin`: Tonelli in `(t, v)`, Euler's integral termwise, E3a (`lintegral_mellin_horocycle`) | 171 |
| F6 ✅ | `RSUnfoldProof`: real form at `σ > 2` (all quantities real: `Γ`, `ζ(2σ)`, `L(σ)`), then the **identity theorem** on `Re s > 2`: `mellin(Φ−κ) = Λ₀(s) − κ/s − κ/(1−s)` and `γζL` are holomorphic there and agree on `3 + 1/(n+1)` | 227 |

Design choices that kept it short:

* **No complex dominated convergence.** The planned F6 (complex-`s` E3a by dominated convergence)
  was replaced by analytic continuation: the identity is proved for real `σ` in `[0,∞]` and
  extended by `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. Holomorphy of the left side
  comes free from `rsFE` (`mellin(Φ−κ) = rsFE.Λ` for `Re s > 1`), of `L(s)` from
  `LSeries_differentiableOn` with abscissa `≤ 2` (`τ(n)²/n¹¹ ≪ n`).
* **The unfolding is in `[0,∞]` throughout**, so Tonelli and `lintegral_tsum` need only
  measurability, never integrability.
* **Fundamental domain without boundary bookkeeping.** `∑_γ 1_U(γw) = 2` holds off the countable
  union of `SL₂(ℤ)`-translates of the unit circle, which is null by invariance of the measure.
  The edge `Re = ½` is removed in real coordinates (a line in `ℝ²`).
* Measurability of `I(v)` is avoided by replacing it with its Parseval series `∑ τ(n)²v¹²e^{−4πnv}`
  (`hasSum_mterm`) inside the integrals.

Sanity check of the normalisation (paper, now also implied by the Lean proof): both sides of
`RSUnfold` have residue `κ` at `s = 1`, and `γ(1)ζ(2)·c = κ` with `c = 3κ(4π)¹²/(π·11!)`, the
constant of `rankinSelberg_asymptotic_zagier_unconditional`.

## The exponent `1/84` (`RieszK`, `PowerSaving84`)

`rieszAsymp_of_continuation` gives the Riesz mean of order `k = 20` with saving `θ = 1 − σ₁ = 1/4`
(order `20 = K + 1`, where `K = 19` is the growth exponent of `Ffun_bound`). The halving descent
turned that into `θ/2^{20}`. `riesz_kdiff` takes one `k`-th forward difference instead:

* `ψ_{j+1}' = (j+1)ψ_j` (right derivative; `ψ_j(u) = u_+^j`) gives the exact relation
  `ΔW_{j+1} = (j+1)∫₀^h W_j(·+s)ds`. The main terms `M_j = c x^{j+1}/(j+1)` satisfy the same
  relation.
* `bracket` (induction on `k`, using that `Δ^k` commutes with `∫₀^h ·(·+s)ds`):
  `k!h^kF_0(x) ≤ Δ_h^kF_k(x) ≤ k!h^kF_0(x+kh)` for both families (`W_0` is monotone since
  `aₙ ≥ 0`).
* The error `E = W_k − M_k = O(x^{k+1−θ})` contributes `|Δ^kE| ≤ 2^k sup|E|`. With
  `h = x^{1−θ/(k+1)}/(k+1)` both `ckh` and `2^k sup|E|/(k!h^k)` are `O(x^{1−θ/(k+1)})`.

So `δ = (1/4)/21 = 1/84`.

## What remains

Nothing for the stated theorem. Further improvements of the exponent:

* lower the growth exponent `19` in `Ffun_bound`. That lowers the order `k` of the Riesz mean
  and raises `δ = (1−σ₁)/(k+1)`. The `19` comes from the crude polynomial normalisation
  `(s+3)^{19}` in the Phragmén–Lindelöf function. With the real convexity bound (a growth
  exponent below 1 near `σ = 1`) one gets `δ` around `1/10`;
* with Stirling and an optimised contour one reaches Rankin–Selberg's `δ = 2/5`.

## Literature

* R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n) … I, II*, Proc.
  Cambridge Phil. Soc. 35 (1939): error `O(x^{3/5})`.
* A. Selberg, *Bemerkungen über eine Dirichletsche Reihe …*, Arch. Math. Naturvid. 43 (1940).
* G. Freud, *Restglied eines Tauberschen Satzes I*, Acta Math. Acad. Sci. Hungar. 2 (1951);
  J. Korevaar, *Tauberian Theory*, Springer 2004, Ch. VII: real-Laplace Tauberian remainders are
  at best `O(1/log x)`.
* E. Landau, *Über die Anzahl der Gitterpunkte in gewissen Bereichen* (1912). This is the
  contour/smoothing lemma for Dirichlet series with nonnegative coefficients.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, §3.2 (theta continuation of `E(z,s)`)
  and §13.
* D. Zagier, *The Rankin–Selberg method for automorphic functions which are not of rapid
  decay* (1981).

**Update (2026-11-05).** Every δ < 2/5 is now proved by Landau's method, and this is now **unconditional**:
`KernelPhase.rankinSelberg_landau_uncond` (the Γ-integral bound `KernelOneBound` is proved in
`KernelPhase`). See [RANKIN_LANDAU](RANKIN_LANDAU.md) and [KERNEL_PHASE](KERNEL_PHASE.md).
