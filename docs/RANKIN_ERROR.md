# A power-saving error term for the Rankin–Selberg mean square of τ (`RamanujanTau/RankinError/`)

**Status (2026-11-04).** The goal is

    S(N) = ∑_{n≤N} τ(n)²/n¹¹ = c·N + O(N^{1−δ}),   c = (3/π)(4π)¹²‖Δ‖²/11! = 0.384084…,

for some explicit δ > 0. What is proved:

* **Evidence level 2 (Lean, conditional on one named hypothesis).**
  `rankinSelberg_power_saving_of_unfold`: if `RSUnfold` holds, then
  `|S(N) − c·N| ≤ C·N^{1 − 2^{−22}}` for all `N ≥ 1`, with Zagier's constant `c`.

  `RSUnfold` is only the classical unfolding identity for real-part `> 2`:

      mellin(Φ − ‖Δ‖²)(s) = γ(s) ζ(2s) ∑ τ(n)² n^{−s−11},      Φ(t) = ∫_𝓕 |Δ|²y¹² Θ_z(t) dμ.

  It involves no analytic continuation. The continuation, the functional equation and the
  boundedness on vertical strips of the completed Rankin–Selberg integral are **proved**
  (`rsFE`, `rsFE_Λ₀_bdd`, `rsData_of_unfold`).
* **Evidence level 1 (Lean, axiom-clean, no hypotheses).** The rest of the chain:
  * Riesz means, the Mellin inversion of the Riesz kernel, and the contour shift;
  * bounds for Γ in vertical strips, and Phragmén–Lindelöf for the completed L-function;
  * the descent from Riesz means to partial sums;
  * the transformation law of the lattice theta function, `Θ(1/t) = tΘ(t)`;
  * `Φ(1/t) = tΦ(t)`, with rapid decay of `Φ − ‖Δ‖²`;
  * the weak functional-equation pair `rsFE`, which gives an entire, symmetric `Λ₀`, bounded
    on strips.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]` (`Main.lean`). Build only these files:
`nice -n 10 lake build RamanujanTau.RankinError.Main`. This builds all 16 files, about 2700 lines.
Nothing outside `RankinError/` was modified. The root file does not import this directory.

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

### Evidence level 2 (conditional)

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

The exponent `δ = 2^{−22}` is wasteful but explicit. Two improvements would raise it:

* Replace the halving descent by one k-th order difference. That uses the integral
  representation `Δ_h^k W_k = k!∫_{[0,h]^k} W_0(x + Σtᵢ)`, and gives `δ = (1−σ₁)/(k+1)`,
  about `1/84`.
* With convexity done sharply (Stirling) one gets Rankin–Selberg's `δ = 2/5`.

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

## What remains: the unfolding identity `RSUnfold`

F1–F3 and F7 below are done, so the continuation and the functional equation are proved. Only
the identity of `mellin(Φ−κ)` with the Dirichlet series is missing. That is a statement for
`Re s > 2`, where everything converges absolutely. The cheapest arrangement unfolds **before**
taking the Mellin transform, so the measure-theoretic part is a nonnegative (ENNReal) identity
for each fixed `t`:

    Φ(t) − ‖Δ‖² = 2 ∫₀^∞ I(v) ∑_{g≥1} e^{−πt g²/v} dv/v²,     I(v) = ∫₀¹ G(x+iv) dx.     (U)

Then `∫₀^∞ t^{s−1} ∑_g e^{−πtg²/v} dt = π^{−s}Γ(s)ζ(2s)v^s`. Combined with the complex-`s`
form of E3a, `∫₀^∞ I(v)v^{s−2}dv = ∑ τ(n)²Γ(s+11)(4πn)^{−s−11}`, this gives `RSUnfold`.

| Piece | Content | Estimate |
|---|---|---|
| F1 ✅ | `theta_inv` | done |
| F2 ✅ | `Φ_inv`, local integrability (`Φ` is antitone), cusp decay of `G` | done |
| F3 ✅ | `Φ − κ = O(t^{−R})` | done |
| F7 ✅ | `rsFE`, `Λ₀` bounded and symmetric, `rsData_of_unfold` | done |
| F5 | (U): split `ℤ²∖0 = ℕ₊ × {coprime}` (`g·(c,d)`), then `∑_{γ∈SL₂(ℤ)} 1_{strip}(γz) h(Im γz) = ∑_{(c,d) coprime} h(y/\|cz+d\|²)` (`HoroUnfold`'s `SL₂(ℤ) ≃ coprime × ℤ`, applied to `γ⁻¹`), then `∫_S ∑_γ φ̃∘γ = ∑_γ ∫_{γS} φ̃ = 2∫ φ̃`, using `SMulInvariantMeasure (GL(2,ℝ)) ℍ volume`, `smul_mem_S_unique`, `exists_smul_mem_U`, `two_le_tsum`/`tsum_le_two`, and the unit circle being null. Plus the change of coordinates `ℍ ↔ ℝ²` against `Freg`/`gR` | 450 |
| F4 | Fubini in `(t, v)` and the Gamma integral `∫ t^{s−1}e^{−at} = Γ(s)a^{−s}` termwise | 150 |
| F6 | complex-`s` E3a, by dominated convergence from the real version `lintegral_mellin_horocycle` | 120 |

Total remaining: about 700 lines. After that, `rankinSelberg_power_saving_of_unfold` is
unconditional with no other change.

Sanity check of the normalisation (paper): both sides of `RSUnfold` have the residue `κ` at
`s = 1`. Indeed `γ(1)ζ(2)·c = κ` with `c = 3κ(4π)¹²/(π·11!)`, which is the constant of the
already-proved asymptotic `rankinSelberg_asymptotic_zagier_unconditional`.

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
