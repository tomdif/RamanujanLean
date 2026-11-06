# The Rankin–Selberg error term is `Ω(x^{3/8})`

Lean: `RamanujanTau/RankinOmega/` (8 files, about 2230 lines). Build with
`nice -n 10 lake build RamanujanTau.RankinOmega.Main` (exit 0). There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. `#print axioms` on every headline gives
`[propext, Classical.choice, Quot.sound]`. **Evidence level (1).** Deligne is not used. The
directory is not imported by `RamanujanTau.lean`.

## 1. Statements

Let `R(N) = ∑_{n≤N} τ(n)²/n¹¹ − cN`, where `c = (3/π)(4π)¹²‖Δ‖²/11!` is the constant of
`RankinExact.rankinSelberg_exact`. That theorem gives `|R(N)| ≤ C N^{3/5}`.

```lean
-- namespace RamanujanTau.RankinOmega   (Main.lean)
theorem rankinSelberg_error_omega :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, ∃ N : ℕ, N0 ≤ N ∧
      c' * (N : ℝ) ^ ((3 : ℝ) / 8) ≤
        |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N|

theorem rankinSelberg_error_not_isLittleO :
    ¬ (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 - 3 / π * … * N)
        =o[atTop] (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 8))

-- for EVERY real constant c (the argument never uses the value of c):
theorem tau_rankin_omega (c : ℝ) : ∃ c' > 0, ∀ X, ∃ x ≥ X,
    c' * x ^ (3/8) ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, τ(n)²/n¹¹ − c x|
theorem tau_rankin_omega_nat (c : ℝ) : …                  -- the same along the integers

-- every nonzero level-one cusp form, every weight k, every c
theorem cuspForm_rankin_omega (f : CuspForm 𝒮ℒ k) (hf : f ≠ 0) (c : ℝ) : ∃ c' > 0, ∀ X, ∃ x ≥ X,
    c' * x ^ (3/8) ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, coeffSq f n / n^(k−1) − c x|
theorem cuspForm_rankin_omega_nat …

-- abstract Rankin–Selberg data (RSDataM m a κ, m ≥ 1, abscissa ≤ 1, some aₙ ≠ 0)
theorem rs_omega / rs_omega_nat / rs_omega_core
```

The exponent is exact, with no `ε` and no logarithm. Combined with `rankinSelberg_exact`, the true
order of the Rankin–Selberg error has exponent in `[3/8, 3/5]`. The conjectured value is
`3/8 + ε`.

New reusable results (all level (1)):

| theorem | statement |
|---|---|
| `ZetaApprox.zeta_formula` | `ζ(s) = ∑_{n≤N} n^{−s} + N^{1−s}/(s−1) − s∫_N^∞ {t} t^{−s−1} dt` for `Re s > 0`, `Im s < 0`, `N ≥ 1` (Mathlib has no Euler–Maclaurin formula for `ζ` in the strip) |
| `norm_zeta_sub_le` | `‖ζ(s) − ∑_{n≤N} n^{−s}‖ ≤ N^{1−u}/‖s−1‖ + ‖s‖N^{−u}/u` |
| `ZetaMean.zeta_mean_sq` | `∫_T^{2T} ‖ζ(u − it)‖² dt ≤ C T`, uniformly for `3/4 ≤ u ≤ 1`, `T ≥ 1` |
| `gamma_ratio_lower` | `‖γₘ(σ−iy)⁻¹‖ ≥ c_g y^{2−4σ} ‖γₘ(1−σ+iy)⁻¹‖`, uniformly for `3/8 ≤ σ ≤ 1/2`, `y ≥ 1` |
| `tail_gen` | `‖L(b, x+iy) m^{x+iy} − b(m)‖ ≤ ε` for all `x ≥ c₀`, for `m` the least index of `b` |
| `Zf_horiz` | `‖ζ(2w)D(w)‖ ≤ K y^{15/16}` on `9/16 ≤ Re w ≤ c`, `Im w = y ≥ 1` |
| `Zf_first_moment` | `∫_Y^{2Y} ‖ζ(2w)D(w)‖ dy ≥ c₃ Y` on `Re w = σ' ∈ [9/16, 5/8]`, uniformly in `σ'` |
| `mellin_Rf_large` | `∫₀^∞ R(x) x^{−s−1} dx = D(s)/s − c/(s−1)` for `Re s > 2` |
| `Lam_eq_mellin` | under `‖R(x)‖ ≤ c₀x^θ`: `Λ(s)γₘ(s)⁻¹ = ζ(2s)(sM(s) + cs/(s−1))` on `{Re s > θ} ∩ {Im s < 0}` |
| `block_lower` | `∫_Ξ^{2Ξ} ‖M(σ − 2πiξ)‖² dξ ≥ K₁ (2Ξ)^{−8δ}`, `σ = 3/8 + δ`, `K₁`, `Ξ₀` independent of `δ` |

Here `D(s) = ∑ aₙ n^{−s}` and `Λ = Lam d` is the completed function,
`Λ(s) = γₘ(s)ζ(2s)D(s)` with `Λ(1−s) = Λ(s)`. For `Δ`, `Λ = RStar` of `RankinSelbergFE`.

## 2. The exponent on paper

Write `σ = Re s` and `t = Im s`.

**Degree and gamma factor.** `γ(s) = 2π^{−s}Γ(s)Γ(s+11)(4π)^{−s−11}` has two Γ-factors of
`s`-weight 1. As an `L`-function, `ζ(s)L(sym²Δ, s) = ζ(2s)D(s)` has degree 4. Stirling applied
to each factor gives `|Γ(1−σ+it)/Γ(σ+it)| ≍ |t|^{1−2σ}`, so

    |γ(1−s)/γ(s)| ≍ |t|^{2−4σ} = |t|^{4(1/2−σ)}.

**Mellin transform.** `M(s) = ∫₁^∞ R(x)x^{−s−1}dx = D(s)/s − c/(s−1)`. By Plancherel on the log
scale, `∫|R(x)|² x^{−2σ−1} dx = (1/2π)∫|M(σ+it)|² dt`.

**Functional equation.** With `w = 1 − s`, `Λ(s) = Λ(w)` gives

    |ζ(2s)| |D(s)| = |γ(w)/γ(s)| |ζ(2w)D(w)|.

So on dyadic blocks `|t| ~ T`:

    |M(σ+it)|² ≍ T^{−2} T^{2(2−4σ)} |ζ(2w)D(w)|² / |ζ(2s)|².

If `∫_T^{2T} |ζ(2w)D(w)|²/|ζ(2s)|² ≫ T` uniformly in `σ`, each block contributes
`≫ T^{3−8σ}`. This sum diverges exactly when `σ ≤ 3/8`, which is `(d−1)/(2d)` with `d = 4`. At
`σ = 3/8 + δ` each block contributes `T^{−8δ}`, and summing over `⌈1/(8δ)⌉` blocks gives
`≫ 1/δ`. If `|R(x)| ≤ c₀x^{3/8}`, the left side is `≤ c₀²/(2δ) + O(1)`. For `c₀` small this is a
contradiction, as in `TauOmegaPartial`.

**What is different from `τ` (`TauOmegaPartial`).** There are two differences.

1. **The reflected line is inside the critical strip.** For a cusp form, `k − σ` lies in the
   half-plane of absolute convergence. Here `1 − σ = 5/8 − δ` is in `(1/2, 1)`, where no mean-value
   asymptotic for a degree-4 function is available (the classical range is `σ > 1 − 1/d = 3/4`).
   But only a *lower* bound of the *first* moment is needed, uniformly in the line. Let `n₀` be the
   least index with `a(n₀) ≠ 0`. On a far-right line, `ζ(2w)D(w)n₀^w ≈ a(n₀)`. A rectangle moves
   this to `Re w = σ'`, and the horizontal sides are `≪ Y^{15/16}` by the convexity bound
   `‖E(w)‖ ≪ ‖w+3‖^{31/16}` (`Stirling.Efun_bound_eps` with `σ₁ = 9/16`, `ε = 1/32`, and
   `E(w) = (w−1)ζ(2w)D(w)`). This gives `Zf_first_moment`.
2. **The denominator `ζ(2s)`.** `D = ζ(s)L(sym²,s)/ζ(2s)`, and on the line `Re 2s = 3/4 + 2δ`,
   `1/ζ(2s)` cannot be bounded below pointwise. The convexity bound `|ζ| ≪ |t|^{1/8}` would cost
   `T^{−1/4}` per block and destroy the divergence. Instead, an AM–GM with an optimized parameter
   λ is used. Pointwise,

       c_g Ξ^{2−4σ} |Z(w)| ≤ |ζ(2s)| |X(s)|,    where X = sM + cs/(s−1),

   and `|ζ||X| ≤ (λ²|ζ|² + |X|²)/(2λ)`. This needs only the **mean square of `ζ` on
   `3/4 ≤ Re ≤ 7/8`**, `∫_T^{2T}|ζ|² ≪ T` (`zeta_mean_sq`), uniformly in the line. That is
   proved from the exact formula with `N = ⌈T^{4/3}⌉`, which makes the error `≤ 6` pointwise,
   together with the repo's weak Montgomery–Vaughan theorem `MeanSquare.mv_poly`:
   `∑n^{−2u} ≤ ζ(3/2)` and `H_N∑n^{1−2u} ≪ N^{5/8} ≪ T^{5/6}`.

   Choosing `λ = A/(C_ζΞ)`, with `A = c_g c₃ Ξ^{3−4σ}`, gives

       ∫|X|² ≥ A²/(C_ζ Ξ) ≍ Ξ^{5−8σ} = Ξ^{2−8δ},

   and dividing by `‖s‖² ≍ Ξ²` gives `Ξ^{−8δ}` (`block_lower`, `final_alg`). The zeros of
   `ζ(2s)` cause no difficulty. The identity `Λ(s)γ(s)⁻¹ = ζ(2s)(sM(s) + cs/(s−1))` is
   multiplicative: wherever `ζ(2s) = 0`, `Λ(w)` vanishes too. The identity principle is applied
   on the convex set `{Re s > 3/8} ∩ {Im s < 0}`, which avoids the poles at `s = 1/2` and `s = 1`
   (`Lam_eq_mellin`).

**Route choice** (decided on paper first).

- **(a) Landau–Mellin–Plancherel.** This is the route used, with the `TauOmegaPartial`
  `Plancherel`, `G1`/`G2` and dyadic skeleton reused.
- **(b) Landau's theorem for nonnegative coefficients.** `R(x)` has no sign, and
  `M(s) ± c'/(s−3/8)` has no real singularity at `3/8`. The only singularities of `D` left of 1
  come from zeros of `ζ(2s)` at `Re s ≤ 1/4`. Those would need `Z(ρ/2) ≠ 0` and give at most
  `Ω(x^{1/4−ε})`, so route (b) cannot reach `3/8`.
- **(c) Voronoi-type `L²` expansion.** This is the route to a mean-square asymptotic. It is
  heavier and was not needed for Ω.

Unconditionally, the cleanest statement turned out to be `Ω(x^{3/8})` itself, with no `ε` loss.

## 3. Files

| file | content | lines |
|---|---|---|
| `ZetaApprox.lean` | `fr`, `gN`, `IN`, `norm_IN_le`, `zeta_formula_large`, `zeta_formula`, `norm_zeta_sub_le` | 280 |
| `ZetaMean.lean` | `rpow_le_of_pow_le`, `sum_inv_sqrt_le`, `cpow_eq_conj_ex`, `zeta_mean_sq` | 243 |
| `Analytic.lean` | `norm_invGamM`, `gamma_ratio_lower`, `tail_gen`, `Zf`, `differentiableAt_Lam/Zf`, `Zf_eq`, `Zf_horiz` | 340 |
| `FirstMoment.lean` | `summable_a2`, `Zf_tail`, `Zf_first_moment` | 229 |
| `Mellin.lean` | `Asum`, `Ind`, `Rf`, `mellin_Asum_large`, `mellin_Ind_large`, `mellin_Rf_large`, `differentiableAt_mellin_Rf`, `Lam_eq_mellin`, `hfun`, `fourier_hfun`, `norm_hfun_le`, `hfun_L1L2` | 385 |
| `Block.lean` | `amgm_aux`, `final_alg`, `g1_lower`, `g2_upper`, `block_pt`, `block_lower` | 321 |
| `Omega.lean` | `dyadic_weight8`, `rs_omega_core` | 178 |
| `Main.lean` | `rs_omega`, `rs_omega_nat`, cusp-form and `τ` headlines, `#print axioms` | 251 |

Reused results:

- `TauOmegaPartial`: `plancherel_of_integrable`, `G1`, `G2`, `integrable_G1/G2`, `integral_G2`.
- `MeanSquare.mv_poly`, `H_le_one_add_log`.
- `RankinSharpGeneral`: `Lam`, `Lam_fe`, `Lam_eq`, `Efun_eq`.
- `Stirling`: `Efun_bound_eps`, `exists_norm_zeta_le2`, `norm_LSeries_le_Deps`.
- `RankinLandau.norm_Gamma_ratio_unif'` and `KernelPhase.rect_diff`.
- `RankinErrorGeneral`: `gamM`, `invGamM`, `rsFnCusp`, `rsDataG`.
- `RankinSharpGeneral.abscissa_aF_le_one`.
- `RankinSelbergGeneral.exists_coeff_ne_zero` and `TauBound.qExpansion_discriminant_coeff_tau`.

## 4. Numerics (evidence level (4))

`scripts/rankin_omega/rankin_omega_check.gp` (PARI, `nbthreads = 1`), with `c = 0.384084054…`,
gives:

- For `1000 < N ≤ 2·10⁵`: `R(N)/N^{3/8} ∈ [−0.59, 0.64]`.
- `R(2·10⁵) = −12.6`.
- The mean of `R(N)²` over `N ≤ X`, divided by `X^{3/4}`, is about `0.016`.

These numbers are consistent with order `x^{3/8}` (possibly up to `ε`), and far below `x^{3/5}`.

## 5. Gaps and what is not claimed

- **Ω± is not proved.** The method sees only `|R|`. Ω± needs a sign argument, for example
  Landau's theorem applied to `∫R x^{−s−1} ± c'/(s−3/8)`. That fails because there is no real
  singularity. A Voronoi-series positivity argument was not attempted.
- **The mean square `∫₁^X R² ≍ X^{7/4}` is not proved.** Under the contradiction hypothesis the
  argument shows `∫₁^∞ |R|² x^{−2σ−1} dx ≫ 1/(σ−3/8)` as `σ ↓ 3/8`. That is the Mellin form of
  the lower mean-square bound, but it is not stated as a standalone theorem. Stating it would be a
  small refactor of `rs_omega_core`. The upper bound `∫R² ≪ X^{7/4+ε}` and the asymptotic would
  need the Voronoi `L²` route (c).
- The constant `c'` is implicit. It comes from `gamma_ratio_lower`, `Zf_first_moment` and
  `zeta_mean_sq`.
- The upper exponent remains `3/5` (`RankinExact`). The gap `[3/8, 3/5]` is untouched from above.

## 6. Literature (from memory; attributions not checked against the sources)

- R. A. Rankin (1939): the error term is `O(x^{3/5})`.
- The Ω-result `Δ(x) = Ω(x^{3/8})` for the Rankin–Selberg problem, and the conjecture
  `Δ(x) ≪ x^{3/8+ε}`, appear in A. Ivić's papers on the Rankin–Selberg problem (around 1990).
- The mean-square conjecture `∫₁^X Δ² ≍ X^{7/4}` is also from that line of work.
- Recent upper-bound improvements below `3/5` are due to B. Huang (2021).
- The Landau–Plancherel Ω-method: Landau; see Ivić, *The Riemann Zeta-Function*, Ch. 13.
