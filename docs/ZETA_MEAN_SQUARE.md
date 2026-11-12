# Mean square of ζ off the critical line, and Rankin–Selberg Ω±(x^{1/4−ε})

Lean: `RamanujanTau/ZetaMeanSquare/` (8 files, about 1780 lines). Build with
`nice -n 10 lake build RamanujanTau.ZetaMeanSquare.Main`, which exits 0. There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. `#print axioms` on all 19 listed results
gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1)** for everything in §1.
The public entry point is included in the `RamanujanTau.lean` import graph.

## 1. Statements (namespace `RamanujanTau.ZetaMeanSquare`)

### (1) The Hardy–Littlewood / Landau mean-value theorem (`Zeta.lean`)

```lean
-- uniform on [σ₀, 1], explicit error
theorem zeta_mean_value_uniform {σ₀ : ℝ} (hσ₀ : 1/2 < σ₀) :
    ∃ C ≥ 0, ∀ σ, σ₀ ≤ σ → σ ≤ 1 → ∀ T, 1 ≤ T →
      |∫ t in 1..T, ‖ζ(σ + t I)‖² − (ζ(2σ)).re · T|
        ≤ C · (T^(3/2 − σ) + T^(2 − 2σ) · (1 + log T)²)

-- the same on dyadic blocks [T, 2T]
theorem zeta_mean_value_dyadic {σ₀} (hσ₀ : 1/2 < σ₀) : … ∫ t in T..2T … (same right side)

-- the Cesàro limit
theorem zeta_mean_square_tendsto {σ} (h1 : 1/2 < σ) (h2 : σ ≤ 1) :
    Tendsto (fun T => (∫ t in 1..T, ‖ζ(σ + t I)‖²) / T) atTop (𝓝 (ζ(2σ)).re)
theorem zeta_mean_square_tendsto_zero {σ} (h1 : 1/2 < σ) (h2 : σ < 1) :
    Tendsto (fun T => (∫ t in 0..T, ‖ζ(σ + t I)‖²) / T) atTop (𝓝 (ζ(2σ)).re)

-- ζ(2σ) is real, so `.re` loses nothing
lemma riemannZeta_two_mul_real (σ) (h : 1/2 < σ) : ζ(2σ) = ((ζ(2σ)).re : ℂ)
```

At `σ = 1` the integral must start at `1`, not `0`. `ζ(1+it) ~ 1/(it)`, so `∫₀¹|ζ(1+it)|²` diverges.
This is why the `0`-based form requires `σ < 1`.

Byproducts, all level 1 and reusable:

| theorem | statement |
|---|---|
| `riemannZeta_conj` | `ζ(s̄) = conj ζ(s)` for `s ≠ 1`. Mathlib does not have this. Proved by the identity principle on `ℂ∖{1}`. |
| `riemannZeta_ofReal_eq_re` | `ζ` is real on `ℝ∖{1}` |
| `tail_L2` | `∫_a^b ‖I_N(u−it)‖² dt ≤ π N^{−2u}/u`, where `I_N(s) = ∫_N^∞ {x}x^{−s−1}dx` (Plancherel on the log scale) |
| `err_L2` | `∫_1^T ‖ζ(σ−it) − ∑_{n≤⌈T⌉} n^{−σ+it}‖² ≤ (4+16π) T^{2−2σ}` for `1/2 ≤ σ ≤ 1` |
| `mean_value_minus` | the uniform theorem on the line `σ − it` |
| `norm_zeta_fe_le` | `‖ζ(v−iτ)‖ ≤ K τ^{1/2−v} ‖ζ(1−v+iτ)‖` for `0 < v ≤ 1/2`, `τ ≥ 2`, uniformly |
| `zeta_dyadic_upper` | `∫_T^{2T} ‖ζ(u+it)‖² ≤ C T` for fixed `1/2 < u ≤ 1` |
| `zeta_two_s_mean_sq` | `∫_Y^{2Y} ‖ζ(2(σ−iy))‖² dy ≤ K Y^{2−4σ}` for `0 < σ < 1/4` |

### (2) Rankin–Selberg Ω± with exponent 1/4 (`Rankin.lean`)

```lean
theorem tau_rankin_omega_pm_quarter {β : ℝ} (hβ : β < 1/4) (c1 X : ℝ) :
    (∃ x ≥ X, ∑_{n≤x} τ(n)²/n¹¹ − c₀ x < −c1 x^β) ∧
    (∃ x ≥ X, c1 x^β < ∑_{n≤x} τ(n)²/n¹¹ − c₀ x)
    -- c₀ = 3/π (4π)¹² ‖Δ‖² / 11!
theorem cuspForm_rankin_omega_pm_quarter (f : CuspForm 𝒮ℒ k) (hf : f ≠ 0) {β} (hβ : β < 1/4) …
    -- with c = rsConst f
theorem cuspForm_omega_pm_quarter_of_bound … -- any c with a 3/5 bound
theorem rs_omega_pm_quarter …                 -- abstract RSDataM with |R| ≤ C x^{3/5}
theorem false_of_conv_quarter …               -- Mellin convergence on Re s > β, β < 1/4 ⇒ False
```

`c1` ranges over all of `ℝ`, so `limsup R/x^β = +∞` and `liminf R/x^β = −∞`. That is,
`R(x) = Ω±(x^{1/4−ε})`. This improves `RankinOmegaPM.tau_rankin_omega_pm`, which has `3/20 − ε`.
Two Ω results are now formal: the two-sided `Ω(x^{3/8})` (`RankinOmega`) and the signed
`Ω±(x^{1/4−ε})` (this directory). The conjectured truth for both is `3/8`.

## 2. Routes

### Mathlib

Mathlib has no mean-value theorem for ζ, no `ζ(s̄) = conj ζ(s)`, and no Euler–Maclaurin formula in
the strip. It does have the functional equation `completedRiemannZeta_one_sub`,
`riemannZeta_def_of_ne_zero` (`ζ = Λ/Γ_ℝ`), `mellin_eq_fourier`, and `integral_exp_mul_Iic`.

### Goal (1): why the existing `zeta_mean_sq` stopped at 3/4, and the fix

`RankinOmega.zeta_mean_sq` used the pointwise error `|ζ(s) − P_N(s)| ≤ N^{1−σ}/|t| + |s|N^{−σ}/σ`.
To make the second term `O(1)` it needs `N ≥ T^{1/σ}`. The Montgomery–Vaughan off-diagonal term
`H_N ∑ n^{1−2σ} ≍ N^{2−2σ}` is then `o(T)` only for `σ > 2/3`. More Euler–Maclaurin terms push the
threshold to `(k+1)/(2k+1)`, but never uniformly to `1/2`.

**The fix:** bound the error only **in `L²`**, with `N = ⌈T⌉`. The tail `s·I_N(s)` has
`|s| ≤ 2T`. Its integrand `I_N(σ−it)` is, as a function of `t`, the Fourier transform of
`h(v) = e^{σv}{e^{−v}}1_{v<−log N}`. Plancherel (`TauOmegaPartial.plancherel_of_integrable`) gives

    ∫|I_N|² ≤ 2π‖h‖² ≤ π N^{−2σ}/σ.

So `∫_1^T|ζ−P|² ≪ T²·T^{−2σ} = T^{2−2σ}`, which is `o(T)` for every `σ > 1/2`. The other pieces
are as follows.

- `mv_poly` on `[0,T]` minus `[0,1]` gives `|∫_1^T|P|² − (T−1)∑n^{−2σ}| ≤ 12 H_N ∑ n^{1−2σ}`. The
  bound `∑ n^{1−2σ} ≤ N^{2−2σ}H_N` yields `O((1+log T)² T^{2−2σ})`.
- The diagonal: `zeta_formula_large` on the real point `2σ` gives
  `|ζ(2σ) − ∑_{n≤N} n^{−2σ}| ≤ N^{1−2σ}/(2σ−1) + N^{−2σ}`.
- The cross term: AM–GM with weight `η = T^{1/2−σ}`,
  `| |ζ|² − |P|² | ≤ η|P|² + (1+1/η)|ζ−P|²`, gives the `T^{3/2−σ}` term. No Cauchy–Schwarz is needed.
- `zeta_formula` holds only for `Im s < 0`, so everything is first proved on `σ − it`
  (`mean_value_minus`). It is then transferred to `σ + it` with `riemannZeta_conj`.

**Error term.** The proved error is `O(T^{3/2−σ} + T^{2−2σ}log²T)`, uniform on `[σ₀,1]`. The
constant depends on `σ₀` only through `ζ(2σ₀)` and `1/(2σ₀−1)`. The classical sharp error is
`O(T^{2−2σ} log T)`, which is better than `T^{3/2−σ}` (Titchmarsh §7.2). The `T^{3/2−σ}` comes from
the crude AM–GM cross term. A sharp version would need the diagonal of `∫ P·conj(E)`, that is, an
explicit main term for `∫ P_N(s)·N^{1−s}/(s−1)` and for the tail. This is not attempted.

### Goal (2): the 1/4 route of `RANKIN_OMEGA_PM.md` §2

Suppose `εR ≥ −c₁x^β` (`ε = ±1`, `β < 1/4`). Then `RankinOmegaPM.conv_of_one_sided` (strip Landau)
makes `M(s) = ∫R x^{−s−1}` absolutely convergent on `Re s > β`. Fix
`σ = (max(β,1/8) + 1/4)/2 ∈ (β, 1/4)`. On `s = σ − iy`:

1. `|M(s)| ≤ L = ∫|R|x^{−σ−1}` (`norm_mellin_le`).
2. `Lam_eq_mellin_conv` and the functional equation `Λ(s) = Λ(1−s)` give
   `c_g y^{2−4σ}|Z(1−σ+iy)| ≤ |ζ(2s)|·y(2L+2|c|)` (`quarter_pt`). The Γ-ratio bound is needed down to
   `σ > 0`. `RankinOmega.gamma_ratio_lower` was stated for `[3/8,1/2]`, so the proof is copied as
   `gamma_ratio_lower'`. The proof only uses `σ > 0`.
3. The first moment `∫_Y^{2Y}|Z(1−σ+iy)| ≥ c₃Y` is needed at `Re w = 1−σ ∈ (3/4,7/8)`.
   `Zf_first_moment` was stated for `[9/16,5/8]`, so the proof is copied as `Zf_first_moment'` with
   range `[9/16,1]`. The proof only uses `σ' ≤ c`.
4. The `ζ(2s)` mean square at `Re(2s) = 2σ ∈ (1/4,1/2)` uses the functional equation
   `|ζ(v−iτ)| ≤ Kτ^{1/2−v}|ζ(1−v+iτ)|`. The ingredients are `Λ = Λ(1−·)`, `ζ = Λ/Γ_ℝ`, the shift
   `Γ(z+1) = zΓ(z)`, and the uniform ratio `RankinLandau.norm_Gamma_ratio_unif'` on `1 ≤ Re ≤ 2`.
   Combined with goal (1) at `u = 1−2σ ∈ (1/2,3/4)`, this gives `∫|ζ(2s)|² ≪ Y^{2−4σ}`.
5. AM–GM with `λ = Y^{(3−e)/2}`, `e = 2−4σ`, gives `c_g c₃ Y^{e+1} ≤ (K/2+2A²)Y^{(3+e)/2}`. The two
   exponents differ by `(e−1)/2 = 1/2 − 2σ > 0`, so this fails for large `Y`.

The 3/5 pointwise bound (`rankinSelberg_exact`) is still used, but only inside `conv_of_one_sided`
(Landau). It is not used in the `L¹ → L²` conversion that limited the old route to
`2·3/8 − 3/5 = 3/20`.

## 3. Files

| file | content | lines |
|---|---|---|
| `Conj.lean` | `riemannZeta_conj`, `norm_riemannZeta_conj`, `riemannZeta_ofReal_eq_re` | 69 |
| `Tail.lean` | `hT`, `fourier_hT`, `integrable_hT`, `memLp_hT`, `integral_sq_hT_le`, `tail_L2` | 132 |
| `Error.lean` | `Pz`, continuity lemmas, `err_pt`, `ceil_bounds`, `err_L2` | 175 |
| `MeanValue.lean` | `bσ`, `diag_close`, `offdiag_le`, `poly_L2`, `sq_compare`, `H_ceil_le`, `mean_value_minus` | 331 |
| `Zeta.lean` | goal-(1) headlines, `Eσ`, `Eσ_two_mul`, `Eσ_div_le` | 215 |
| `ZetaLeft.lean` | `norm_zeta_fe_le`, `zeta_dyadic_upper`, `zeta_two_s_mean_sq` | 196 |
| `Rankin.lean` | `gamma_ratio_lower'`, `Zf_first_moment'` (copies), `norm_mellin_le`, `quarter_pt`, `false_of_conv_quarter`, `rs_omega_pm_quarter`, cusp-form and `τ` headlines | 628 |
| `Main.lean` | imports, `#print axioms` | 37 |

Reused results:

- `RankinOmega`: `zeta_formula`, `zeta_formula_large`, `IN`, `gN`, `norm_IN_le`,
  `differentiableAt_IN`, `norm_sum_cpow_eq`, `Zf`, `Zf_tail`, `Zf_horiz`, `differentiableAt_Zf`,
  `amgm_aux`, `exists_first`, `coeffSq_discriminant`, `discriminant_ne_zero'`, `norm_invGamM`.
- `MeanSquare`: `mv_poly`, `dpoly`, `H_le_one_add_log`.
- `TauOmegaPartial.plancherel_of_integrable`.
- `RankinOmegaPM`: `Lam_eq_mellin_conv`, `conv_of_one_sided`, `Rf_re_of_one_lt`, `hR_of_nat`.
- `RankinLandau.norm_Gamma_ratio_unif'`, `KernelPhase.rect_diff`, `RankinExact.rankinSelberg_exact(_general)`.

## 4. Gaps, and what is not claimed

- **Sharp error term.** The classical `O(T^{2−2σ}log T)`, and the second main term in
  `∫|ζ(σ+it)|² = ζ(2σ)T + (2π)^{2σ−1}ζ(2−2σ)T^{2−2σ}/(2−2σ) + …` for `1/2 < σ < 1`, are not
  formalized. The proved error `T^{3/2−σ}` is enough for the asymptotic and for goal (2). Estimate
  to do it: 300–600 lines, via an explicit computation of the cross term `∫P·N^{1−s}/(s−1)` and the
  tail.
- **σ = 1/2.** `∫_0^T|ζ(1/2+it)|² ~ T log T` (Hardy–Littlewood) is not attempted. Here
  `T^{2−2σ} = T`, so the route above gives only `O(T log²T)`. That bound would follow at `σ = 1/2`
  with the same proof if `σ₀ = 1/2` were allowed: the diagonal term needs `2σ > 1`, so `ζ(2σ)` is
  replaced by `∑_{n≤T}1/n`.
- **Ω± exponent.** `1/4 − ε` is now formal. Nothing is claimed at `β = 1/4`. The conjectured
  `Ω±(x^{3/8})` needs the degree-4 Voronoi `L²` expansion (`RANKIN_OMEGA_PM.md` §5).
- `gamma_ratio_lower'` and `Zf_first_moment'` are verbatim copies of the existing proofs with a
  wider hypothesis range. The existing files were not edited.
- **Numerics (level 4)** were not run (no `mpmath` in the environment).

## 5. Literature (from memory; attributions not checked)

- Hardy–Littlewood (1918, 1922) and Landau: `∫_0^T|ζ(σ+it)|²dt ~ ζ(2σ)T` for `σ > 1/2`.
  Titchmarsh, *Theory of the Riemann zeta-function*, Thm 7.2 and §7.2–7.4 (error term), and Ivić,
  *The Riemann zeta-function*, Ch. 1.
- Montgomery–Vaughan (1974), the mean value theorem for Dirichlet polynomials. The repo uses a weak
  form, `6 H_N ∑ n|bₙ|²`.
- Rankin–Selberg Ω results: Ivić (around 1990), `Ω(x^{3/8})`. The signed `Ω±(x^{1/4−ε})` via
  Landau plus mean squares is the paper argument recorded in `RANKIN_OMEGA_PM.md` §2.
