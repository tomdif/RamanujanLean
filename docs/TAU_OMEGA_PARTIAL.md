# `∑_{n≤x} τ(n) = Ω(x^{23/4})`: the exact Ω-exponent for cusp-form partial sums

Lean: `RamanujanTau/TauOmegaPartial/` (8 files, about 1200 lines). No `sorry`, no `native_decide`,
no new axiom, no named hypothesis. Build with
`nice -n 10 lake build RamanujanTau.TauOmegaPartial.Main` (exit 0). `#print axioms` on every
headline gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1).** Deligne is not used.

## 1. Statements

```lean
-- RamanujanTau.TauOmegaPartial
theorem tau_partial_sum_omega :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ ((23 : ℝ) / 4) ≤ |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)|

theorem tau_partial_sum_not_isLittleO :
    ¬ (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ ((23 : ℝ) / 4))

-- every nonzero level-one cusp form, every weight k
theorem cuspForm_partial_sum_omega (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) ≤ ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖

theorem cuspForm_partial_sum_not_isLittleO (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ¬ (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n) =o[atTop]
      (fun x : ℝ => x ^ (((k : ℝ) - 1) / 2 + 1 / 4))
```

The exponent is exact: there is no `ε` loss and no logarithm. Together with
`TauPartialSumsSharp.tau_partial_sum_sharp` (`≪ x^{59/10+ε}`), the true order of `∑_{n≤x} τ(n)`
has exponent in `[23/4, 59/10]`. The conjectured value is `23/4 + ε`.

Reusable intermediate results (all level (1)):

```lean
theorem plancherel_of_integrable {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    MemLp (𝓕 h) 2 ∧ ∫ ξ, ‖𝓕 h ξ‖ ^ 2 = ∫ u, ‖h u‖ ^ 2          -- Plancherel on L¹ ∩ L²
theorem mellin_A_eq (f) (hk : 1 ≤ k) (hα : 0 ≤ α) (hX : ∀ x ≥ X0, ‖A f x‖ ≤ c0 * x ^ α)
    (hw : α < w.re) : mellin (A f) (-w) = fL f w / w            -- ∫ A(x) x^{-w-1} dx = L(f,w)/w
theorem fe_lower (f) (hk : 3 ≤ k) : ∃ c > 0, ∀ σ t, (k-1)/2 ≤ σ → σ ≤ k/2 →
    c * (1+|t|)^(k-2σ) * ‖fL f (k - (σ+it))‖ ≤ ‖fL f (σ+it)‖
theorem first_moment ... : ∃ c3 > 0, ∃ Y0 ≥ 1, ∀ σ' ∈ [k/2+1/8, k/2+1/4], ∀ Y ≥ Y0,
    c3 * Y ≤ ∫ y in Y..2Y, ‖fL f (σ' + iy)‖^2                  -- uniform in σ'
theorem block_lower ... : ∃ K1 > 0, ∃ Ξ0 ≥ 1, ∀ δ ∈ (0, 1/16], ∀ Ξ ≥ Ξ0,
    K1 * (2Ξ)^(-4δ) ≤ ∫ ξ in Ξ..2Ξ, ‖L(f, σ-2πiξ)/(σ-2πiξ)‖^2,   σ = (2k-1)/4 + δ
```

(`first_moment` and `block_lower` take `hk : 12 ≤ k` and the least index `m` with `a_f(m) ≠ 0`.)

## 2. Choice of route

Write `α = (k−1)/2 + 1/4 = (2k−1)/4` and `A(x) = ∑_{n≤x} a_f(n)`.

* **(a) Voronoi / Cramér mean square** `∫_X^{2X} A² ≫ X^{k+1/2}`. This needs the truncated
  Voronoi formula with an `L²`-controlled error and a Montgomery–Vaughan-type diagonal
  extraction for `∑ a(n) n^{−3/4} cos(4π√(nx) − ·)`. `TauPartialSumsSharp` has the exact dual
  expansion only for Riesz means of order `r ≥ 2`. Getting down to order 0 with an `L²` error
  needs new kernel work. This route was rejected as the longest.
* **(b) Landau–Mellin–Plancherel.** This is the route used. The brief's worry about the exponent
  resolves as follows. The functional equation gives
  `|L(σ+it)|² ≍ |t|^{2(k−2σ)} |L(k−σ+it)|²`, with the exponent **doubled**. So
  `∫ |L(σ+it)|²/|t|² dt` converges exactly when `σ > k/2 − 1/4 = α`. It diverges like
  `1/(σ−α)` as `σ ↓ α`, which is precisely the exponent of the Ω statement. There is no
  `ε`-loss, provided the lower bound for the right-hand side is **uniform in σ**. That
  uniformity is the one new analytic input (`first_moment`). It cannot come from the per-`σ`
  limit theorems in `MeanSquareFull`, whose `T₀(σ)` is uncontrolled.
* Smoothing first (Riesz mean `B = ∫A`) does **not** work. The Mellin transform of `B` decays two
  powers faster, so Plancherel only detects `B = Ω(x^{α+1/2})`, which is too weak for `A`.
  Plancherel had to be applied to the discontinuous `A` itself. Mathlib's `L²` Fourier transform
  (`Lp.fourierTransformₗᵢ`) is not identified with `𝓕` on `L¹ ∩ L²` in Mathlib; we prove that
  identification (`Plancherel.lean`).

## 3. Proof

Assume, for contradiction, that `‖A(x)‖ ≤ c₀ x^α` for `x ≥ X₀ ≥ 1`, where `c₀ = √K₂/4` and `K₂`
comes from step 6. Let `σ = α + δ` with `0 < δ ≤ 1/16`.

1. **Mellin transform** (`Mellin.lean`). For `Re w > (k+1)/2`, Abel summation (Mathlib
   `LSeries_eq_mul_integral'`) gives `∫₀^∞ A(x)x^{−w−1}dx = L(f,w)/w`. Under the hypothesis, the
   left side is holomorphic on `Re w > α` (`mellin_differentiableAt_of_isBigO_rpow`, where
   `A = 0` on `(0,1)`). The right side is entire divided by `w`. The identity principle
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) extends the identity to `Re w > α`.
2. **Log scale** (`Fourier.lean`). Let `h_σ(u) = e^{σu} A(e^{−u})`. By `mellin_eq_fourier`,
   `𝓕h_σ(ξ) = L(f, σ−2πiξ)/(σ−2πiξ)`. The hypothesis gives the pointwise bound
   `|h_σ(u)| ≤ c₀e^{δu}` for `u ≤ −log X₀`, and `≤ S = ∑_{n≤X₀}|a(n)|` on `[−log X₀, 0]`. So
   `h_σ ∈ L¹ ∩ L²` and `∫|h_σ|² ≤ c₀²/(2δ) + S² log X₀`.
3. **Plancherel** (`Plancherel.lean`). For `h ∈ L¹ ∩ L²`, `∫|𝓕h|² = ∫|h|²`. The proof has
   three ingredients. First, the `L²` transform of `h` and the function `𝓕h` define the same
   tempered distribution (`Lp.fourier_toTemperedDistribution_eq` and the multiplication formula
   `integral_fourierIntegral_smul_eq_flip`). Second, du Bois-Reymond
   (`ae_eq_of_integral_contDiff_smul_eq`) makes them a.e. equal. Third,
   `Lp.norm_fourier_eq` gives equality of norms.
4. **Functional equation** (`FE.lean`, `fe_lower`). For `(k−1)/2 ≤ σ ≤ k/2`,
   `|L(σ+it)| ≥ c(1+|t|)^{k−2σ}|L(k−σ−it)|`, with `c` uniform. This uses `fL_functional_equation`
   and the uniform Stirling ratio `RankinLandau.norm_Gamma_ratio_unif'`.
5. **Uniform mean square on `k − σ`** (`FirstMoment.lean`, `first_moment`). Let `m` be the least
   index with `a(m) ≠ 0`, and put `G(s) = L(f,s)m^s`.
   - On a far line `Re s = c`, `|G − a(m)| ≤ |a(m)|/2` uniformly in `Im s` (`tail_small`).
     Hence `|∫_Y^{2Y} G(c+iy)dy| ≥ |a(m)|Y/2`.
   - The rectangle to `Re s = σ'` (`KernelPhase.rect_diff`) costs two horizontal sides. Each is
     `≪ Y^{7/8}` by convexity (`fL_line`, `fL_bounded_of_gt`), uniformly for
     `σ' ∈ [k/2+1/8, c]`.
   - Cauchy–Schwarz (`sq_integral_le`) gives `∫_Y^{2Y}|L(σ'+iy)|² ≥ c₃Y` for `Y ≥ Y₀`, with
     `c₃` and `Y₀` independent of `σ'`.
6. **Blocks** (`Block.lean`, `block_lower`). Combine 4 and 5 at `σ' = k−σ ∈ [k/2+3/16, k/2+1/4)`,
   using `2(k−2σ) = 1−4δ` and `|σ−2πiξ| ≤ (k+2π)ξ`. This gives
   `∫_Ξ^{2Ξ} |𝓕h_σ|² ≥ K₁(2Ξ)^{−4δ}`.
7. **Assembly** (`Omega.lean`). Sum the blocks `[2^jΞ₀, 2^{j+1}Ξ₀]` for `j < J = ⌈1/(4δ)⌉`.
   Each block is `≥ K₂ = K₁/(4Ξ₀)` (`dyadic_weight`). Together with Plancherel and step 2:
   `K₂/(4δ) ≤ c₀²/(2δ) + S² log X₀`. Since `c₀² = K₂/16`, this reads
   `K₂/4 ≤ K₂/32 + δ S² log X₀`. That is false for `δ ≤ K₂/(8(S² log X₀ + 1))`.

## 4. Files

| file | content | lines |
|---|---|---|
| `Plancherel.lean` | `integral_norm_sq_Lp`, `plancherel_of_integrable` | 81 |
| `Mellin.lean` | `A`, `A_of_lt_one`, `measurable_A`, `norm_A_le`, `locallyIntegrableOn_A`, `mellin_A_eq_of_large`, `mellin_A_eq` | 122 |
| `Fourier.lean` | `hfun`, `fourier_hfun`, `G1`/`G2` majorants, `norm_hfun_le`, `integral_G2`, `hfun_L1L2` | 163 |
| `FE.lean` | `fe_lower`, `rpow_aux`, `tail_small` | 187 |
| `FirstMoment.lean` | `sq_integral_le`, `horiz_bound`, `first_moment` | 233 |
| `Block.lean` | `Fs`, `continuous_Fs`, `block_lower` | 147 |
| `Omega.lean` | `exists_first_coef`, `dyadic_weight`, `cuspForm_partial_sum_omega` | 174 |
| `Main.lean` | `cuspForm_partial_sum_not_isLittleO`, `tau_partial_sum_omega`, `tau_partial_sum_not_isLittleO`, `#print axioms` | 92 |

Reused: `HeckeConvexGeneral` (`fL`, `coef`, `fL_entire`, `fL_eq_LSeries`,
`fL_functional_equation`, `fC_bound`, `fL_line`, `fL_bounded_of_gt`,
`exists_sum_norm_coef_le`, `summable_norm_coef_div_rpow`, `LSeriesSummable_coef`,
`eq_zero_of_lt_twelve`, `coef_discriminant`), `RankinLandau.norm_Gamma_ratio_unif'`,
`KernelPhase.rect_diff`, `RankinSelbergGeneral.exists_coeff_ne_zero`,
`HardyZerosGeneral.discriminant_ne_zero'`. The public entry point is included in the `RamanujanTau.lean` import graph.

## 5. Gaps and possible extensions

- **Ω±** (sign changes of `A(x)` at height `x^α`) is not proved. The method gives only `|A|`.
  Ω± needs either a positivity argument on the Voronoi series or Landau's theorem applied to
  `∫A x^{−s−1} ± c/(s−α)`. The latter fails here because `L` has no real singularity.
- **No extra factor.** Hafner–Ivić obtain an Ω± result with an extra `exp(D(log log x)^{1/4}…)`
  factor, using Deligne and Diophantine approximation. That is out of reach of this method.
- The constant `c` is implicit (it comes from `fe_lower`, `tail_small`, `first_moment`). The
  Cramér-type mean-square asymptotic `∫_1^X A² ~ C X^{k+1/2}` is not proved. Under the
  contradiction hypothesis the argument shows `∫_1^∞ |A|² x^{−2σ−1} dx ≫ 1/(σ−α)` as `σ ↓ α`.
  This is the Mellin form of a lower mean-square bound, but it is not stated as a standalone
  theorem.
- The upper bound remains `59/10 + ε` (see `TAU_PARTIAL_SUMS_SHARP.md`). The gap `[23/4, 59/10]`
  is untouched from above.

## 6. Literature

- E. Landau (1915–1924): Ω-theorems for lattice-point problems. Hardy (1915) proved
  `P(x) = Ω(x^{1/4})` for the circle problem.
- J. L. Hafner, A. Ivić, *On sums of Fourier coefficients of cusp forms*, Enseign. Math. 35
  (1989): `A(x) = Ω±(x^{k/2−1/4}·…)` and the mean square `∫_1^X A² = C X^{k+1/2} + …`.
- The Plancherel-type Ω argument (mean square of the Mellin transform near the abscissa) is
  standard (Landau; see e.g. Ivić, *The Riemann Zeta-Function*, Ch. 13).

These attributions are from memory and were not checked against the sources.
