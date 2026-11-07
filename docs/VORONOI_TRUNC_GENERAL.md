# Truncated Voronoi in `L²`, the Cramér limit and exact `Ω±` for every level-one cusp form

> **Update (2026-11-06):** the complex-coefficient and a(1) = 0 gaps are closed in `VoronoiTruncComplete`; see [VORONOI_TRUNC_COMPLETE](VORONOI_TRUNC_COMPLETE.md).

Lean: `RamanujanTau/VoronoiTruncGeneral/` (10 files, about 3550 lines). No `sorry`, no `native_decide`,
no new axiom, no named hypothesis. Build with `nice -n 10 lake build RamanujanTau.VoronoiTruncGeneral.Main`
(exit 0). `#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
**Evidence level (1).** Deligne is not used. The directory is not imported by `RamanujanTau.lean`.

This generalizes `RamanujanTau/VoronoiTrunc/` (`docs/VORONOI_TRUNC.md`, `τ`, weight 12) to every
nonzero `f ∈ S_k(SL₂(ℤ))` with real coefficients. That closes the "Only `τ`" gap listed there.

## 1. Statements

Notation: `a(n) = (coef f n).re`, with `hreal : ∀ n, (coef f n).im = 0`, and
`S(x) = Σ_{1≤n≤x} a(n)`.

```lean
-- namespace RamanujanTau.VoronoiTruncGeneral   (Main.lean)
theorem cusp_voronoi_truncated_L2 (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re -
          x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (coef f n).re * (n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop (𝓝 0)

theorem cusp_voronoi_truncated_L2_rate ... : ∃ C ≥ 0, ∀ X ≥ 144,
    ∫ x in X..2X, (S x − V_{⌊X^θ⌋} x)^2 ≤ C X^{k+1/2} (X^{−1/16} + Σ_{n>⌊X^θ⌋} a(n)² n^{−(k+1/2)})

theorem cusp_cramer (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hreal : ∀ n, (coef f n).im = 0) :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop
      (𝓝 ((∑' n : ℕ, (coef f n).re ^ 2 * (n : ℝ) ^ (-((k : ℝ) + 1 / 2))) / ((4 * k + 2) * π ^ 2)))

theorem cusp_omega_pm_exact (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) (h1 : (coef f 1).re ≠ 0) {c : ℝ}
    (hc : c < |(coef f 1).re| / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ∧
      (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4))

theorem eigenform_omega_pm_exact (f) (hf : EigenformEdge.IsNormalizedEigenform f)
    {c} (hc : c < 1 / (2 * π * √2)) : -- same conclusion
theorem cusp_partial_sum_omega_pm_exact ... -- the same, for arbitrarily large x (no dyadic window)
theorem kernel_asymp_even {m} (hm : 1 ≤ m) {L} (hL : 0 < L) :
    |(-1) ^ m * Ik (2 * m) L - cos (2L − π/4)/√(πL)| ≤ Ck (2m)/(πL)
```

In words:

- **(A)** The truncated Voronoi formula holds in mean square on every dyadic block:
  `X^{−(k+1/2)} ∫_X^{2X} (S − V_{X^θ})² → 0` for `0 < θ ≤ 1/4`. Here
  `V_N(x) = x^{(k−1)/2+1/4}/(π√2) Σ_{n≤N} a(n) n^{−(k/2+1/4)} cos(4π√(nx) − π/4)`.
  The remainder is `≪ X^{k+1/2}(X^{−1/16} + Σ_{n>N} a(n)² n^{−(k+1/2)})`.
- **(B)** The limit `∫₁^X S² ~ (B_f/((4k+2)π²)) X^{k+1/2}` exists, with
  `B_f = Σ a(n)² n^{−(k+1/2)}`. For `k = 12` the constant is `B/(50π²)`, as in `tau_cramer`.
- **(B′)** Exact `Ω±(x^{(k−1)/2+1/4})` in every dyadic interval, for real `f` with `a(1) ≠ 0`.
  The constant is any `c < |a(1)|/(2π√2)`. For a normalized eigenform (`a(1) = 1`) this is
  `c < 1/(2π√2)`.

`hf : f ≠ 0` only serves to force `k` even and `k ≥ 12` (`exists_half`: odd weight gives `f = 0` by
`HardyZerosGeneral.eq_zero_of_odd`, and `k < 12` gives `f = 0` by `HeckeConvexGeneral.eq_zero_of_lt_twelve`).
For `f = 0`, (A) and (B) hold trivially, but they are not stated in that case.

### The phase and the constant

- **Phase.** Put `k = 2m`. The modular relation `f(−1/τ) = τ^k f(τ)` at `τ = iz` reads
  `D(z) = (iz)^{−k} D(1/z) = (−1)^m z^{−2m} D(1/z)`, where `D(z) = Σ a(n) e^{−2πnz}`
  (`Dq_modular_cusp`). The Schläfli kernel therefore carries the sign `(−1)^m`:
  `k_j(n,x) = (−1)^m (x/n)^{(2m+j)/2} I_{2m+j}(2π√(nx))` (`kB_eq_Ik`). The saddle point gives
  `(−1+i) i^{−(2m+1)} = (−1)^m (1+i)`, so `I_{2m}(L) = (−1)^m cos(2L − π/4)/√(πL) + O(1/L)`
  (`Ik_asymp_even`). This matches `J_{2m}(2L) ~ cos(2L − mπ − π/4)/√(πL)`. The two signs
  cancel, so the phase is `−π/4` with sign `+` for **every** even `k`, whether `k ≡ 0` or `k ≡ 2 (mod 4)`.
- **Constant.** `V_N² ≈ x^{k−1/2} (1/(2π²)) Σ a(n)² n^{−(k+1/2)} cos²` has mean
  `x^{k−1/2} B_f/(4π²)`. Integrating, `∫₁^X x^{k−1/2} = X^{k+1/2}/(k+1/2)`, which gives
  `B_f/(4π²(k+1/2)) = B_f/((4k+2)π²)`.

## 2. Structure of the proof

The analytic core is proved for an abstract real sequence `a` and weight `2m` satisfying
`VData m a` (`Data.lean`). The fields are:

- `two_le : 2 ≤ m`;
- `zero : a 0 = 0`;
- `modular`: `D(z) = (−1)^m (z^{2m})⁻¹ D(z⁻¹)` for `Re z > 0`;
- `rankin`: `Σ_{n≤N} a(n)² ≤ B N^{2m}`.

From these, `Data.lean` derives:

- `|a(n)| ≤ A n^{m+1}`;
- `Σ_{n≤N}|a(n)| ≤ A N^{m+1/2}`;
- `Σ|a(n)| n^{−β} < ∞` for `β > m+1/2`;
- `Σ a(n)² n^{−β} < ∞` for `β > 2m`, via `LSeriesSummable_of_sum_norm_bigO`.

`VData.smul` shows that `VData` is stable under scaling. `Cusp.lean` (`vdata_of_cusp`) proves
`VData` for a cusp form, using `hasSum_qExpansion`, `SlashInvariantForm.slash_action_eqn''` at `S`, and
`HeckeConvexGeneral.exists_sum_sq_div_le` / `sum_sq_le` (Rankin–Selberg).

The proof is the `τ` proof of `docs/VORONOI_TRUNC.md` §2, with every weight-dependent exponent
made symbolic in `m`. The parameters stay the same: `r = 12`, `h = X^{7/32}`, `M = ⌊X^{5/8}⌋`,
`N = ⌊X^θ⌋`. Every exponent shifts by the same amount `m − 6`, so the relative savings
(`X^{−1/16}`, `X^{−1/8}`, …) do not depend on `k`. The coefficient bound `|a(n)| ≪ n^{m+1}` makes
the second interchange in `dual_W` work for `r ≥ 5` exactly as `|τ(n)| ≪ n^7` did.

(B′) is proved for `a(1) = 1` (`omega_plus/minus`, Ingham's kernel on frequency 1). The case
`a(1) ≠ 0` reduces to it by applying it to `a/a(1)` (`VData.smul`). When `a(1) < 0` the two
signs swap.

## 3. Files

| file | content |
|---|---|
| `Data.lean` | `Dq`, `VData`, derived bounds (`sum_abs_le`, `abs_le`, `summable_abs_div`, `summable_sq`), `VData.smul` |
| `Cusp.lean` | `hasSum_coef_exp`, `cusp_S`, `Dq_modular_cusp`, `vdata_of_cusp`, `coef_eq_re` |
| `Dual.lean` | `coef_exp_sum`, `sg`, `kB` (with sign `(−1)^m`), `dual_W`, `kB_rel`, `kB_eq_Ik`, `DkC_kB`, `DkC_WC_eq` |
| `MeanValue.lean` | `mean_value` with weight `y^p√y` and bound `b^{p+1}√M(2H_M+1)Σc²` (any `p`) |
| `Est.lean` | `lead_even`, `Ik_asymp_even`, `mK`, `kB_zero_sub_main`, `norm_kB_top_le`, Rankin-trick sums, Lipschitz bound, short sums |
| `Assembly.lean` | `Sre`, `bco`, `Vth`, `Sh`, bracket, head/tail split, `pointwise_bound`, `L2_main` |
| `Final.lean` | parameter bounds `B2_bound` (`X^{m−5/16}`), `B4_bound` (`X^{m−9/32}`), `T1_bound`, `mv_bound`, `voronoi_L2_bound`, `voronoi_L2` |
| `Cramer.lean` | dyadic mean square of `V_N`, transfer to `S`, dyadic summation, `cramer_core` |
| `Omega.lean` | Ingham kernel, `omega_core`, `omega_plus`, `omega_minus` (for `a(1) = 1`) |
| `Main.lean` | cusp-form headlines, `#print axioms` |

Reused unchanged from `VoronoiTrunc/` (weight-free): `Kernel.lean` (`Ak_asymp`, `Ik_bound`,
`Ck`, `sqrt_identity`), `Contour.lean` (`lineInt_eq_Ik`), `Laplace.lean` (`laplace_inv`), the line
`zl` and the kernel family `gE`/`kE`/`hasDerivAt_kE`, `riesz_term`, `It` with `Avg.lean`, and
`DkC_summable`. Also reused: `TauPartialSumsSharp` (`WC`, `DkC`, `bracket_signed`, …),
`HeckeConvexGeneral` (`coef`, Rankin bounds, `eq_zero_of_lt_twelve`), `HardyZerosGeneral.eq_zero_of_odd`,
and `EigenformEdge.IsNormalizedEigenform`.

## 4. Numerical checks (evidence level (4); `scripts/voronoi_trunc_general/`)

`check_general.gp` (output in `check_general.out`) uses `f = ΔE₄` (k = 16, m = 8) and `f = ΔE₆`
(k = 18, m = 9, the case `k ≡ 2 mod 4`).

- **Kernel sign.** `I_ν = J_ν(2L)` for `ν = 16, 18`, to about 9 digits at `L = 5, 20` and 6 digits at `L = 45` (quadrature error). For large `L`,
  `J_ν(2L)√(πL)` approaches `(−1)^{ν/2} cos(2L − π/4)`: for example `ν = 18`, `L = 2000`
  gives `0.99998` against `0.99946`.
- **Sign of the main term.** The table shows the mean of `(S − V_N)²/x^{k−1/2}` over `[X, 2X]` for
  both signs of `V_N`:

  | k | X | N | sign `+` (proved) | sign `−` | mean `S²/x^{k−1/2}` | `B_f/(4π²)` |
  |---|---|---|---|---|---|---|
  | 16 | 2000 | 20 | 0.00806 | 0.20714 | 0.05726 | 0.056985 |
  | 16 | 8000 | 120 | 0.00308 | 0.21854 | 0.05679 | |
  | 18 | 2000 | 20 | 0.01051 | 0.23945 | 0.06666 | 0.066829 |
  | 18 | 8000 | 120 | 0.00410 | 0.25856 | 0.06745 | |

  So the `+` sign (phase `−π/4`, no `(−1)^{k/2}`) is correct for both residues of `k` mod 4.
- **Cramér.** `X^{−(k+1/2)}∫₁^X S²` is `0.00347 / 0.00332` at `X = 4000 / 16000` for `k = 16`,
  against `B_f/(66π²) = 0.003454`. For `k = 18` it is `0.00346 / 0.00372`, against
  `B_f/(74π²) = 0.003612`.
- **Ω±.** On `[8000, 16000]`, `max S/x^{(k−1)/2+1/4} = 0.71 / 0.81` and `min = −0.69 / −0.76`
  (for k = 16 / 18). Both have absolute value above `1/(2π√2) = 0.1125`.

## 5. Gaps

- **Complex coefficients.** The statements need real `a(n)`. Every level-one form is
  `f = g + ih` with `g, h` real cusp forms, because the space has a rational basis. The `L²`
  statement for complex `f` would need a complex version of `mean_value` (Hermitian off-diagonal
  terms), or this decomposition. Neither was done.
- **`a(1) = 0` in (B′).** `cusp_omega_pm_exact` needs `a(1) ≠ 0`. For a general real `f ≠ 0`, the
  same argument should work with Ingham's kernel on the first nonzero frequency `n₀`: the
  off-diagonal frequencies `|√n − √n₀| ≥ 1/(√N+√n₀)` cost an extra `X^{1/8}`, which still gives `o(X)`.
  That would give `c < |a(n₀)| n₀^{−(k/2+1/4)}/(2π√2)`. It was not written out. Normalized
  eigenforms, and in particular every form of a one-dimensional `S_k`, are covered.
- **Range of `N`, pointwise Voronoi, sharp `Ω±` constant, higher moments.** These are as for `τ`
  (`docs/VORONOI_TRUNC.md` §4): `θ ≤ 1/4` only, `L²` only, constant `1/(2π√2)` not sharp, and no
  fourth moment.

## 6. Literature (from memory, not checked against sources)

- Wilton (1929) and Chandrasekharan–Narasimhan (1962): the Voronoi formula for cusp-form
  coefficients, with phase `cos(4π√(nx) − π/4)`.
- Cramér (1922) and Tong (1956): mean squares.
- Ingham (1942): `Ω±`.
- Hafner–Ivić (1989): `Ω±` with a growing factor, using Deligne.

No novelty claim is made.
