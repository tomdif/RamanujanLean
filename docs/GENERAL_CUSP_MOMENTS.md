# Good's mean-square asymptotic for every nonzero level-one cusp form

Module: `RamanujanTau/GeneralCuspMoments/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.GeneralCuspMoments.Main` (exit 0).

## Evidence levels

| result | level |
|---|---|
| (1) `∫_0^T |L(f,k/2+it)|² dt ~ c_f T log T`, `c_f = 2·rsConst f`, every `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0` (Good 1982) | **(1) Lean, axiom-clean** |
| `c₁ T log T ≤ ∫_0^T |L(f,k/2+it)|² ≤ c₂ T log T` for `T ≥ T₀` | **(1) Lean, axiom-clean** |
| weighted form `κ^k ∫|Λ(f,k/2+it)|²e^{2βt}dt / log(1/κ) → 12‖f‖²`, `κ = cot β → 0⁺` | **(1) Lean, axiom-clean** |
| Laplace form `λ^k ∫_0^∞ t^{k−1}e^{−λt}|L|² / log(1/λ) → (2π)^{k−1}2^k·12‖f‖²` | **(1) Lean, axiom-clean** |
| exact weighted Parseval identity for `f` | **(1) Lean, axiom-clean** |
| `f = Δ`: constant equals `CriticalMeanSquareAsymp.cDelta` | **(1) Lean, axiom-clean** |
| (2) Hafner `N₀(T) ≫ T` for general `f` | **done** in [HAFNER_GENERAL](HAFNER_GENERAL.md) (2026-11-05) |

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every headline (see the end
of `Main.lean`). No named hypotheses, no `sorry`, no `native_decide`, no `axiom`. Real
coefficients are **not** needed for (1).

## Headlines (`namespace RamanujanTau.GeneralCuspMoments`, `k : ℕ`)

```lean
/-- Good's constant: twice the Rankin–Selberg constant of `RankinSelbergGeneral` /
`RankinExact.rankinSelberg_exact_general`. -/
noncomputable def cF (f : CuspForm 𝒮ℒ (k : ℤ)) : ℝ := 2 * RankinSelbergGeneral.rsConst f

theorem cF_eq (f) : cF f = 2 * (3 / π * (4 * π) ^ k * RankinSelbergGeneral.petNormSqF f /
    (Nat.factorial (k - 1) : ℝ))
theorem cF_pos (f) (hf : f ≠ 0) : 0 < cF f

theorem fL_critical_mean_square_asymptotic (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2) / (T * Real.log T))
      atTop (𝓝 (cF f))

theorem fL_critical_mean_square_two_sided (f) (hf : f ≠ 0) :
    ∃ c₁ c₂ T₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 1 < T₀ ∧ ∀ T ≥ T₀,
      c₁ * (T * Real.log T) ≤ ∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2 ∧
      ∫ t in Icc 0 T, ‖fL f ((k : ℂ) / 2 + t * I)‖ ^ 2 ≤ c₂ * (T * Real.log T)

theorem fL_weighted_asymptotic (f) (hf : f ≠ 0) :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ k *
      (∫ t : ℝ, ‖heckeLambda f ((k : ℂ) / 2 + t * I)‖ ^ 2 * Real.exp (2 * β * t)) /
        Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
      (𝓝 (12 * RankinSelbergGeneral.petNormSqF f))

theorem fL_laplace_asymptotic (f) (hf : f ≠ 0) :
    Tendsto (fun l : ℝ => l ^ k / Real.log (1 / l) *
      ∫ x in Ioi (0 : ℝ), x ^ (k - 1) * ‖fL f ((k : ℂ) / 2 + (x : ℂ) * I)‖ ^ 2 *
        Real.exp (-(x * l))) (𝓝[>] 0)
      (𝓝 ((2 * π) ^ (k - 1) * (2 ^ k * (12 * RankinSelbergGeneral.petNormSqF f))))

/-- sanity check: f = Δ gives the constant of `CriticalMeanSquareAsymp` -/
theorem fL_discriminant_critical_mean_square_asymptotic :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T,
      ‖fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I)‖ ^ 2) /
        (T * Real.log T)) atTop (𝓝 RamanujanTau.CriticalMeanSquareAsymp.cDelta)
```

`fL f` is the entire continuation of `∑ a_f(n) n^{−s}` (`HeckeConvexGeneral.fL_eq_LSeries`),
`petNormSqF f = ∫_𝓕 |f|² y^k dx dy/y²`, and
`rsConst f = (3/π)(4π)^k ‖f‖²/(k−1)!` is the constant of
`(1/N)∑_{n≤N} |a(n)|²/n^{k−1} → rsConst f` (`RankinSelbergGeneral.rankinSelberg_asymptotic`)
and of `RankinExact.rankinSelberg_exact_general` (`… = rsConst f · N + O(N^{3/5})`).

Internally everything is stated for weight `k = 2p + 2` (`f : CuspForm 𝒮ℒ ((2p+2 : ℕ) : ℤ)`,
hypothesis `12 ≤ 2p+2`); the headline reduces to that case by `HardyZerosGeneral.eq_zero_of_odd`
and `eq_zero_of_lt_twelve` (`exists_weight_eq`).

## Proof (what changed relative to the Δ proof)

The Δ proof (`CriticalMeanSquareAsymp`, `docs/CRITICAL_MEAN_SQUARE_ASYMP.md`) was split into
weight-free abstract parts and an `f`-specific part.

1. **Abstract ray asymptotic** (`Ray.lean`). Hypotheses `RayHyp p D c₀` on any `D : ℂ → ℂ`:
   holomorphic on `ℍ`, `1`-periodic, `|D(z)|(Im z)^{p+1} ≤ M e^{−π Im z}`, and
   `y^{2p+2}∫₀¹|D(x+iy)|²dx → c₀`. The Cauchy-estimate Lipschitz bound (`RayHyp.lip`), the sharp
   blocks (`block_sharp`, with `(x+1)^{N+1} − x^{N+1} ≤ 2^{N+1}x^N` replacing the binomial
   expansion for `N = 11`), the summation (`sum_sharp`), the cusp tail and the `[s,1]` edge
   (`ray_decomp`), and the logarithmic average (`CriticalMeanSquareAsymp.harm_tendsto`, reused)
   give `ray_tendsto`.
2. **Cusp-form input** (`CuspRay.lean`).
   * `exists_cusp_bound`: `|f(z)| y^{p+1} ≤ M e^{−πy}` on all of `ℍ`, from
     `RankinSelbergGeneral.exists_Gf_le` (`|f|²y^k` bounded) and
     `HardyZerosGeneral.cusp_bound` (`|f| ≤ A e^{−2πy}` for `y ≥ Y`).
   * `Phi_neg`: `Φ(−w) = i^k Φ(w)` (from `Zc_neg`, the functional equation), so `|Φ|` is even;
     this replaces `Phis_six_neg` and handles the root number `−1` for `k ≡ 2 mod 4`
     without any realness hypothesis.
   * `norm_gF_le` + `CriticalMeanSquare.maj` (reused): the Fourier side is integrable.
   * `weighted_parseval_f`: `CriticalMeanSquare.parseval` (reused) applied to
     `F(t) = Λ(f,k/2+it)e^{βt}`, with `𝓕F(ξ) = Φ(2πξ+iβ) = 2πG(2πξ+iβ)`
     (`HardyZerosGeneral.Phi_eq_strip`).
   * `rayHyp_f`: `D = f` satisfies `RayHyp` with `c₀ = (3/π)‖f‖²`; the horocycle limit is
     `RankinSelbergGeneral.horocycle_tendsto` (`hD_eq_horoMean`).
   * `weighted_asymptotic_f`: two mirror rays, `2π·2·(3/π)‖f‖² = 12‖f‖²`.
3. **Gamma weight** (`Gamma.lean`). For every `p`:
   `|Γ(p+1+it)|² = ∏_{j<p}((j+1)²+t²) · πt/sinh(πt)` (`norm_Gamma_sq`, induction on `p` from
   `Γ(1+it)Γ(1−it) = πt/sinh πt`). Kernel `kG p t = P_p(t)·(πt/sinh πt)/(2π)^{2p+2}·e^{πt}` with
   `kG ≥ t^{2p+1}/(2π)^{2p+1}` and `kG(2π)^{2p+1}/t^{2p+1} → 1` (`tendsto_kG_ratio`,
   `∏(1+(j+1)²/t²) → 1` by `tendsto_finsetProd`). `k` is even, so `k/2` is an integer and the
   product formula is exact; no Stirling is needed.
4. **Laplace transform** (`CuspLaplace.lean`). As in the Δ case; integrability of
   `|Λ(f,k/2+it)|²e^{2βt}` comes from `HardyZerosGeneral.heckeLambda_line_decay`, and
   integrability of `x^{k−1}|L|²e^{−λx}` from `kG_ge` (so the convexity bound is not needed).
5. **Abstract Tauberian step** (`Tauber.lean`). `LapHyp g n K`: `g ≥ 0` continuous and
   `λ^{n+1}∫_0^∞ x^n g e^{−λx}/log(1/λ) → K`. Then `∫_0^T g/(T log T) → K/n!`
   (`tendsto_of_laplace`). **New:** the a-priori bound `∫_0^T g ≤ C T log T`
   (`upper_of_laplace`) is derived from the Laplace bound itself
   (`g(x) ≤ e T^{−n}x^n g(x)e^{−x/(2T)}` on `[T,2T]`, then dyadic summation), so the
   Hecke–Hafner/Schur upper bound `CriticalMeanSquare.critical_mean_square_upper` is not needed.
   The Karamata part (`CriticalMeanSquareAsymp.KarC.convC_gKQ`, reused) and the sandwich
   `Q_ε(e^{−u}) = max(u,ε)^{−n}` are the Δ argument with `11 → n`.
6. **Constant** (`Kc_div_eq`): `(2π)^{2p+1}2^{2p+2}·12‖f‖²/(2p+1)! = 2·rsConst f`.

## Files

| file | lines | content |
|---|---|---|
| `Gamma.lean` | 182 | `Pq`, `norm_Gamma_sq`, `kG`, `kG_ge`, `kG_le`, `tendsto_kG_ratio` (Mathlib only) |
| `Tauber.lean` | 500 | `LapG`, `LapHyp`, `lap_bound`, `dyadic_of_laplace`, `cum_aux_gen`, `upper_of_laplace`, `QeN`, `Lam_gQN_bounds`, `SCN_bounds`, `tendsto_of_laplace` |
| `Ray.lean` | 622 | `pz`, `HhD`, `RayHyp`, `RayHyp.bounds`, `RayHyp.lip`, `Gsig`, `block_sharp`, `hD`, `sum_sharp`, `integral_change`, `tail_bound`, `ray_decomp`, `ray_tendsto` |
| `CuspRay.lean` | 449 | `exists_cusp_bound`, `Phi_neg`, `norm_Gc_le`, `gF`, `integrable_gF`, `Ff`, `fourier_Ff`, `Ru`, `weighted_parseval_f`, `Ru_even`, `rayHyp_f`, `c0f`, `weighted_asymptotic_f` |
| `CuspLaplace.lean` | 466 | `Lsq`, `fW`, `integrable_fW`, `norm_heckeLambda_sq`, `weight_eq`, `Lap`, `KGL`, `KGL_le`, `weighted_lambda_f`, `Kc`, `laplace_asymptotic_f`, `Kc_div_eq`, `critical_mean_square_asymptotic_f` |
| `Moments.lean` | 132 | `cF`, `cF_eq`, `cF_pos`, `exists_weight_eq`, headlines, Δ corollary |
| `Main.lean` | 34 | imports, `#print axioms` |

Reused unchanged (imported, not edited): `HardyZerosGeneral` (`Zc`, `Phi`, `Gc`, `Fc`,
`Phi_eq_strip`, `Zc_neg`, `cusp_bound`, `Fc_add_one`, `heckeLambda_line_decay`,
`eq_zero_of_odd`), `HeckeConvexGeneral` (`fL`, `heckeLambda_eq_fL`, `fL_entire`),
`RankinSelbergGeneral` (`horocycle_tendsto`, `exists_Gf_le`, `petNormSqF`, `rsConst`,
`rsConst_pos`, `petNormSqF_discriminant`), `CriticalMeanSquare` (`parseval`, `maj`,
`min_le_maj`), `CriticalMeanSquareAsymp` (`KarC`, `Harmonic`, `cDelta`), `EisensteinReal.Karamata`.

## Gaps

* **(2) Hafner's `N₀(T) ≫ T` for general `f`** — *update: now proved in [HAFNER_GENERAL](HAFNER_GENERAL.md).* Original note: The Δ proof
  (`HardyCountHafner`, ~1400 lines, plus `HardyCountLinear.{Windows,Kernel,Main}` and
  `HardyCount.{Window,Contour}`) is Δ-specific in ≈2100 lines: the σ-general Fourier identity
  `Φ_σ = 2πe^{σw}f(ie^w)` for `σ = k/2 + x` (only `σ = k/2` exists in `HardyZerosGeneral`),
  the uniform off-line mean square `∫_T^{2T}|L(f,k/2+x+it)|² ≪ T/x` (needs Stirling from below
  at general `σ`), the horizontal-side area bound, the window kernel `Iw` built from a real `Z`
  (for `k ≡ 2 mod 4` use `Y = Im Z`, odd), and `norm_fL_sub_one_le` far right. No mathematical
  obstruction is visible (the ingredients `integral_Zc_exp`, `Fc_rot_decay`, root-number
  handling and `exists_cusp_bound` above are in place). Estimate: 1500–2500 new lines, one
  focused session. Target statement:
  `fL_critical_zeros_linear f hf hreal : ∃ c T₀, 0 < c ∧ ∀ T ≥ T₀, ∃ S : Finset ℝ,
   (∀ t ∈ S, 0 < t ∧ t ≤ T ∧ fL f (k/2 + t*I) = 0) ∧ c * T ≤ S.card`.
* The secondary term `2c_f T(log(T/2πe)+C)` is not formalized (needs a rate in the horocycle
  limit and a Tauberian remainder).
* Not added to `RamanujanTau.lean`, `README.md`, `docs/STATUS.md`, `docs/RESULTS.md` (per brief).

## Literature

- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29
  (1982) 278–295.
- R. A. Rankin (1939), A. Selberg (1940): the constant `rsConst f`.
- D. Zagier (1981), P. Sarnak (1981): horocycle equidistribution.
- J. Karamata (1931): Tauberian theorem.
- J. L. Hafner, Math. Ann. 264 (1983): `N₀(T) ≫ T` (the open item (2)).
