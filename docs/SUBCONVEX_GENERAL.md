# t-aspect subconvexity for `L(f,s)`, every level-one cusp form `f`: audit, milestone, plan

**Status (2026-11-06).**

* **Level 1** (Lean, axiom-clean):
  * the weight-`k` reduction `SCS_f(η,B) ⇒ |L(f,k/2+it)| ≪ (1+|t|)^{1/2−δ₂(η,B,u)}`, for every `f` with real coefficients, so for every normalized Hecke eigenform;
  * the consistency check at `f = Δ`: the general pipeline gives `δ = 1/134`, unconditionally;
  * the `Δ`-specific geometric core of the SCS proof, generalized to weight `k`.
* **Level 2:** for every normalized eigenform `f`, subconvexity in Lean is conditional on the single named class `SCSf f η B`.
* **Level 3** (paper only): the instance `SCSf f (1/21) (1/21)` for general `f`, which would give unconditional `δ = 1/134` for every eigenform.

So the goal is **not** reached unconditionally for `k ≠ 12`. What is missing is a mechanical, but large, weight-`k` copy of the SCS chain downstream of `TwoPoint` (§3).

    nice -n 10 lake build RamanujanTau.SubconvexGeneral.Main      # exit 0

* Every `#print axioms` in `SubconvexGeneral/Main.lean` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/SubconvexGeneral/`.
* The directory has 8 files and about 1.4k lines.
* No existing file was modified.

## 1. Audit: what in the `Δ` chain is weight-specific?

The chain is `SubconvexityCond` → `SCSProof` → `SCSSharp` → `SCSSharp2`. Here `λ(n) = τ(n)n^{−11/2}` and `a_n = τ(n)τ(n+h)`.

| piece | `Δ`-specific content | weight-`k` version | exponent change after normalizing `λ_f = a_f(n) n^{−(k−1)/2}` |
|---|---|---|---|
| `SubconvexityCond.Defs`: `lam`, `shiftSum`, SCS class | `τ`, `11/2` | `nlam f` (`EigenformEdge`), `shS`, `SCSf` (**done**) | none |
| `Expand`, `Gauss`, `Kernel`, `Pointwise`, `Coeff` (gBound part) | none (generic sequences) | reused by import | none |
| `OffDiag`, `MeanValue` | `lam` hard-coded as a constant, never used | generic `l` (`GOffDiag`, **done**, verbatim) | none |
| diagonal `Σλ²/n` | `MeanSquare.sum_tau_sq_rpow_le` (τ only) | Abel summation of Rankin `Σλ_f² ≤ AN` (`sum_nlam_sq_div_le`, **done**) | none; the log is absorbed in the same `T^{v/2}` |
| approximation `approx_tauL` at `σ = 6` | `tauL`, `13/2`, `c = 7−σ`, `tauL_growth` | `approx_fL` at `σ = k/2`, line `c = 1`, `fL_growth` from `fC_bound`/`fL_line` (**done**) | the abscissae shift by `k/2 − 6`; the error `X^{−δ}(1+|t|)^{1/2+δ+ε}` is unchanged |
| conjugation `tauL_conj` | `τ` real | `EigenformEdge.fL_conj` (needs real coefficients) | none |
| reduction `rpoly_bound2`, `tauL_subconvex_of_SCS2` | `lam`, `tauL`, `bsm 6` | `rpoly_boundF`, `fL_subconvex_of_SCSf` (**done**) | **none**: `δ₂ = η/((1+u)(4B+6+2η))` |
| `TwoPoint`: `Ψ = (z−w̄)¹²Δ(z)conj Δ(w)`, `Gh` | weight 12, `Δ`, `τ` real | `PsiF`, `GhF = Σ conj a(n) a(n+h) e^{−nW}`, `PsiF_smul`, `norm_PsiF_le` (exponent `k/2`), `coeff_PsiF` (**done**) | `Dh⁶ ↦ Dh^{k/2}`, prefactor `(y(i−ζ̄))^k` |
| `Gbounds`: Parseval `Στ²e^{−nσ} ≪ σ^{−12}` | `12` | `coef_sq_laplace` (`σ^{−k}`, **done**) | `−12 ↦ −k` |
| `Gbounds2`: `abs_laplace_le`, Lipschitz `norm_Gh_sub_le` | `aabs` via `τ` | not done | `σ^{−12} ↦ σ^{−k}` |
| `CS2–4`, `Qform1–3`, `Main1`, `Main4`, `Point1–4`; `SCSSharp.NormQ`/`Point`; `SCSSharp2.Point`/`Point21` | `Psi`/`cf` appear in the definitions; `^6`, `^12`, `R⁶ = 64A¹²` | not done (§3) | **none in `s`, `a`, `B`** (§2) |
| `Tauber1–6`, `SCSSharp.RieszK/Rmean/Asum/Final`, `SCSSharp2.Rmean21/Asum21/Final21` | `x^{12−η}`, `t^{−11/2}(t+h)^{−11/2}`, Rankin short sums for `τ` | not done (§3) | `12 ↦ k`, `11 ↦ k−1`; Rankin short sums come from `RankinExact.rankinSelberg_exact_general` (`N^{3/5}`, **every weight**) |
| Bruhat/Kloosterman/Weil, `Test`, `Measures`, `Unfold2`, `Ball`, `Divisor`, `KloostGcd` | none (test function only) | reused by import | none |

## 2. Why `δ` should be the same for every `k` (paper, level 3)

The pointwise bound is

    Y^k |G^f_h| ≪ (A-power) · h^{β/2} ε^{−3/2} Y^{1/4−δ_W} + A ε.

Each ingredient changes with `k` as follows.

* **Unchanged:** `‖P‖²` and `μ(I)μ(B)`. Neither depends on `f`.
* **`‖Ψ_f 1_{supp P}‖₂ ≤ M R^{k/2}(cR)^{1/2}`** with `R = 2A²`.
* **Prefactor:** `|Y(i−ζ̄₀)|^k ≥ (YA/2)^k`.
  * `R^{k/2}/(A/2)^k = 2^{3k/2}` is a constant.
  * So the `A`-loss is `A^{1}` from the ball measure, exactly as at `k = 12`, where `R⁶ = 64A¹²` cancelled `A¹²`.
* **Lipschitz error of `cf`:**
  * the relative error is `≪_k Aε`;
  * `Σ n|a_n|e^{−nσ} ≪ σ^{−k−1}` from `coef_sq_laplace`;
  * the derivative of `(y(i−ζ̄))^k` costs a factor `k`.

So `|G^f_h(σ+iv)| ≪_f h^{1/22} (|2v/σ|+3) σ^{−k+s}` with the same `s = 99/1000` and `a = 1`.

* **Tauberian step:** the same kernel `P₂`, the same `(κ, ι, j) = (2/39, 1/273, 13)`. The Rankin short sums have error `N^{3/5}` in every weight.
* **Abel summation:** `w(t) = t^{−(k−1)/2}(t+h)^{−(k−1)/2}` with `|w'| ≤ (k−1)t^{−(k+1)/2}(t+h)^{−(k−1)/2}`, the same structure.

Hence `SCS_f(1/21, 1/21)` should hold, and `fL_subconvex_of_SCSf` turns it into `δ = 1/134`, **for every `f`**. Only the constants depend on `f` and `k`.

Lean evidence for the weight-independence:

* the reduction is proved for every `k` with the same `δ₂` (level 1);
* the check `fL_discriminant_subconvex` re-derives `1/134` through the weight-`k` code at `k = 12`.

For the pointwise and Tauberian part the invariance is paper only.

## 3. What remains, and its cost

To prove `instance : SCSf f (1/21) (1/21)` for every `f`, you need a weight-`k` copy of every file whose **content** mentions `Psi`, `Gh`, `cf`, `aabs`, `tau` or `lam` in the `SCSSharp2.Final21` dependency chain. Files with `Δ`-free content, such as `Coord`, `Main2`, `Main3`, the `Bruhat*` files and `Test`, are reused by import.

| block | files | lines (τ version) | main friction |
|---|---|---|---|
| unfolding/Hölder for `Ψ_f` | `CS2`, `CS3`, `CS4`, `Qform`, `Qform2`, `Qform3`, `SCSSharp.NormQ` | ≈ 800 | `Dh⁶` ↦ `Dh^{k/2}` (rpow); measurability of `PsiF` |
| a-priori/Lipschitz for `G^f_h` | `Gbounds2` | ≈ 175 | `σ^{−12}` ↦ `σ^{−k}`; complex `a_n` |
| main term / pointwise | `Main1`, `Main4`, `Point1`, `Point2`, `Point4`, `SCSSharp.Point`, `SCSSharp2.Point`, `SCSSharp2.Point21` | ≈ 1.2k | `(YA/2)^k` vs `R^{k/2}` constants; `k`-dependent numerics in place of `norm_num` on `12` |
| Tauberian/unsmoothing | `Tauber1`, `Tauber2`, `Tauber4–6`, `SCSSharp.RieszK`/`Rmean`/`Asum`, `SCSSharp2.Rmean`/`Rmean21`/`Asum`/`Asum21` | ≈ 1.6k | `x^{12−η}` ↦ `x^{k−η}`; Rankin short sums from `rankinSelberg_exact_general` |
| Abel summation | `Final1`, `Final2`, `SCSSharp.Final`, `SCSSharp2.Final`/`Final21` | ≈ 1.1k | `t^{−11/2}` ↦ `t^{−(k−1)/2}`; real part of `conj a(n) a(n+h)` |

The estimate is **3.5–5k new lines**, mostly find-and-replace plus re-proving numeric side conditions with `k` symbolic. That is two to four agent sessions.

A cleaner design would abstract the downstream chain over a structure `TwoPointData`. Its fields would be:

* `Φ` measurable and invariant;
* `‖Φ‖ ≤ M Dh^m`;
* the horocycle-coefficient identity with some `G`;
* the Parseval bound `σ^{−2m}`;
* Rankin short sums.

The chain would then be proved once, and `Δ` and every `f` would become instances. This is the same amount of work as the port, but it leaves one proof instead of two.

**Complex coefficients.**

* The SCS side handles complex `a_f`, since `GhF` uses `conj a(n) a(n+h)`.
* The reduction needs real coefficients, for `fL_conj` (used for `t ≤ −1`) and for the real mean-value expansion.
* For an arbitrary `f`, there are two routes, and neither is formalized:
  1. Write `f = f₁ + i f₂` with `f_j` having real coefficients. This needs `f^ρ(z) = conj f(−z̄)` as a `CuspForm`, which is not in the repo or Mathlib.
  2. Use the eigenbasis of `S_k`. Neither Mathlib nor the repo has Hecke operators.
* Normalized eigenforms, the requested fallback, are covered: `IsNormalizedEigenform.real`.

## 4. Files (`RamanujanTau/SubconvexGeneral/`)

| file | content |
|---|---|
| `Defs.lean` | `shS`, class `SCSf f η B`, `scsf_trivial` (`SCS_f(0,0)`), `SCSf.mono`, `sum_sq_div_le_log`, `sum_nlam_sq_div_le` |
| `GOffDiag.lean` | `offS_eqG`, `offS_boundG`, `sum_offS_boundG`, `mean_value_boundG` (generic `l`) |
| `Approx.lean` | `fL_growth`, `aSF`, `LSeries_aSF`, `summable_aSF`, `bsmF`, `tsum_eq_dpolyF`, **`approx_fL`** |
| `Reduction.lean` | `dpoly_bsmF_eq`, `rpoly_boundF`, **`fL_subconvex_of_SCSf`** |
| `Check.lean` | `nlam_discriminant`, `scsf_discriminant`, **`fL_discriminant_subconvex`**, `fL_subconvex_eigen_of_SCSf`, `exists_subconvex_of_SCSf` |
| `TwoPointF.lean` | `PsiF`, `GhF`, `f_smul`, **`PsiF_smul`**, **`norm_PsiF_le`**, **`coeff_PsiF`** |
| `GboundsF.lean` | `aabsF`, `aabsF_le`, `coef_sq_laplace` |
| `Main.lean` | headlines + `#print axioms` |

Headline statements (`RamanujanTau.SubconvexGeneral`; `k : ℕ`, `f : CuspForm 𝒮ℒ (k : ℤ)`):

```lean
class SCSf (f) (η B : ℝ) : Prop where
  bound : ∃ C, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shS (nlam f) h N| ≤ C * ((N : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B

theorem fL_subconvex_of_SCSf (f) (hreal : ∀ n, (coef f n).im = 0) {η B : ℝ} [SCSf f η B]
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hB : 0 ≤ B) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - subconvexDelta2 η B u)

theorem fL_subconvex_eigen_of_SCSf {f} (hf : IsNormalizedEigenform f) [SCSf f η B] ... -- same

theorem fL_discriminant_subconvex : ∃ C, 0 ≤ C ∧ ∀ t : ℝ,
    ‖fL (k := 12) DeltaF (((((12 : ℕ) : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1/2 - 1/134 : ℝ)

theorem approx_fL (f) (hk : 12 ≤ k) {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε)
    (hθ : 1/2 + δ + ε ≤ 2) : ∃ C, 0 ≤ C ∧ ∀ X ≥ 1, ∀ t,
      ‖fL f (↑(k/2) + t*I) - dpoly (bsmF f (k/2) X) ⌊X⌋₊ t‖ ≤ C * X^(-δ) * (1+|t|)^(1/2+δ+ε)

theorem PsiF_smul (f) (γ : SL(2, ℤ)) (z w : ℍ) : PsiF f (γ • z) (γ • w) = PsiF f z w
theorem norm_PsiF_le (f) : ∃ M, 0 ≤ M ∧ ∀ z w,
    ‖PsiF f z w‖ ≤ M * (normSq (z - conj w) / (z.im * w.im)) ^ ((k : ℝ) / 2)
theorem coeff_PsiF (f) (h : ℕ) {y} (hy : 0 < y) (ζ : ℍ) :
    ∫ x in 0..1, PsiF f (hp hy x) (aff hy x ζ) * cexp (-2πi h x) =
      (y (I - conj ζ)) ^ k * e^{-2π h y} * GhF f h (2π y (1 + I conj ζ))
theorem coef_sq_laplace (f) : ∃ C₀ ≥ 0, ∀ σ > 0, Summable (‖a_f n‖² e^{-nσ}) ∧
    ∑' n, ‖a_f n‖² e^{-nσ} ≤ C₀ σ^(-k)
```

Reused unchanged by import:

* from `SubconvexityCond`: `Expand`, `Gauss`, `Kernel`, `Pointwise`, `Coeff.gBound_gX*`, `exp_poly_bound`, `tpow_le`, `mul4_le`;
* from `SCSSharp2`: `subconvexDelta2`, `delta2_facts`;
* from `MeanSquare`: `perron_c`, `shift_identity`, `natCast_cpow_inv`, `norm_Pk3_le_left`;
* from `HeckeConvexGeneral`: `fL`, `fL_entire`, `fL_eq_LSeries`, `fC_bound`, `fL_line`, `fL_convexity(_strip)`, `summable_norm_coef_div_rpow`, `exists_sum_sq_div_le`;
* from `EigenformEdge`: `nlam`, `nrm`, `fL_conj`, `IsNormalizedEigenform`, `isNormalizedEigenform_discriminant`;
* from `SCSProof.TwoPoint`: `smul_sub_conj`, `aff`;
* from `RankinSelberg`: `hasSum_normSq_coeff`, `hp`.

## 5. Literature

* Good (1982): `L(f,k/2+it) ≪ t^{1/3+ε}` for every level-one holomorphic form, by spectral methods. This is far beyond `δ = 1/134`.
* Selberg (1965), Good (1981) and Jutila (1987) for shifted convolution sums.
* Weil (1948) for Kloosterman sums.

These are cited from memory and have not been re-checked.

## 6. Update (2026-11-06): gap 1 closed, unconditional `δ = 1/180` for every eigenform

**Status: level 1 (Lean, axiom-clean, no hypotheses).**

* Directory: `RamanujanTau/SubconvexGeneral2/`, 13 files, about 2.4k lines.
* It imports `SubconvexGeneral`, `SCSProof` and `SCSSharp`, and modifies none of them.
* Build: `nice -n 10 lake build RamanujanTau.SubconvexGeneral2.Main` exits 0.
* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit` or `native_decide`.

```lean
theorem pointwise_GF (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (hev : Even k) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 → (h : ℝ) * σ ≤ 1 →
      ‖GhF f h ((σ : ℂ) + v * I)‖ ≤ K * Real.sqrt h * (|2 * v / σ| + 3) * σ ^ (-(k : ℝ) + 12 / 125)
theorem scsf_of_pointwise (f) (hk : 12 ≤ k) (hreal : ∀ n, (coef f n).im = 0) (hpw : …) :
    SCSf f (1 / 22) (1 / 2)
theorem scsf_general (f) (hreal) : SCSf f (1 / 22) (1 / 2)
theorem fL_subconvex_general (f) (hreal) : ∃ C, 0 ≤ C ∧ ∀ t : ℝ,
    ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 180 : ℝ)
theorem fL_subconvex_eigenform {f} (hf : IsNormalizedEigenform f) : … -- same bound
```

**What was ported.** This is the weight-`k` copy of the `SCSSharp` chain, so the exponents are `SCS(1/22, 1/2)` and not `SCSSharp2`'s `1/21`. The weight-independence claim of §2 is confirmed in Lean: `η`, `B`, `s`, the `A`-loss and the Tauberian parameters are those of `SCSSharp`, and only the constants depend on `k` and `f`. Then `δ₂(1/22, 1/2, 1/89) = 1/180`.

| file group | content |
|---|---|
| `Geo*` (pointwise) | `GeoCS`: unfolding/Hölder for `Ψ_f`. `GeoQform`: `cfF`, `QF_eq`. `GeoGbounds`: `abs_laplace_leF`, Lipschitz `norm_GhF_sub_le`. `GeoMainTerm`: `main_term_leF`, `cfF_sub_le`. `GeoPoint`: `norm_G0_leF`, `pointwise_parF` (`k = 2m`, `R^m` against `(YA/2)^{2m}`), `pointwise_GF` |
| `Tau*` (Tauberian side) | `TauBasic`: `aT = Re a(n)·Re a(n+h)`, `rankin_shortT` from `rankinSelberg_exact_general`. `TauRiesz`: `laplace_rieszT`, `RmeanT_bound`. `TauAsum`: `AsumT_bound_large`. `TauFinal`: Abel weight `t^{−(k−1)/2}(t+h)^{−(k−1)/2}`, `AsumT_cs`, `scsf_of_pointwise` |
| assembly | `OddWeight`: `eq_zero_of_odd` (via `−1 ∈ SL₂(ℤ)`) and `scsf_of_eq_zero`. `Main`: `scsf_general`, `fL_subconvex_general`, `fL_subconvex_eigenform` |

**Remaining gaps.**

* **Exponent.** Porting `SCSSharp2` (gcd Kloosterman and the `1/21` retune) would give `δ = 1/134` for every `f`. That work is now mechanical: copy `Point21`/`Rmean21`/`Asum21`/`Final21` on top of the `Geo*`/`Tau*` files.
* **Complex coefficients.** The theorem needs real coefficients, so it covers all eigenforms but not an arbitrary `f`. To remove that, see §3.

## 7. Update (2026-11-06): `SCS_f(1/21, 1/21)` and `δ = 1/134` for every eigenform

**Status: level 1 (Lean, axiom-clean, no hypotheses).**

* Directory: `RamanujanTau/SubconvexGeneral3/`, 6 files, about 1.0k lines.
* It imports `SubconvexGeneral`, `SubconvexGeneral2` and `SCSSharp2` (for `KloostGcd`, `ηt`, `Asum21`), and modifies none of them.
* Build: `nice -n 10 lake build RamanujanTau.SubconvexGeneral3.Main` exits 0.
* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom`.

```lean
theorem scsf_general21 (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) :
    SCSf f (1 / 21) (1 / 21)
theorem fL_subconvex_general134 (f) (hreal) : ∃ C, 0 ≤ C ∧ ∀ t : ℝ,
    ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 - 1 / 134 : ℝ)
theorem fL_subconvex_eigenform134 {f} (hf : IsNormalizedEigenform f) : … -- same bound
```

So the `Δ` exponent `δ = 1/134` (`SCSSharp2.tauL_subconvex_sharp2`) now holds for every normalized Hecke eigenform of level one. With `u = 1/66`, `δ₂(1/21, 1/21, 1/66) = 1/134`.

| file | ported from | change against `SubconvexGeneral2` |
|---|---|---|
| `GeoPoint21` | `SCSSharp2.Point21` | `norm_tsum_Iγ_le_gcd (1/400) (2/21)`; `t = Y^{1/1000}`, `ε = t⁹⁹/2`; `h^{1/21}` in place of `√h`; saving `99/1000` (`pointwise_GF21`) |
| `TauRiesz21` | `SCSSharp2.Rmean21` | `L = x^{1−2/39}`; `RmeanT_bound21 : ≪ h^{1/21} x^{k−1/21}` |
| `TauAsum21` | `SCSSharp2.Asum21` | `rankin_shortT21` (exponent `1−1/21`); `AsumT_bound_large21` (cut `x^{1/273}`, `13!`) |
| `TauFinal21` | `SCSSharp2.Final21` | Abel summation with `B = η`: for `t < h`, `(t+h)^{1/2} ≤ 2h^{η}(N+h)^{1/2−η}` (`shS_bound21`, `scsf_of_pointwise21`) |
| `Main` | — | `scsf_general21` (`k < 12` and odd `k`: `f = 0`), `fL_subconvex_general134`, `fL_subconvex_eigenform134` |

Remaining gap (unchanged): an arbitrary `f` with complex coefficients (§3). For further exponent gains, the sheared box of `SCS_SHARP2.md` §4 applies verbatim in weight `k`.
