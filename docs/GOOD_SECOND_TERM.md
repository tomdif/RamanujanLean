# Good's mean square of L(Δ,s) with a second term: the χ-free AFE and the reduction to the off-diagonal

Lean: `RamanujanTau/GoodSecondTerm/` (12 files, about 1960 lines). It also reuses `RamanujanTau/ZetaAFE/`.

Build with `nice -n 10 lake build RamanujanTau.GoodSecondTerm.Main`, which exits 0. There is no
`sorry`, no `native_decide`, no new axiom and no named hypothesis in any proved statement.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 11 headlines.

The only hypothesis is `OffDiagHyp δ`. It appears as an explicit premise of
`good_second_term_of_offdiag` and nowhere else.

## 0. Outcome

| result | evidence |
|---|---|
| χ-free exact AFE for `|L(Δ,6+it)|²` (`afe_exact_delta`) | **(1)** |
| smoothed AFE, `|L|² = Σ_{m,n} τ(m)τ(n)(mn)^{−6}(n/m)^{it}V(log(mn) − 2log(t/2π)) + O(t^{−1/2})` (`delta_afe`) | **(1)** |
| second-order Stirling, `R_t(z)(t/2π)^{−2z} = 1 + O(e^{y²/2}/t²)` (`gamma_ratio_delta`) | **(1)** |
| diagonal with second term and power saving (`AA_asymp`, `abs_DsumD_sub_le`, `diag_err_D`) | **(1)** |
| **unconditional reduction**: `∫₀ᵀ|L(Δ,6+it)|² = 2c₀T log(T/2π) + (2γ_Δ−2c₀)T + Off(T) + O(T^{9/10})` (`good_reduction`) | **(1)** |
| Good's second term with error `O(T^{1−δ} + T^{9/10})`, given `|Off(T)| ≪ T^{1−δ}` (`good_second_term_of_offdiag`) | **(2)**, conditional on `OffDiagHyp δ` |
| `OffDiagHyp δ` itself (needs shifted-convolution cancellation, §3) | **not proved** |
| `γ_Δ` = the Laurent constant of `Σ τ(n)²n^{−11−s}` at `s = 1`, giving the value of `c₁` | (3) standard, and (4) PARI |
| the asymptotic with `c₁` checked against `∫₀ᵀ|L(Δ,6+it)|²`, for `T ≤ 400` | (4) PARI |

## 1. Statements (namespace `RamanujanTau.GoodSecondTerm`)

```lean
-- Off(T) = Σ_{m≠n} ∫_16^T τ(m)τ(n)(mn)^{-6} (n/m)^{it} V(log(mn) − 2 log(t/2π)) dt
noncomputable def OffInt (T : ℝ) : ℂ := ∑' p, ∫ t in (16 : ℝ)..T, boD t p
def OffDiagHyp (δ : ℝ) : Prop := ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T → ‖OffInt T‖ ≤ C * T ^ (1 - δ)

theorem good_reduction : ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T →
    ‖(((∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) : ℝ) : ℂ) -
      ((2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T : ℝ) : ℂ) -
      OffInt T‖ ≤ C * T ^ (9 / 10 : ℝ)

theorem good_second_term_of_offdiag {δ : ℝ} (h : OffDiagHyp δ) : ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T →
    |(∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) -
      (2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T)| ≤
      C * (T ^ (1 - δ) + T ^ (9 / 10 : ℝ))

theorem delta_afe : ∃ C ≥ 0, ∀ t ≥ 16,
    ‖(‖tauL (6 + t I)‖² : ℂ) − ∑' p, bD t (2 log(t/2π)) p‖ ≤ C * t^(−1/2)
theorem afe_exact_delta (hc : 1/2 < c) (hc1 : c ≤ 1) … :
    π * ‖tauL (6 + tI)‖² = ∑' p : ℕ × ℕ, ∫ y, afeTermD t c p y
theorem gamma_ratio_delta (0 ≤ c ≤ 1) : ∃ K ≥ 0, ∀ t y, 16 ≤ t →
    ‖RtD t (c+yI) * cexp (−(2(c+yI)·log(t/2π))) − 1‖ ≤ K e^{y²/2} / t²
theorem norm_digamma_second (6 ≤ Re s) : ‖ψ(s) − log s + 1/(2s)‖ ≤ 10/(Re s + |Im s|)²
theorem AA_asymp : ∃ C ≥ 0, ∀ N ≥ 1, |Σ_{n≤N} τ(n)²/n¹² − c0 log N − gammaD| ≤ C N^{−1/5}
theorem abs_DsumD_sub_le : ∃ C ≥ 0, ∀ L, |Σ_n τ(n)²n^{−12} V(2log n − L) − c0 L − 2 gammaD| ≤ C(1+|L|)e^{−L/10}
```

Definitions:

- `c0 = CriticalMeanSquareAsymp.rankinC = (3/π)(4π)¹²‖Δ‖²/11!`, Rankin's constant.
- `gammaD = c0·γ + Σ_{n≥1} E(n)/(n(n+1))`, where `E(N) = Σ_{n≤N} τ(n)²/n¹¹ − c0 N`.
- `bD t ℓ (m−1,n−1) = τ(m)τ(n)(mn)^{−6}(n/m)^{it} V(log(mn) − ℓ)`, with
  `V(L) = ∫_{u>L} e^{−u²/4}/√π du = erfc(L/2)`.

## 2. The method: porting the symmetric Ξ-AFE from ζ

1. **The χ-free AFE.** Set `Φ_t(z) = Λ(6+z+it)Λ(6+z−it)`, with `Λ = heckeLambda` entire and
   `Λ(12−s) = Λ(s)`. Then `Φ_t` is even and entire. Unlike the ζ case, no `s(1−s)` factor is
   needed, because Λ has no poles.
   - `ZetaAFE.afe_line` applies verbatim. The growth bound comes from `heckeLambda_bdd_strip`.
   - On `Re z = c ∈ (1/2, 1]`, the series `Σ|τ(n)|n^{−6−c}` converges (`HeckeConvex`, from
     Rankin–Selberg and Cauchy–Schwarz). This confirms the brief's claim that `c > 1/2` suffices.
   - `tauL = LSeries` holds on `Re s > 13/2`, so the double Dirichlet series can be swapped with
     the integral. `HeckeZeros.tauL_conj` gives `Φ_t(0) = G₀|L(6+it)|²`.
2. **Degree 2 needs second-order Stirling.** The analytic conductor is `t²`, so the main term
   needs `R_t(z) ≈ (t/2π)^{2z}`.
   - The first-order error `O(1/t)` would cost `τ^{2c}/t ≥ 1`, which is too big.
   - The `1/t` terms cancel between `±t`. The proof combines
     `ψ(s) = log s − 1/(2s) + O(|s|^{−2})` (`norm_digamma_second`, via `digamma_eq_log_add`,
     the telescoping `Σ 1/((s+j)(s+j+1)) = 1/s`, and `Complex.norm_log_sub_logTaylor_le`) with
     `log a₊ + log a₋ = 2 log t + O(t^{−2})` and `1/a₊ + 1/a₋ = O(t^{−2})`.
   - This gives `‖E_t‖ ≤ 150(1+|y|)³/t²` (`norm_EfD_le`). For `|y| > t/4`, use crude bounds:
     `|Γ(6+c+iv)| ≤ Γ(6+c)` and `|Γ(6+it)|² = Pq(t)πt/sinh πt ≥ e^{−πt}`.
   - With `c = 3/4` the AFE error is `τ^{3/2}/t² = O(t^{−1/2})`.
3. **Diagonal.** Start from Rankin's `Σ_{n≤N} τ(n)²/n¹¹ = c₀N + O(N^{3/5})`
   (`rankin_normalization`).
   - Summation by parts (`AA_eq`) and Mathlib's `eulerMascheroniSeq` bounds give
     `A(N) = c₀ log N + γ_Δ + O(N^{−1/5})`. (The tail is bounded crudely by
     `Σ_{n≥N} n^{−7/5} ≤ N^{−1/5} Σ n^{−6/5}`.)
   - The `V`-smoothing is the same Tonelli argument as in `ZetaAFE.Diag`.
   - With `L = 2 log(t/2π)`, the diagonal is `2c₀ log(t/2π) + 2γ_Δ + O(t^{−1/10})`. Integrating
     gives `2c₀T log(T/2π) + (2γ_Δ − 2c₀)T`.
4. **Assembly** (`good_reduction`). Integrate over `[16,T]`.
   - The AFE error contributes `O(T^{1/2})`.
   - The diagonal error contributes `O(T^{9/10})`.
   - The off-diagonal is exactly `Off(T)`. The interchange uses `ZetaAFE.integral_tsum_Icc`.

## 3. Why the off-diagonal is left as a hypothesis (the real gap)

The brief proposed "Off-diagonal: first-derivative test as before". **For degree 2 that test
cannot even recover the leading term.**

The first-derivative test gives
`|Off(T)| ≤ Σ_{m≠n} |a(m)a(n)|(mn)^{−1/2}·2V(log(mn/τ²))/|log(n/m)|`, with
`a(n) = τ(n)n^{−11/2}` and `τ = T/2π`. Now look at the near-diagonal pairs `n = m + h` with
`m ≤ τ`, so that `mn ≲ τ²`. Each such pair contributes `≈ |a(m)a(m+h)|/h`. Summing over them gives
`≈ Σ_{h≤τ} h^{−1} Σ_{m≤τ}|a(m)a(m+h)| ≍ τ log τ`, which is `≍ T log T`. That is the same order
as the main term. The individual integrals `∫ e^{itλ}V dt` with `λ ≈ h/m ≈ h/T` do not oscillate
on `[0,T]`, so no t-integration can help.

A power saving therefore needs cancellation in the shifted convolution sums
`Σ_{m≤x} a(m)a(m+h)`. Bounds like `≪ x^{1−η}`, uniform in `h ≤ x^{1+ε}`, come from spectral theory
(Good used Kuznetsov / the spectral decomposition on `SL₂(ℤ)\ℍ`) or from the δ-method with Weil's
Kloosterman bound. None of this is in the repo.

The off-diagonal majorant is computed numerically in `offdiag_majorant.gp` (§4).

What is proved is the sharp reduction: by `good_reduction`, `OffDiagHyp δ` for some `δ > 0` is
**equivalent** to Good's second-term asymptotic with error `O(T^{1−min(δ,1/10)})`. In particular,
Good's theorem implies `OffDiagHyp δ` for every `δ < 1/10`, so the hypothesis is not vacuous. The
main-term constants do not enter the hypothesis: if `c₁` were wrong, `good_reduction` would fail
to compile.

## 4. Constants and numerics (level 4): `scripts/good_second_term/`

`constants.gp` builds L(sym²Δ, s) by `lfuncreate` with
- integer coefficients (local factor
  `1 − (τ(p)²−p¹¹)X + p¹¹(τ(p)²−p¹¹)X² − p³³X³`),
- gamma factor `Γ_ℝ(s−10)Γ_ℝ(s)Γ_ℝ(s+1)`, and
- weight 23.

`lfuncheckfeq` gives `−67`. It then uses `D(s) = Σ a(n)²n^{−s} = ζ(s)L(sym²Δ,s)/ζ(2s)`.

| quantity | value |
|---|---|
| `c₀ = L(sym²Δ,1)/ζ(2)` | `0.3840840544681703699` (agrees with `cDelta/2`) |
| `γ_Δ = c₀(γ + L'/L(sym²,1) − 2ζ'(2)/ζ(2))` (the Laurent constant) | `0.7960282558479304465` |
| partial-sum check `Σ_{n≤3·10⁴} a(n)²/n − c₀ log N` | `0.79606436` (approaches `γ_Δ`) |
| `2c₀` | `0.7681681089363407` |
| `2γ_Δ − 2c₀` (coefficient of `T`, with `T log(T/2π)`) | `0.8238884027595202` |
| written as `2c₀T log T + c₁T`, `c₁ = 2γ_Δ − 2c₀(1 + log 2π)` | `−0.5879101478016163` |
| Good's form `2c₀T(log(T/2πe) + C)`, `C = γ_Δ/c₀` | `2.0725365882480251` |

`meansq_check.gp` computes `I(T) = ∫₀ᵀ|L(Δ,6+it)|²` with `lfun`:

| T | I(T) | 2c₀T log(T/2π) + 0.82389T | difference | difference/√T | (I − 2c₀T log(T/2π))/T |
|---|---|---|---|---|---|
| 50 | 119.965 | 120.859 | −0.89 | −0.13 | 0.806 |
| 100 | 294.922 | 294.964 | −0.04 | −0.00 | 0.824 |
| 200 | 699.423 | 696.418 | 3.01 | 0.21 | 0.839 |
| 300 | 1150.441 | 1138.066 | 12.38 | 0.71 | 0.865 |
| 400 | 1587.541 | 1605.817 | −18.28 | −0.91 | 0.778 |

The last column oscillates around the predicted `0.8239`, and the residual is of size `√T`.

`offdiag_majorant.gp` computes the first-derivative-test majorant `M(T)` from §3, truncated at
`mn ≤ min(τ²e⁵, 6·10⁴)`. The output is in `offdiag_majorant.out`:

| T | M(T) | M(T)/(T log T) |
|---|---|---|
| 25 | 41.7 | 0.519 |
| 50 | 102.7 | 0.525 |
| 100 | 236.1 | 0.513 |
| 200 | 522.5 | 0.493 (truncation at `6·10⁴` starts to bite) |

So the absolute majorant is `≈ 0.5 T log T`, of the same order as the main term `0.768 T log T`.
The true `Off(T)` is `O(√T)` numerically (the residual column above). The cancellation is
genuine and arithmetic.

## 5. Gaps and next steps

1. **`OffDiagHyp`**, the shifted-convolution input, is the only missing piece. The natural next
   seam is a uniform bound `|Σ_{m≤x} a(m)a(m+h)| ≤ C x^{1−η}(1+h)^A`, then deriving `OffDiagHyp`
   from it by partial summation in `m`. That derivation is elementary but long (smooth weights in
   `m` with `t`-derivatives up to `T`); estimate 800–1500 lines. Proving the
   shifted-convolution bound itself needs Kuznetsov or the δ-method, which is a major project.
2. The exponent `9/10` in `good_reduction` comes from crude choices:
   - the tail bound `N^{−1/5}` (instead of `N^{−2/5}`);
   - `(1+L)e^{−L/10}`.

   It could be improved to about `T^{4/5+ε}`; the AFE error alone is `T^{1/2}`.
3. The identification of `gammaD` with the Laurent constant of `ζ(s)L(sym²Δ,s)/ζ(2s)` is not
   formalized. The Lean statement defines `gammaD` by the convergent series, and the
   identification is the standard Abel-summation fact, checked numerically to 4 digits.

## 6. Literature (from memory; not checked)

- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29 (1982):
  `∫₀ᵀ|L(f,k/2+it)|² = 2c T(log(T/2πe) + C) + O((T log T)^{2/3})`, by spectral methods.
- Shifted convolution sums: Selberg (1965); Good; Jutila; Blomer (2004). The δ-method: Duke,
  Friedlander and Iwaniec.

---

## 7. 2026-11-06: `OffDiagHyp (1/600)` discharged; Good's asymptotic is unconditional

**Status.** Builds with `lake build RamanujanTau.GoodSecondTerm2.Main` (exit 0). Every headline
depends only on `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `axiom`, `admit` or
`native_decide` in `RamanujanTau/GoodSecondTerm2/` (15 files, about 3100 lines).

### Headlines (namespace `RamanujanTau.GoodSecondTerm2`)

- `good_second_term`: for all `T ≥ 16`,
  `|∫₀ᵀ ‖L(Δ,6+it)‖² dt − (2c₀ T log(T/2π) + (2γ_Δ − 2c₀)T)| ≤ C T^{599/600}`.
  This is unconditional.
- `offDiagHyp_unconditional : GoodSecondTerm.OffDiagHyp (1/600)`. It is derived from
  `good_second_term` and `good_reduction`.
- `good_second_term_large`: the same bound for `T ≥ 2^300`. Here the constant comes from the
  analysis. The range `[16, 2^300]` is handled by compactness.

### Method

The only arithmetic input is `SCSSharp2.shiftedConvolutionBound_sharp2`, through `scs_partial`.

1. **Smoothing in `u`.**
   - A bound for `Off(T)` pointwise in `T` cannot be proved. The `T`-boundary term of the
     first-derivative test for near-diagonal pairs gives `T log T`.
   - Instead, `I(u) = ∫₀ᵘ|L|²` is monotone. This gives
     `avg_{[T−H,T]} I ≤ I(T) ≤ avg_{[T,T+H]} I` with `H = T^{299/300}`.
   - `avgOff_eq` shows that `(1/H)∫_T^{T+H} Off(u) du = Σ_p zz T H p`. The per-pair weight is
     `P̃ = ∫_{16}^T e^{itλ}W + (1/H)∫_T^{T+H}(T+H−t)e^{itλ}W`.
2. **Per-pair estimate (`norm_Ptil_le`).**
   - Two integrations by parts give `‖P̃‖ ≤ W(16)/|λ| + (7Φ + 3W(T+H)/H)/λ²`.
   - The `1/H` comes from the averaged boundary term.
   - The bound `∫|φ'| ≤ 2 sup φ` uses unimodality of `φ = W'`.
3. **Regions** of pairs `m < n`, with `h = n − m`. The `n < m` half follows by conjugate symmetry
   (`zz_swap`).
   - Far pairs (`n ≥ 2m+1`) are product-summable.
   - The near region with small `m` (`m < M₀`) contributes `O(M₀)` by Rankin.
   - The near region with large `h` (`h ≥ h₂`) contributes `O(T^{1+δ'}/h₂)`.
   - The SCS region `S₊ = {m ≥ M₀, h < h₂}` is handled by Abel summation of `λ(m)λ(m+h)` against
     the smooth weight `rr t h x` inside the `t`-integral. It contributes
     `O((T+H) h^{1/21}(M₀^{−1/42} + (T+H)h M₀^{−43/42}))` per `h` (`norm_Spart_h`, `off_avg_bound`).
4. **Parameters (`avgOff_le`).**
   - `H = T^{299/300}`, `M₀ = ⌊H⌋`, `h₂ = ⌊T^{1/150}⌋`, `ε = 1/600`, `T ≥ 2^300`.
   - The resulting exponents are `599/600`, `12389/12600` and `12515/12600`. All are at most
     `599/600`.
5. **Main term.** The main term is Lipschitz with constant `2|c₀|(log 2T + 1) + |2γ_Δ − 2c₀|`
   (`mainF_lip`). Its effect on the sandwich is `O(H log T) = O(T^{599/600})`.

### Files (`RamanujanTau/GoodSecondTerm2/`)

Bounds, IBP, Rankin2, SCSAbel, Pair, NonS, Sums, Regions, SPart, OffBound, OffTotal, Avg, Param,
Final, Main.

### Remarks

- The exponent `599/600` is not optimized. The bottleneck is the SCS saving `1/21` together with
  the `M₀^{−1/42}` loss from Abel summation with a `t`-dependent weight.
- The `9/10` in `good_reduction` was not improved. It is dominated by `599/600`, so improving it
  would not change the final exponent.
