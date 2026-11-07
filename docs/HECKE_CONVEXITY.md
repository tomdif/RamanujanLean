# Rankin's absolute convergence and the convexity bound for L(Δ, s)

Lean directory: `RamanujanTau/HeckeConvex/` (`Summable.lean`, `Convex.lean`, `Main.lean`).
Build: `lake build RamanujanTau.HeckeConvex.Main`. Every headline theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

**Evidence level: (1), Lean and axiom-clean.** There are no named hypotheses, no `sorry` and
no `native_decide`.

Coordinates are unnormalized: `L(Δ,s) = Σ τ(n) n^{-s}` (weight 12), the critical line is
`Re s = 6`, and `tauL` is the entire continuation `(2π)^s Γ(s)^{-1} Λ(s)` from
`RamanujanTau/HeckeL/Main.lean`.

## Statements

```lean
-- (A) Rankin 1939
theorem RamanujanTau.HeckeConvex.exists_sum_abs_tau_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, |(tau n : ℝ)| ≤ A * (N : ℝ) ^ (13 / 2 : ℝ)

theorem RamanujanTau.HeckeConvex.LSeriesSummable_tau_of_gt_13_2 {s : ℂ} (hs : 13 / 2 < s.re) :
    LSeriesSummable tauC s

theorem RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow {σ : ℝ} (hσ : 13 / 2 < σ) :
    Summable fun n : ℕ => |(tau n : ℝ)| / (n : ℝ) ^ σ

theorem RamanujanTau.HeckeConvex.tauL_eq_LSeries_of_gt {s : ℂ} (hs : 13 / 2 < s.re) :
    tauL s = LSeries tauC s

theorem RamanujanTau.HeckeConvex.tauL_bounded_of_gt {σ : ℝ} (hσ : 13 / 2 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, σ ≤ s.re → ‖tauL s‖ ≤ D

-- (B) the convexity bound
theorem RamanujanTau.HeckeConvex.tauL_convexity_strip {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 11 / 2 ≤ σ → σ ≤ 13 / 2 →
      ‖tauL ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (13 / 2 - σ + ε)

theorem RamanujanTau.HeckeConvex.tauL_convexity {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε)
```

The repo already had summability for `Re s > 7` (`RamanujanTau.LSeriesSummable_tau`, from Hecke's
bound `τ(n) = O(n^6)`), and `tauL = LSeries tauC` was known only on `Re s > 7`. Before this
directory, nothing in the repo proved convergence at the 13/2 threshold.

## Proof outline

### (A) `Summable.lean`

1. The unconditional Rankin–Selberg asymptotic is
   `EisensteinReal.rankinSelberg_asymptotic_zagier_unconditional`:
   `(1/N) Σ_{n≤N} τ(n)²/n¹¹ → c`. A convergent sequence is bounded, so
   `Σ_{n≤N} τ(n)²/n¹¹ ≤ B N` for every `N`.
2. Each term satisfies `τ(n)² ≤ (τ(n)²/n¹¹) N¹¹` for `n ≤ N`, so `Σ_{n≤N} τ(n)² ≤ B N¹²`.
3. Cauchy–Schwarz (Mathlib `sq_sum_le_card_mul_sum_sq`) gives
   `(Σ_{n≤N} |τ(n)|)² ≤ N · B N¹²`, so `Σ_{n≤N} |τ(n)| ≤ √B N^{13/2}`.
4. Mathlib's partial-summation criterion `LSeriesSummable_of_sum_norm_bigO` with `r = 13/2`
   gives `LSeriesSummable tauC s` for `Re s > 13/2`.

### (B) `Convex.lean`

0. **Continuation identity on `Re s > 13/2`.** `tauL` is entire. `LSeries tauC` is analytic on
   its half-plane of absolute convergence, whose abscissa is at most 13/2 by (A). The two
   functions agree near `s = 8`, and the half-plane is convex, so the identity theorem
   (`eqOn_of_preconnected_of_eventuallyEq`) gives `tauL_eq_LSeries_of_gt`. It follows that
   `‖tauL s‖ ≤ D_σ := Σ|τ(n)| n^{-σ}` on `Re s ≥ σ > 13/2`.
1. **The PL function.** Fix `0 < ε ≤ 1/2`. Let `a = 11/2 − ε` and `b = 13/2 + ε`. Define
   `f_ε(s) = tauL(s) Γ(s/2) / Γ((13+2ε−s)/2)`.
   Its weight has modulus `≍ |t|^{σ−b}`, which has slope 1 in `σ`. The degree-2 weight
   `Γ(s)/Γ(c−s)` would have slope 2, which is the wrong slope for this degree-2 L-function
   with factor `Γ(s) = Γ_ℂ(s)`.
2. **Right edge `Re s = b`.** Here `(13+2ε−s)/2 = conj(s/2)`, so the weight has modulus exactly
   1 and `‖f_ε‖ ≤ D_b` (`fC_right`).
3. **Left edge `Re s = a`.** Using `Λ(12−s) = Λ(s)`,
   `tauL(s) = (2π)^s (2π)^{-(12−s)} Γ(12−s)/Γ(s) · tauL(12−s)` with `Re(12−s) = b`.
   Both Γ-pairs are shifts by the same real `θ = 1+2ε`:
   `12−s = s̄ + θ` and `(13+2ε−s)/2 = conj(s/2) + θ`.
   - `Stirling.norm_Gamma_add_le` gives `|Γ(12−s)| ≤ 2e¹⁰ |s|^θ |Γ(s)|`.
   - `Stirling.norm_Gamma_mul_rpow_le_add` gives `|Γ(s/2)| |s/2|^θ ≤ e¹⁰ |Γ((13+2ε−s)/2)|`.

   The Γ-quotient is therefore at most `2^{1+θ} e²⁰ ≤ 8e²⁰`. The `2π` factors contribute
   `(2π)^{-1-2ε} ≤ 1`. The result is `‖f_ε‖ ≤ 8e²⁰ D_b` (`fC_left`).
4. **Growth inside the strip.** The function `f_ε` is `O(e^{2π|t|})` there, using four facts:
   - `heckeLambda_bdd_strip`;
   - `1/Γ(w) ≪ e^{π|Im w|}` for `0 ≤ Re w ≤ 10`, from `RankinError.exists_norm_inv_Gamma_le`
     together with compactness for `|Im w| < 1`;
   - `|Γ(s/2)| ≤ Γ(Re s/2)`;
   - the bound `(2π)^σ ≤ (2π)^7`.

   This is the growth estimate `fC_growth`.
5. **Phragmén–Lindelöf.** `RankinSharp.pl_strip` applies to the strip `[a, b]`, which has width
   `1+2ε < 2π`, and gives `fC_bound`.
6. **Back to `tauL`.** On `Re s = σ ∈ [a, b]` we have `(13+2ε−s)/2 = conj(s/2) + (b−σ)`, so
   `‖tauL s‖ ≤ 2e¹⁰ C ‖s/2‖^{b−σ}` (`tauL_line`).
7. **Headlines.** For `11/2 ≤ σ ≤ 13/2` and `ε' = min(ε, 1/2)`, we have
   `‖s/2‖ ≤ 4(1+|t|)` and `4^θ ≤ 16`, which gives `tauL_convexity_strip`. Taking `σ = 6` gives
   `tauL_convexity`.

## Remarks

- **1/2 is the convexity barrier.** The exponent `1/2 + ε` at `σ = 6` is exactly the
  Phragmén–Lindelöf interpolation between `O(1)` at `Re s = 13/2 + ε` and `O(|t|^{1+2ε})` at
  `Re s = 11/2 − ε`. Beating it is the subconvexity problem, for example Good (1982):
  `L(Δ, 6+it) ≪ |t|^{1/3+ε}`. Subconvexity is **not attempted** here.
- The input to (A) is Rankin–Selberg on average, not Deligne's bound. Deligne's bound
  `|τ(n)| ≤ d(n) n^{11/2}` would give 13/2 pointwise, but it is not used.
- The constant `C` is not explicit as a number. It is assembled from `D_{13/2+ε}`, `e²⁰` and the
  Phragmén–Lindelöf data, and it degenerates as `ε → 0` because `D_{13/2+ε} → ∞`.
- The strip version is stated for `11/2 ≤ σ ≤ 13/2`. The bound for `σ > 13/2` is
  `tauL_bounded_of_gt`. The bound for `σ < 11/2` would follow from the functional equation plus
  `Stirling.norm_Gamma_add_le`, but it is not stated here.
