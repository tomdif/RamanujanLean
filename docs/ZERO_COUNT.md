# Counting the nontrivial zeros of L(Δ,s): `T ≪ N(T) ≪ T log T` and `N(T+1) − N(T) ≪ log T`

Lean: `RamanujanTau/ZeroCount/{Bounds,Jensen,Main}.lean`, namespace `RamanujanTau.ZeroCount`.
Build: `nice -n 10 lake build RamanujanTau.ZeroCount.Main`, which exits 0. The module is included in
the root `RamanujanTau.lean` import graph.

**Evidence level (1).** The results are in Lean and axiom-clean: every headline below prints
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `native_decide`, no new
`axiom` and no named hypothesis.

Coordinates are unnormalized: `tauL s = L(Δ,s) = Σ τ(n) n^{-s}`, the critical strip is
`11/2 < Re s < 13/2` and the critical line is `Re s = 6`.

## Definitions

```lean
noncomputable def mult (u : ℂ) : ℕ := analyticOrderNatAt tauL u     -- multiplicity (0 if tauL u ≠ 0)
def zeroSet (a b : ℝ) : Set ℂ :=
  {u | tauL u = 0 ∧ 11/2 < u.re ∧ u.re < 13/2 ∧ a < u.im ∧ u.im ≤ b}
noncomputable def zeroCountAB (a b : ℝ) : ℕ := ∑ u ∈ (zeroSet_finite a b).toFinset, mult u
noncomputable def zeroCount (T : ℝ) : ℕ := zeroCountAB 0 T           -- N(T), with multiplicity
```

By `zeroSet_eq_of_nonneg`, which uses edge non-vanishing, for `0 ≤ a` the set `zeroSet a b` is
exactly `{u | tauL u = 0 ∧ a < Im u ≤ b}`. So `N(T)` counts **all** zeros with `0 < Im ≤ T`,
with multiplicity.

## Headline statements

```lean
-- Bounds.lean
theorem tauL_norm_lower {s : ℂ} (hs : 13/2 < s.re) : Real.exp (-Kconst s.re) ≤ ‖tauL s‖
theorem tauL_poly_bound : ∃ A, 0 ≤ A ∧ ∀ s : ℂ, 5 ≤ s.re → s.re ≤ 9 → ‖tauL s‖ ≤ A * (1 + ‖s‖)^2
-- Jensen.lean
theorem jensen_disc : ∃ E, ∀ t₀ : ℝ,
  ((∑ᶠ u, divisor tauL (closedBall (7 + t₀ * I) |8/5|) u : ℤ) : ℝ) ≤ (2 * log (12 + |t₀|) + E) / log (5/4)
theorem window_count : ∃ C, 0 ≤ C ∧ ∀ T : ℝ, ∀ S : Finset ℂ, ↑S ⊆ zeroSet T (T+1) →
  ((∑ u ∈ S, mult u : ℕ) : ℝ) ≤ C * log (|T| + 2)
-- Main.lean
theorem zeroSet_finite (a b : ℝ) : (zeroSet a b).Finite
theorem zeroSet_eq_of_nonneg (ha : 0 ≤ a) : zeroSet a b = {u | tauL u = 0 ∧ a < u.im ∧ u.im ≤ b}
theorem zeroCountAB_add (hab : a ≤ b) (hbc : b ≤ c) : zeroCountAB a c = zeroCountAB a b + zeroCountAB b c
theorem zeroCount_window : ∃ C, 0 ≤ C ∧
  (∀ T, (zeroCountAB T (T+1) : ℝ) ≤ C * log (|T| + 2)) ∧
  (∀ T, 0 ≤ T → (zeroCount (T+1) : ℝ) - zeroCount T ≤ C * log (T + 2))
theorem zeroCount_le : ∃ C, 0 ≤ C ∧ ∀ T, 0 ≤ T → (zeroCount T : ℝ) ≤ C * (T + 1) * log (T + 2)
theorem zeroCount_le_T_log_T : ∃ C, 0 ≤ C ∧ ∀ T, 2 ≤ T → (zeroCount T : ℝ) ≤ C * T * log T
theorem zeroCount_two_sided : ∃ c C T₀, 0 < c ∧ 0 ≤ C ∧ 2 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
  c * T ≤ zeroCount T ∧ (zeroCount T : ℝ) ≤ C * T * log T
```

## Proof

1. **Lower bound at the centre** (`tauL_norm_lower`). For `Re s > 13/2`, the Euler product
   (`HeckeZeros.tauL_eulerProduct`) gives `(∏_p P_p(s))·L(s) = 1`. The local bound is
   `‖P_p(s) − 1‖ ≤ |τ(p)|p^{−σ} + p^{11−2σ}`, and the majorant is summable by Rankin's
   absolute convergence. The partial products of norms satisfy
   `∏_F(1 + g_p) ≤ exp Σ g_p` (Mathlib `Real.prod_one_add_le_exp_sum`), and
   `HasProd.norm` passes this to the limit. Hence `‖L(s)‖ ≥ exp(−K(σ))`, uniformly in `t`.
2. **Growth on `5 ≤ Re ≤ 9`** (`tauL_poly_bound`). For `Re ∈ [5,7]` this is
   `HeckeConvex.tauL_line` with `ε = 1/2`: `‖L‖ ≤ 2e¹⁰C‖s/2‖^{7−σ} ≤ 2e¹⁰C(1+‖s‖)²`. For
   `Re ≥ 7` it is `tauL_bounded_of_gt`.
3. **Jensen** (`jensen_disc`). Take centre `c = 7 + it₀`, `r = 8/5` and `R = 2`. Mathlib's
   `AnalyticOnNhd.sum_divisor_le`, from `Mathlib/Analysis/Complex/JensenFormula.lean`, gives
   `Σ_{|u−c|≤r} ord_u L ≤ log(M/‖L(c)‖)/log(R/r)`, where
   `M = (1+A)(12+|t₀|)² ≥ sup_{|z−c|=2}‖L‖`.
4. **Windows** (`window_count`). The window `11/2 < Re < 13/2`, `T < Im ≤ T+1` lies in the disc
   of radius `8/5` about `7 + i(T+1/2)`, because `(3/2)² + (1/2)² = 5/2 < 64/25`. On the disc,
   `divisor = mult` (`divisor_eq_mult`). The order is never `⊤`, because `L(7) ≠ 0` and the
   identity theorem applies (`order_ne_top`).
5. **Finiteness and summation** (`Main`). A window contains no infinite set of zeros: such a set
   would contain finite subsets of every size, which contradicts step 4. A general `zeroSet a b`
   is covered by finitely many windows. For `N(T)`, split by window index
   `⌈Im⌉₊ − 1 < ⌈T⌉₊ ≤ T+1` with `Finset.sum_fiberwise_of_maps_to`.
6. **Lower bound.** `HardyCountHafner.tauL_critical_zeros_linear` provides `≥ cT` distinct
   `t ∈ (0,T]` with `L(6+it) = 0`. The map `t ↦ 6+it` sends them injectively into
   `zeroSet 0 T`, and each zero has `mult ≥ 1` (`critical_card_le_zeroCount`).

## What is not proved (gaps)

- **The Riemann–von Mangoldt asymptotic** `N(T) = (T/π) log(T/(2πe)) + O(log T)`
  (Iwaniec–Kowalski Thm 5.8) is **not** proved. It needs:
  - the argument principle on the rectangle `[5,7] × [0,T]`, or Littlewood's lemma. Mathlib has
    Jensen's formula on discs, but neither of these;
  - `arg Γ(s)` via Stirling. The repo's `Stirling` module bounds `|Γ|`, not `arg Γ`;
  - a Backlund-type bound `arg L(σ+iT) ≪ log T` on the horizontal side. The standard proof of
    that bound is itself Jensen counting, of the type proved here, applied to
    `(L(s+iT) + L(s̄+iT)‾)/2`.
- **Lower bound `N(T) ≫ T log T`** is not proved. The current lower bound `≫ T` comes from
  Hafner's critical-line zeros only.
- The constants `C`, `c` and `T₀` are ineffective. They are existential, and assembled from the
  PL constant in `HeckeConvex`, `K(7)` and Hafner's constant.
- `N(T+1) − N(T) ≪ log T` is the expected **sharp order** for a degree-2 L-function, up to the
  constant. The proof uses only convexity, which is all Jensen needs (polynomial growth).

## Literature

Iwaniec–Kowalski, *Analytic Number Theory*, Prop. 5.7 (the Jensen window bound) and Thm 5.8
(the `N(T)` asymptotic); Titchmarsh, *Theory of the Riemann zeta-function* §9.2–9.4 (the ζ
analogue). Hafner (1983): `N₀(T) ≫ T` for cusp forms.
