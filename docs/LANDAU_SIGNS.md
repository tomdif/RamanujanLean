# LandauSigns: Landau's theorem and sign changes of cusp-form coefficients

Status (2026-11-05): **Lean, axiom-clean** (`[propext, Classical.choice, Quot.sound]`), 0 sorry,
no native_decide, no new axioms. `LandauSigns.Main` is included in the root import graph.

Build: `nice -n 10 lake build RamanujanTau.LandauSigns.Main`

## Files
- `RamanujanTau/LandauSigns/Landau.lean`: Landau's theorem (Mathlib-only imports).
- `RamanujanTau/LandauSigns/Signs.lean`: the application to `S_k(SL₂(ℤ))` and to `τ`.
- `RamanujanTau/LandauSigns/Main.lean`: `#print axioms` for every headline.

## 1. Landau's theorem (Pringsheim–Landau)
This is not in Mathlib. Mathlib has `LSeries.positive_of_differentiable_of_eqOn`, which says
`F > 0` on ℝ, but it has nothing about convergence.

```lean
theorem RamanujanTau.LandauSigns.landau {a : ℕ → ℂ} (ha : 0 ≤ a) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {x : ℝ} (hx : abscissaOfAbsConv a ≤ x)
    (hEq : {s : ℂ | x < s.re}.EqOn F (LSeries a)) (s : ℂ) : LSeriesSummable a s

theorem landau_abscissa ... : abscissaOfAbsConv a = ⊥
theorem landau_real {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) ... (s : ℂ) :
    LSeriesSummable (fun n => (b n : ℂ)) s
```
`0 ≤ a` uses `ComplexOrder`, so each value is real and nonnegative. The hypotheses are
the same as in Mathlib's `positive_of_differentiable_of_eqOn`.

Proof. Take a real `c > x` and write the Taylor series of `F` at `c` (`Complex.hasSum_taylorSeries_of_entire`).
`iteratedDeriv j F c = (-1)^j L(log^j·a, c)` (`Set.EqOn.iteratedDeriv_of_isOpen`, `LSeries_iteratedDeriv`).
At a real `σ < c` this gives a double series `Σ_j Σ_n (c-σ)^j/j! · a(n) log^j n · n^{-c}` with
nonnegative terms. Tonelli (`summable_prod_of_nonneg`, applied twice around `Prod.swap`)
swaps the order of summation. The inner sum over `j` is `a(n) n^{-c} e^{(c-σ)log n} = a(n) n^{-σ}`.
For complex `s` the result follows from `LSeriesSummable.of_re_le_re`.

## 2. Sign changes for real cusp forms
```lean
theorem RamanujanTau.LandauSigns.coeff_sign_changes (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, ((qExpansion 1 f).coeff n).im = 0) :
    (∀ M : ℕ, ∃ n, M ≤ n ∧ 0 < ((qExpansion 1 f).coeff n).re) ∧
    (∀ M : ℕ, ∃ n, M ≤ n ∧ ((qExpansion 1 f).coeff n).re < 0)

theorem not_eventually_nonneg (f) (hf : f ≠ 0) {u : ℂ} (hu : u ≠ 0) (M : ℕ) :
    ¬ ∀ n, M ≤ n → 0 ≤ u * coef f n          -- core, any twist u ≠ 0
theorem twelve_le_weight (hf : f ≠ 0) : 12 ≤ k  -- from Mathlib rank_eq_zero_of_weight_lt_twelve
```
Proof. Use `trunc (coef f) u M` (`[n ≥ M]·u·a(n)`). Its L-series equals
`u(fL f s − Σ_{n<M} a(n) n^{-s})` on `Re s > (k+1)/2` (`fL_eq_LSeries`, `LSeriesSummable_coef`),
and this expression is entire (`fL_entire`). Landau's theorem gives summability at `s = 0`,
so `a(n) → 0`. That contradicts `TauOmega.coeff_omega`, which says `|a(n)| ≥ c n^{(k-1)/2} ≥ c`
infinitely often. Taking `u = -1` and `u = 1` gives the two halves. No hypothesis `1 ≤ k`
is needed, because `f ≠ 0` already forces `k ≥ 12`.

## 3. τ
```lean
theorem RamanujanTau.LandauSigns.tau_sign_changes :
    (∀ M : ℕ, ∃ n, M ≤ n ∧ 0 < RamanujanTau.tau n) ∧
    (∀ M : ℕ, ∃ n, M ≤ n ∧ RamanujanTau.tau n < 0)
```
This applies `coeff_sign_changes` to `CuspForm.discriminant`, using `coef_discriminant` as the bridge.
It is a sanity check only. `TauSigns` already proves stronger quantitative results.

## Gaps / scope
- Landau is stated for an *entire* continuation. The local form only needs analyticity on a
  neighbourhood of `[σ₀−η, ∞)` and gives convergence for `σ > σ₀−η`. It is not formalised.
  The Taylor-radius argument carries over, but you need the radius at `c` to reach past `σ₀−η`.
- The real-coefficient hypothesis is stated as `im = 0` for every `n`. It holds for Hecke
  eigenforms (the coefficients are totally real algebraic numbers) but is not derived here.
