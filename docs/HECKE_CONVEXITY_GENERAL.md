# Hecke theory and the convexity bound for every level-one cusp form

Lean directory: `RamanujanTau/HeckeConvexGeneral/` (`Summable.lean`, `Hecke.lean`,
`Convex.lean`, `Main.lean`). Build: `nice -n 10 lake build RamanujanTau.HeckeConvexGeneral.Main`.
All 16 theorems printed in `Main.lean` depend only on `[propext, Classical.choice, Quot.sound]`.

**Evidence level: (1), Lean and axiom-clean.** There are no named hypotheses, no `sorry` and
no `native_decide`.

This generalizes `RamanujanTau/HeckeConvex/` (where `f = Δ`, see `HECKE_CONVEXITY.md`) and the
Hecke construction of `RamanujanTau/HeckeL/` (where it was only for `Δ`) to every
`f : CuspForm 𝒮ℒ (k : ℤ)` with `k : ℕ`, which is the setting of `RankinSelbergGeneral`. The
original files are unchanged. The proofs were copied and parametrized.

Coordinates are unnormalized. `coef f n := (qExpansion 1 f).coeff n` is `a_f(n)`.
`L(f,s) = Σ a_f(n) n^{-s}` (weight `k`) has critical line `Re s = k/2`.
`heckeLambda f := mellin (fun t => f(it))`, and
`fL f s := (2π)^s Γ(s)^{-1} heckeLambda f s` is the entire continuation of `L(f,s)`.

## Statements

```lean
-- (a) Rankin's mean bound and absolute convergence  (Summable.lean)
theorem exists_sum_norm_coef_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ∑ n ∈ Icc 1 N, ‖coef f n‖ ≤ A * (N : ℝ) ^ (((k : ℝ) + 1) / 2)
theorem LSeriesSummable_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ}
    (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable (coef f) s
theorem summable_norm_coef_div_rpow (f) (hk : 1 ≤ k) {σ : ℝ} (hσ : ((k : ℝ) + 1) / 2 < σ) :
    Summable fun n : ℕ => ‖coef f n‖ / (n : ℝ) ^ σ

-- (b) Hecke's theorem  (Hecke.lean)
noncomputable def heckePair (f) (hk : 1 ≤ k) : StrongFEPair ℂ   -- weight k, ε = I ^ k
theorem heckeLambda_entire (f) (hk : 1 ≤ k) : Differentiable ℂ (heckeLambda f)
theorem heckeLambda_functional_equation (f) (hk : 1 ≤ k) (s : ℂ) :
    heckeLambda f (k - s) = I ^ k * heckeLambda f s
theorem heckeLambda_eq (f) (hk : 1 ≤ k) {s : ℂ} (hs : ((k : ℝ) + 1) / 2 < s.re) :
    heckeLambda f s = (2 * π : ℂ) ^ (-s) * Gamma s * LSeries (coef f) s
theorem heckeLambda_bdd_strip (f) (hk : 1 ≤ k) (a b : ℝ) :
    ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖heckeLambda f s‖ ≤ L
theorem fL_entire (f) (hk : 1 ≤ k) : Differentiable ℂ (fL f)
theorem fL_eq_LSeries (f) (hk : 1 ≤ k) {s : ℂ} (hs : ((k : ℝ) + 1) / 2 < s.re) :
    fL f s = LSeries (coef f) s
theorem fL_functional_equation (f) (hk : 1 ≤ k) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n)
    (hs' : ∀ n : ℕ, (k : ℂ) - s ≠ -n) :
    (2π)^(-(k-s)) * Gamma (k - s) * fL f (k - s) = I ^ k * ((2π)^(-s) * Gamma s * fL f s)

-- (c) convexity  (Convex.lean)
theorem fL_bounded_of_gt (f) (hk : 1 ≤ k) {σ : ℝ} (hσ : ((k : ℝ) + 1) / 2 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, σ ≤ s.re → ‖fL f s‖ ≤ D
theorem fL_convexity_strip (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, ((k : ℝ) - 1) / 2 ≤ σ → σ ≤ ((k : ℝ) + 1) / 2 →
      ‖fL f ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (((k : ℝ) + 1) / 2 - σ + ε)
theorem fL_convexity (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fL f (((k : ℝ) / 2 : ℝ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε)

-- consistency (Main.lean)
lemma coef_discriminant (n : ℕ) : coef (k := 12) CuspForm.discriminant n = tauC n
```

The convexity theorems hold for every `k : ℕ`, with no `1 ≤ k` hypothesis, because for `k < 12`
Mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` gives `f = 0`, so `fL f = 0`.

## Proof outline

**(a)** `RankinSelbergGeneral.rankinSelberg_asymptotic` implies that
`(1/N) Σ_{n≤N} |a(n)|²/n^{k−1}` is bounded by some `B`. Multiplying by `n^{k−1} ≤ N^{k−1}` gives
`Σ |a(n)|² ≤ B N^k`. Cauchy–Schwarz then gives `(Σ |a(n)|)² ≤ B N^{k+1}`, and Mathlib's
`LSeriesSummable_of_sum_norm_bigO` turns this into absolute convergence.

**(b)** Neither Mathlib nor the repo had this for general `f`. The repo's `HeckeL/Basic.lean`
was specific to `Δ`. The generalization works as follows:
- `slash_action_eqn''` at `mapGL S ∈ 𝒮ℒ` with `denom S (it) = it` gives
  `f(i/t) = (i^k t^k) f(it)`.
- `CuspFormClass.exp_decay_atImInfty` gives decay at `∞`.
- Together these make `(F, F)` a `StrongFEPair` with `ε = i^k` and `symm.Λ = Λ`. This yields
  entirety and `Λ(k−s) = i^k Λ(s)`.
- The Mellin–Dirichlet identity comes from `hasSum_qExpansion` and `hasSum_mellin`, and it holds
  on all of `Re s > (k+1)/2` by (a). So for general `f`, no identity-theorem step is needed for
  `fL = LSeries` on that half-plane, unlike the `Δ` case.

**(c)** This is the proof from `HeckeConvex/Convex.lean` with `13 ↦ k+1` and `12 ↦ k`, applied
for `k ≥ 12`:
- The Phragmén–Lindelöf function is `fC f ε s = L(f,s) Γ(s/2) / Γ((k+1+2ε−s)/2)`.
- On the right edge, the Γ-ratio has modulus 1.
- On the left edge, `L(f,s) = i^k (2π)^{2s−k} Γ(k−s)/Γ(s) L(f,k−s)` with `|i^k| = 1`, and the
  repo's Stirling-type ratio bounds give `8e²⁰`.
- Inside the strip, the growth is at most `e^{2π|t|}`. This uses `heckeLambda_bdd_strip` on
  `[k/2−1, k/2+1]` and `1/Γ ≪ e^{π|Im|}` on `0 ≤ Re ≤ k+2`, which is the generalized strip
  lemma.
- `RankinSharp.pl_strip` closes the argument.
- The Stirling lemmas need `Re ≥ 1` at `(k−1)/2 − ε` and at half of it. Both hold for `k ≥ 12`,
  and smaller `k` are handled by `S_k = 0`.

## Gaps / scope

- Odd `k` and `k < 12` hold trivially (`S_k = 0`). The statements are still uniform in `k`.
- The constants are ineffective (`∃ C`), as in the `Δ` version.
- `fL` is defined through `Λ` for every `f`. The identity `fL f = LSeries (coef f)` is proved
  only on `Re s > (k+1)/2` (`fL_eq_LSeries`). Off that half-plane it is a definition and not a
  convergent series.
