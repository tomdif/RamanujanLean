# Zeros of `L(f,s)` for every level-one cusp form: Riemann–von Mangoldt and a zero-free region

Lean: `RamanujanTau/GeneralZeros/` (12 files, about 2900 lines), namespace
`RamanujanTau.GeneralZeros`. Build: `nice -n 10 lake build RamanujanTau.GeneralZeros.Main` exits 0.
The public entry point is included in the `RamanujanTau.lean` import graph.

**Evidence level (1).** Every headline in `Main.lean` prints
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `native_decide` and no new
`axiom`. The only named hypothesis is the real edge point `h0`, and it is used only in the
all-heights version of the zero-free region.

This generalizes `ZeroCount/` and `ZeroCountRvM/` (see `ZERO_COUNT.md` and `ZERO_COUNT_RVM.md`)
from `Δ` to every nonzero `f ∈ S_k(SL₂(ℤ))`. It also generalizes `ZeroFreeRegion/` (see
`ZERO_FREE_REGION.md`) from `Δ` to every normalized Hecke eigenform (`IsNormalizedEigenform`,
from `EigenformEdge`).

## Correction to the expected main term

The brief expected the main term to be `(T/π) log(T/(2πe))` for every cusp form. **That is
false when `a_f(1) = 0`.** Let `n₀` be the first index with `a_f(n₀) ≠ 0`. Then
`L(f,s) = a_f(n₀) n₀^{−s} G(s)` with `G → 1` as `Re s → ∞`. So `arg L(f, σ₁+iT)` turns like
`−T log n₀`, and it does so on both vertical sides of the rectangle (on the left side because of
the functional equation). The proved formula is

  `N_f(T) = (T/π) log(T/(2π e n₀)) + O(log T)`.

It reduces to the expected formula exactly when `n₀ = 1`, for example for every normalized
eigenform and for `Δ`. A concrete case with `n₀ = 2` is `Δ² ∈ S₂₄`, where `a(1) = 0` and
`a(2) = 1`. That instance is not formalized; the general theorem covers it.

## Definitions (`Count.lean`)

```lean
noncomputable def ord (f) (u : ℂ) : ℕ := analyticOrderNatAt (heckeLambda f) u
def zeroSet (f) (a b : ℝ) : Set ℂ := {u | heckeLambda f u = 0 ∧ a < u.im ∧ u.im ≤ b}
noncomputable def zeroCountAB (f) (a b : ℝ) : ℕ := ∑ᶠ u ∈ zeroSet f a b, ord f u
noncomputable def zeroCount (f) (T : ℝ) : ℕ := zeroCountAB f 0 T          -- N_f(T)
theorem zeroSet_eq_fL (ha : 0 ≤ a) : zeroSet f a b = {u | fL f u = 0 ∧ a < u.im ∧ u.im ≤ b}
theorem ord_eq_fL (hk : 1 ≤ k) (hu : u.im ≠ 0) : ord f u = analyticOrderNatAt (fL f) u
```

`heckeLambda` and `fL` come from `HeckeConvexGeneral`. By the last two lemmas, `N_f(T)` counts
the zeros of `L(f,s)` with `0 < Im s ≤ T`, with multiplicity.

## Headline statements

### Part 1: zero counting and Riemann–von Mangoldt, for every nonzero cusp form

The coefficients may be complex. No Euler product is used.

```lean
-- Count.lean
theorem window_count (hf : f ≠ 0) : ∃ C, 0 ≤ C ∧ ∀ T S, ↑S ⊆ zeroSet f T (T+1) →
    ((∑ u ∈ S, ord f u : ℕ) : ℝ) ≤ C * Real.log (|T| + 2)
theorem zeroSet_finite (hf) (a b) : (zeroSet f a b).Finite
theorem zeroCount_window (hf) : ∃ C, 0 ≤ C ∧ (∀ T, (zeroCountAB f T (T+1) : ℝ) ≤ C * log (|T|+2)) ∧
    (∀ T, 0 ≤ T → (zeroCount f (T+1) : ℝ) - zeroCount f T ≤ C * log (T+2))
theorem zeroCount_le (hf) : ∃ C, 0 ≤ C ∧ ∀ T, 0 ≤ T → (zeroCount f T : ℝ) ≤ C * (T+1) * log (T+2)
-- RvMFinal.lean
theorem riemann_von_mangoldt_gen (hf : f ≠ 0) (ha₀ : coef f n₀ ≠ 0)
    (hmin : ∀ n < n₀, coef f n = 0) : ∃ C, 0 ≤ C ∧ ∀ T, 2 ≤ T →
    |(zeroCount f T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1 * n₀))| ≤ C * Real.log T
theorem riemann_von_mangoldt_of_coef_one (h1 : coef f 1 ≠ 0) : ∃ C, 0 ≤ C ∧ ∀ T, 2 ≤ T →
    |(zeroCount f T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T
theorem zeroCount_ge_T_log_T_gen (hf) : ∃ T₀, 2 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
    T / (2 * π) * Real.log T ≤ zeroCount f T
-- Main.lean (sanity check)
theorem riemann_von_mangoldt_discriminant : … zeroCount (k := 12) Δ T … (T/π) log(T/(2πe)) …
```

The hypotheses `ha₀` and `hmin` only say which integer `n₀` is. Such an `n₀` exists for every
`f ≠ 0` (`exists_first`). The hypothesis `coef f 1 ≠ 0` implies `f ≠ 0`.

### Part 2: the zero-free region, for every normalized Hecke eigenform (`ZFREigen.lean`)

```lean
theorem fL_zero_free_region (hf : IsNormalizedEigenform f) : ∃ c > 0, ∃ t₀, ∀ s, fL f s = 0 →
    t₀ ≤ |s.im| → s.re ≤ ((k : ℝ) + 1) / 2 - c / Real.log |s.im|               -- unconditional
theorem fL_zero_free_region_left (hf) : ∃ c > 0, ∃ t₀, ∀ s, fL f s = 0 →
    t₀ ≤ |s.im| → ((k : ℝ) - 1) / 2 + c / Real.log |s.im| ≤ s.re               -- unconditional
theorem fL_zero_free_region_uniform (hf) (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) :
    ∃ c > 0, ∀ s, fL f s = 0 → (∀ n : ℕ, s ≠ -n) →
      s.re ≤ ((k : ℝ) + 1) / 2 - c / Real.log (|s.im| + 2) ∧
      ((k : ℝ) - 1) / 2 + c / Real.log (|s.im| + 2) ≤ s.re
theorem fL_discriminant_zero_free_region : …   -- Δ, both halves, recovered from the general theorem
```

In the abstract normalized layer, with the edge at `Re = 1`, the statement is
`ZFR.L_zero_free_region`. It holds for every `[EData]` for which `L` has polynomial growth on
`3/4 ≤ Re ≤ 11/8`, and the constant is `c = 1/18144`, as for `Δ`.

## Proofs

### Part 1

1. **Normalization on a half-plane** (`Setup.exists_sigma_normalized`). With
   `G(s) = n₀^s a_f(n₀)^{−1} L(f,s)`, we get `|G − 1| ≤ 1/4` on all of `Re s ≥ σ₁`; Hafner only
   needed one line. Consequently `Λ ≠ 0` on `Re ≥ σ₁`, and by the functional equation also on
   `Re ≤ k − σ₁`. So all zeros of `Λ` lie in `k − σ₁ < Re < σ₁`. For a general cusp form `σ₁` can
   exceed `(k+1)/2`, since without an Euler product `L(f,s)` can vanish to the right of the
   critical strip.
2. **Jensen** (`Count.window_right`). The disc has centre `σ₁ + i(T+½)` and radius `d + ¼`, where
   `d = σ₁ − k/2`. It sits inside the disc of radius `d + ½`, which lies in `Re ≥ (k−1)/2`. There
   `‖L‖ ≤ B(1+‖s‖)²` (`fL_growth`, from the PL convexity `fL_line` together with absolute
   convergence). The lower bound at the centre is `|L(c)| ≥ ¾|a_f(n₀)| n₀^{−σ₁}`, which comes from
   `|G − 1| ≤ ¼` and replaces the Euler-product bound used for Δ. Zeros with `Re < k/2` are
   reflected by `s ↦ k − s` into the window at height `−T−1`. The reflection preserves the order
   (`order_reflect`, via Mathlib's `analyticOrderAt_comp_of_deriv_ne_zero`). This gives
   `window_count`, finiteness, and `N(T+1) − N(T) ≪ log T`.
3. **Argument principle on `[k−σ₁, σ₁] × [−T, T]`** (`Symmetry.pi_count_eq_gen`, with
   `ZeroCountRvM.arg_principle_rect`). Only `φ(k−s) = −φ(s)` is used. That holds for either root
   number `i^k = ±1`, so the case `k ≡ 2 mod 4` needs no separate treatment.
   - There is no conjugation symmetry, because the coefficients may be complex. That is why the
     rectangle is symmetric about the real axis instead of having its bottom edge on it.
   - The reflection `ρ ↦ k − ρ` identifies the zeros below the real axis with those above. Hence
     `π(2N_f(T) + N_f⁰) = Re V − Im H(T) + Im H(−T)`, where `V = ∫_{−T}^{T} φ(σ₁+iy) dy`,
     `H(t) = ∫_{k/2}^{σ₁} φ(x+it) dx`, and `N_f⁰` (`realCount`) is the constant number of real
     zeros.
4. **Decomposition** (`RvM.phi_eq_gen`). On `Re s > 0`, `φ = −log(2πn₀) + ψ + G'/G`. The constant
   contributes `−2T log(2πn₀)`.
5. **Gamma.** Cauchy's theorem on `[k/2, σ₁] × [−T, T]` (`gamma_cauchy_gen`) reduces the Gamma
   contribution to `Re ∫_{−T}^{T} ψ(k/2+iy) dy = 2∫₀ᵀ Re ψ(k/2+iy) dy`. The weight `k` is even,
   so `k/2 = m` is a natural number. The asymptotic
   `∫₀ᵀ Re ψ(m+iy) dy = T log T − T + O(log T + m)` (`integral_re_digamma_nat`) follows from the
   case `m = 6` (`ZeroCountRvM.integral_re_digamma_six`) by `ψ(s+1) = ψ(s) + 1/s` and
   `∫₀ᵀ Re 1/(j+iy) dy = arctan(T/j) ∈ [0, π/2]`.
6. **`G'/G` terms.**
   - On the vertical sides, `Re G ≥ ¾` gives a contribution of at most `π`
     (`abs_re_integral_logDeriv_vert`).
   - On the horizontal sides at heights `±T`, the contribution is `O(log T)` by
     `Backlund.backlund_gen`. This is Backlund's method for an arbitrary entire `G`, applied to
     `g(z) = (G(z+iT) + \overline{G(\bar z − iT)})/2`, which is real on the real axis without
     any symmetry of `G`.
7. **General `T`**: move to a non-ordinate in `(T, T+1)`, as in the Δ version (`RvMFinal`).

### Part 2

The proof ports `ZeroFreeRegion/{Continuation,Monotone,Psi,Region,Uniform}` from `Δ` to
`EigenformEdge.EData`. The files are `ZFRData`, `ZFRPsi`, `ZFRRegion` and `ZFREigen`.

1. **Abel continuation of `R(s)`.** `R(s) = Σ λ(n)² n^{−s}` is continued to `Re s > 3/5` using
   Rankin's error term `EData.rs_partial`. For eigenforms that error term is
   `RankinExact.rankinSelberg_exact_general`.
2. **Local positivity of the `Π × Π̃` product.** The local identity
   `ZeroFreeRegion.localD_inv_eq_exp_tsum` is generic and is reused. The Satake parameters and
   local factors come from `EigenformEdge` (`satake`, `L_local`, `rs_local`).
3. **The remaining inputs.**
   - Polynomial growth of `L` near the edge: `Lf_growth`, from `fL_growth`.
   - Edge non-vanishing off the real axis: `L_ne_zero_edge_of_ne`, which is unconditional.
   - The conjugation symmetry `L_conj`, which holds because eigenform coefficients are real.
4. **The left half.** This follows from `Λ(k−s) = i^k Λ(s)`, valid for zeros off the real axis.
5. **The all-heights version.** The zeros with `|Im| ≤ t₀` and `s ≠ −n` form a finite set, a
   subset of `GeneralZeros.zeroSet`. Each lies strictly inside the strip by
   `EigenformEdge.fL_zeros_in_strip`, and that step uses `h0`. A finite set of points strictly
   inside the strip allows a uniform `c`, so no Siegel-type issue arises for a fixed `f`.

## Hypotheses and gaps

- **`h0 : L(f,(k+1)/2) ≠ 0`** is needed only for `fL_zero_free_region_uniform`. It is the
  hypothesis of `EigenformEdge`, discussed in `EIGENFORM_EDGE.md`. It is discharged for `Δ`
  (`fL_discriminant_edge_real`) and, more generally, for every `f` with `f(iy) ≥ 0`. The regions
  for `|Im ρ| ≥ t₀` are unconditional.
- **The constants are ineffective.** `C`, `σ₁`, `t₀` and `c` (in the uniform version) are
  existential.
- **There is no `S(T)` refinement.** The asymptotic ratio `N_f(T) ~ (T/π) log T` is not stated as
  a `Tendsto`, although it is immediate.
- **The zero-free region is stated for eigenforms only.** For a general cusp form there is no
  Euler product, and a region of de la Vallée-Poussin type need not hold. Linear combinations
  can have zeros with `Re > (k+1)/2`, as in the Davenport–Heilbronn phenomenon (this is
  literature, not formalized here).
- **No instance with `n₀ > 1` is formalized**, for example `Δ²`. Only the general theorem is.

## Literature

- Iwaniec–Kowalski, *Analytic Number Theory*, Thm 5.8 (Riemann–von Mangoldt) and Thm 5.10 / §5.3
  (zero-free regions for GL(2) via `L(f×f̄)`).
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §9.2–9.4 (Backlund) and §3.9.
- Hafner (1983), the normalization by the first nonzero coefficient.
- Davenport–Heilbronn (1936), zeros of Dirichlet series without Euler product.
