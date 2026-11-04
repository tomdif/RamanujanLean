# Hecke's theorem for Ramanujan's L-function (`RamanujanTau/HeckeL/`)

**Status (2026-11-04).** Hecke's theorem (1936) for `Δ`, proved **unconditionally and
axiom-clean** (evidence level 1):

    Λ(s) = (2π)^{−s} Γ(s) L(Δ,s),     L(Δ,s) = ∑ τ(n) n^{−s}   (Re s > 7),

extends to an **entire** function, **bounded on every vertical strip**, with
**`Λ(12 − s) = Λ(s)`** (root number `+1`, as `12 ≡ 0 mod 4`). Consequently `L(Δ,s)` is entire,
vanishes at `s = 0, −1, −2, …`, and these are its **only real zeros**. In particular
**`L(Δ,6) > 0`**.

No sorry, no new axiom, no `native_decide`. Every headline prints
`[propext, Classical.choice, Quot.sound]`. There are 4 files and 563 lines. Build only these:

    nice -n 10 lake build RamanujanTau.HeckeL.Positivity RamanujanTau.HeckeL.Growth

Nothing outside `RamanujanTau/HeckeL/` and this write-up was modified. The root file does not
import the directory.

## Route

The proof follows the brief.

* `f(t) = Δ(it)`. Here `heckeF t := (Δ ∘ ofComplex)(t·i)`, which is continuous on `(0,∞)` by
  `UpperHalfPlane.mdifferentiable_iff`.
* `f(1/t) = t¹² f(t)`. This comes from Mathlib's `discriminant_S_invariant`,
  `S·(it) = i/t` and `(it)¹² = t¹²`.
* `f(t) = O(e^{−2πt})` as `t → ∞`, by `CuspFormClass.exp_decay_atImInfty`. Hence `f = O(t^r)`
  for every `r`.
* So `(f, f)` is a Mathlib **`StrongFEPair ℂ`** with `k = 12` and `ε = 1` (`heckePair`). Mathlib
  then supplies `Λ = mellin f`, entire, and `Λ(k − s) = ε·Λ_symm(s)`.
* Dirichlet series. For `t > 0`, `Δ(it) = ∑ τ(n) e^{−2πnt}` (`hasSum_qExpansion` plus the
  bridge `heckeData.coeff_discriminant`). Then Mathlib's `hasSum_mellin` (termwise Γ-integral)
  applies, using the summability `∑|τ(n)|(2πn)^{−σ} < ∞` for `σ > 7` (`LSeriesSummable_tau`,
  Hecke's bound).
* Boundedness on strips: `‖t^{s−1}‖ ≤ t^{a−1} + t^{b−1}`. This is the pattern of
  `RankinError/RSFE.rsFE_Λ₀_bdd`.

Two results go beyond the brief.

* **Positivity on the real axis.** `Δ(it)` is real, because its q-expansion has real
  coefficients. It is nonzero (`discriminant_ne_zero`) and eventually positive: by Mathlib's
  `discriminant_eq_q_prod` and `tendsto_atImInfty_tprod_one_sub_eta_q_pow`, `Δ(it)/q → 1`.
  The intermediate value theorem then gives `Δ(it) > 0` for every `t > 0`. So
  `Λ(σ) = ∫₀^∞ Δ(it)t^{σ−1}dt > 0` for every real `σ`.
* **Growth on the reflected line, without Stirling.** On `Re s = 4`,
  `Γ(12−s) = (11−s)(10−s)(9−s)(8−s)Γ(8−s)` and `8 − s = s̄`, so `|Γ(8−s)| = |Γ(s)|` exactly.

## Headline theorems (evidence level 1, all in namespace `RamanujanTau.HeckeL`)

`tauC n = (τ n : ℂ)`. `heckeLambda = heckePair.Λ = mellin heckeF`.
`tauL s = (2π)^s · Γ(s)⁻¹ · heckeLambda s`, which is the entire continuation of `L(Δ,s)`.
Mathlib's `Γ⁻¹` is entire, and Mathlib sets `Γ(−n) = 0`.

| Theorem | File | Statement |
|---|---|---|
| `heckePair` | Basic | `StrongFEPair ℂ` with `f = g = heckeF`, `k = 12`, `ε = 1` |
| `heckeF_inv` | Basic | `t > 0 → heckeF (1/t) = t¹² · heckeF t` |
| `hasSum_heckeF` | Basic | `t > 0 → HasSum (n ↦ τ(n)·e^{−2πnt}) (heckeF t)` |
| `mellin_heckeF` | Basic | `7 < Re s → mellin heckeF s = (2π)^{−s} Γ(s) LSeries tauC s` |
| **`heckeLambda_entire`** | Basic | `Differentiable ℂ heckeLambda` |
| **`heckeLambda_functional_equation`** | Basic | `∀ s, heckeLambda (12 − s) = heckeLambda s` |
| **`heckeLambda_eq`** | Basic | `7 < Re s → heckeLambda s = (2π)^{−s} Γ(s) LSeries tauC s` |
| **`heckeLambda_bdd_strip`** | Basic | `∀ a b, ∃ L, ∀ s, a ≤ Re s ≤ b → ‖heckeLambda s‖ ≤ L` |
| **`tauLSeries_entire`** | Main | `Differentiable ℂ tauL` |
| **`tauL_eq_LSeries`** | Main | `7 < Re s → tauL s = LSeries tauC s` |
| `heckeLambda_eq_tauL` | Main | `(∀ n:ℕ, s ≠ −n) → heckeLambda s = (2π)^{−s} Γ(s) tauL s` |
| **`tauLSeries_zeros_trivial`** | Main | `∀ n : ℕ, tauL (−n) = 0` |
| `tauL_functional_equation` | Main | if `s` and `12 − s` are not in `−ℕ`: `(2π)^{−(12−s)}Γ(12−s) tauL(12−s) = (2π)^{−s}Γ(s) tauL(s)` |
| **`tauLSeries_center`** | Main | `heckeLambda 6 = (2π)^{−6} · 120 · tauL 6` |
| `heckeLambda_deriv_center` | Main | `deriv heckeLambda 6 = 0` |
| **`heckeU_pos`** | Positivity | `t > 0 → 0 < Re Δ(it)`; and `heckeF_real`: `Δ(it)` is real |
| **`heckeLambda_pos`** | Positivity | `∀ σ : ℝ, Im Λ(σ) = 0 ∧ 0 < Re Λ(σ)` |
| `heckeLambda_neg_nat_ne_zero` | Positivity | `heckeLambda (−n) ≠ 0`: the trivial zeros come only from `Γ` |
| **`tauL_real_eq_zero_iff`** | Positivity | `∀ σ : ℝ, tauL σ = 0 ↔ ∃ n : ℕ, σ = −n` |
| `tauL_pos` | Positivity | `0 < σ → Im tauL(σ) = 0 ∧ 0 < Re tauL(σ)` |
| **`tauLSeries_center_pos`** | Positivity | `Im tauL(6) = 0 ∧ 0 < Re tauL(6)`, i.e. `L(Δ,6) > 0` |
| `LSeries_tau_real_pos` | Positivity | `7 < σ → Im L(Δ,σ) = 0 ∧ 0 < Re L(Δ,σ)` |
| **`tauL_bound_re_four`** | Growth | `∃ C, ∀ s, Re s = 4 → ‖tauL s‖ ≤ C ‖11−s‖‖10−s‖‖9−s‖‖8−s‖`, so `L(Δ,4+it) ≪ (1+\|t\|)⁴` |

## Numerical sanity check (evidence level 4)

The script is `scripts/heckel/hecke_check.gp`. It uses PARI `lfuncreate` with
`[ramanujantau, 0, [0,1], 12, 1, 1]`, 40 digits and `nbthreads = 1`.

* `lfuncheckfeq = −195` (in bits), so the functional equation holds to about 2^{−195} ≈ 10^{−58}.
* `|Λ(s) − Λ(12−s)| < 10^{−59}` at `s = 3+2i`, `6+5i`, `1.3−0.7i` and `10+i`.
* `L(Δ,6) = 0.79212283864603056935…` and `Λ(6) = 120(2π)^{−6}L(Δ,6) = 0.0015448793603950…`.
  The numerical `Λ'(6)` is `0` to 50 digits.
* `L(Δ,0) = L(Δ,−1) = L(Δ,−2) = 0`.
* `Λ(σ) > 0` at `σ ∈ {−3.5, −0.5, 0.5, 3, 6, 9, 12.5}`, and the symmetry `Λ(−0.5) = Λ(12.5)`
  is visible. `L(Δ,−0.5) < 0` matches the sign `Γ(−0.5) < 0`.
* `tauL_bound_re_four`: `|L(4+iT)|` against the proved bound `C∏|j−s|` (with
  `C = (2π)^{−4}∑|τ(n)|n^{−8}`) is 10.0 ≤ 13.1 at `T = 10`, 5.46e4 ≤ 7.70e4 at `T = 100`, and
  7.01e8 ≤ 7.66e8 at `T = 1000`.

## Gaps and what is not done

* **The convexity bound `|L(Δ,6+it)| ≪ |t|^{1+ε}` is not formalized.**
  * What is needed: Phragmén–Lindelöf between `Re s = 7+ε`, where the series converges
    absolutely, and `Re s = 5−ε`. Mathlib has `PhragmenLindelof.vertical_strip`. What is
    missing is an a priori bound for `Γ(s)⁻¹` inside the strip, plus `|Γ(12−s)/Γ(s)|` on
    non-integer lines (Stirling). This was not taken from the concurrent Stirling agent.
  * The integer-line trick gives a weaker version. Use lines `4` and `8`, where the Γ-ratios are
    exact polynomials as in `tauL_bound_re_four`. Interpolating needs only PL and a crude bound
    on `1/Γ` (for example from `Γ(s)Γ(1−s) = π/sin πs` and `|Γ(z)| ≤ Γ(Re z)`). It would give
    `L(Δ,6+it) ≪ |t|²`. Estimate: 250–400 lines.
  * The sharp convexity `|t|^{1/2+ε}` needs `∑|τ(n)|n^{−σ} < ∞` for `σ > 13/2`. That follows
    from Rankin–Selberg (`∑_{n≤N}τ(n)² ≪ N^{12}`, available in `RankinSelberg`/`RankinError`) by
    Cauchy–Schwarz, plus Stirling on non-integer lines.
* `tauL_functional_equation` is stated away from `−ℕ` and `12 + ℕ`, because Mathlib's `Γ` is
  `0` at its poles. The clean statement is `heckeLambda_functional_equation` for `Λ`.
* Not done: the Euler product of the continuation off `Re s > 7`, zeros off the real axis, and
  GRH. All of these are open or out of scope.

## Literature

* E. Hecke, *Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung*,
  Math. Ann. 112 (1936).
* Iwaniec–Kowalski, *Analytic Number Theory*, §14.
* D. Zagier, *Elliptic modular forms and their applications* (in *The 1-2-3 of Modular Forms*),
  §3. The positivity of `Δ(iy)` is immediate from the product formula.
* Mathlib's `Mathlib.NumberTheory.LSeries.AbstractFuncEq` (Loeffler), which supplies the
  FE-pair machinery.
