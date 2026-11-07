# Edge non-vanishing and the PNT for every level-one Hecke eigenform

Lean: `RamanujanTau/EigenformEdge/` (8 files, about 2650 lines, no `sorry`, no new axiom, no
`native_decide`). Build with `nice -n 10 lake build RamanujanTau.EigenformEdge.Main` (exit 0).
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 23 headlines in `Main.lean`.

This generalizes `EdgeNonvanishing/` (docs/EDGE_NONVANISHING.md) and `TauPNT/` +
`WienerIkehara/Main.lean` (docs/TAU_PNT.md, docs/WIENER_IKEHARA.md) from `Δ` to every
normalized level-one Hecke eigenform `f ∈ S_k(SL₂(ℤ))`.

## What "eigenform" means here

Mathlib has no Hecke operators on `CuspForm 𝒮ℒ k`, and the repo has no general eigenform notion
(`HeckeEigenform.lean` covers only `Δ`, through `dim S₁₂ = 1`). So the eigenform property is
stated through the coefficients `a_f(n) = coef f n`:

```lean
structure IsNormalizedEigenform (f : CuspForm 𝒮ℒ (k : ℤ)) : Prop where
  real : ∀ n, (coef f n).im = 0
  one : coef f 1 = 1
  mul : ∀ {m n : ℕ}, m.Coprime n → coef f (m * n) = coef f m * coef f n
  hecke : ∀ {p : ℕ}, p.Prime → ∀ e : ℕ,
    coef f (p ^ (e + 2)) = coef f p * coef f (p ^ (e + 1)) - (p : ℂ) ^ (k - 1) * coef f (p ^ e)
```

These are theorems about every normalized level-one Hecke eigenform (Hecke 1937; the
coefficients are real because the `T_n` are self-adjoint for the Petersson product). They say
which `f` the results are about. They are not unproved analytic inputs about `L(f,s)`. The
structure is inhabited: `isNormalizedEigenform_discriminant` proves it for `Δ`, using Mordell's
multiplicativity and the Hecke recurrence for `τ`.

## Results

Notation: `λ_f(n) = a_f(n)/n^{(k−1)/2}` (`nlam`), `L(f,s) = fL f s` (`HeckeConvexGeneral`).

| statement | Lean | hypotheses | evidence |
|---|---|---|---|
| Euler product; `L(f,s) ≠ 0` for `Re s > (k+1)/2` | `L_eulerProduct`, `fL_ne_zero_of_gt` | `hf` | (1) |
| **`L(f,(k+1)/2+it) ≠ 0` for `t ≠ 0`** | `fL_ne_zero_edge_of_ne` | `hf` | (1) |
| `f(iy) ≥ 0` on `y > 0` ⇒ `L(f,σ) ≠ 0` for real `σ > 0` | `fL_real_ne_zero_of_imagAxis_nonneg` | `hf`, positivity | (1) |
| Δ edge theorem recovered from the general one | `fL_discriminant_ne_zero_edge` | none | (1) |
| **`L(f,(k+1)/2+it) ≠ 0` for all `t`** | `fL_ne_zero_edge` | `hf`, `h0` | (2) |
| no zeros on `Re s ≥ (k+1)/2`, nor on `Re s ≤ (k−1)/2` except `s = −n` | `fL_ne_zero_of_ge`, `fL_ne_zero_of_le` | `hf`, `h0` | (2) |
| nontrivial zeros lie in `(k−1)/2 < Re s < (k+1)/2` | `fL_zeros_in_strip` | `hf`, `h0` | (2) |
| smoothed PNT: `∑_p λ_f(p) log p · p^{−σ}` has a finite limit as `σ → 1⁺` | `eigen_PNT_smoothed` | `hf`, `h0` | (2) |
| infinitely many `p` with `a_f(p) > 0`, and infinitely many with `a_f(p) < 0` | `eigen_prime_sign_changes` | `hf`, `h0`, `[DeligneBoundF f]` | (2) |
| `∑_{p<N} λ_f(p) log p = o(N)` | `eigen_PNT_lam` | `hf`, `h0`, `[DeligneBoundF f]` | (2) |
| **`∑_{p<N} a_f(p) log p = o(N^{(k+1)/2})`** | `eigen_PNT` | `hf`, `h0`, `[DeligneBoundF f]` | (2) |
| `∑_{p<N} τ(p) log p = o(N^{13/2})` (Δ recovered) | `tau_PNT_recovered` | `[DeligneBound]` | (2) |

```lean
theorem fL_ne_zero_edge_of_ne (hf : IsNormalizedEigenform f) {t : ℝ} (ht : t ≠ 0) :
    fL f (((k : ℂ) + 1) / 2 + t * I) ≠ 0
theorem fL_ne_zero_edge (hf : IsNormalizedEigenform f) (h0 : fL f (((k : ℂ) + 1) / 2) ≠ 0) (t : ℝ) :
    fL f (((k : ℂ) + 1) / 2 + t * I) ≠ 0
theorem fL_zeros_in_strip (hf) (h0) {s : ℂ} (h : fL f s = 0) (hn : ∀ n : ℕ, s ≠ -n) :
    ((k : ℝ) - 1) / 2 < s.re ∧ s.re < ((k : ℝ) + 1) / 2
theorem eigen_PNT (hf) (h0) [DeligneBoundF f] :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, (coef f p).re * Real.log p) /
      (N : ℝ) ^ (((k : ℝ) + 1) / 2)) atTop (𝓝 0)
```

## Named hypotheses

- **`h0 : fL f ((k+1)/2) ≠ 0`, the real edge point.** The positivity argument cannot reach
  `t = 0`. There `F(σ)` becomes `ζ(σ)L(σ)⁴(ζ(2σ)R(σ))⁴`, with a pole of order 5 against a zero of
  order 4. The two-factor version `ζ L² ζ(2s)R` has pole order 2 against zero order 2, so it only
  rules out a double zero. For `Δ` the repo used `Δ(iy) > 0`. Here that becomes the theorem
  `fL_real_ne_zero_of_imagAxis_nonneg`: if `f(iy) ≥ 0` then `L(f,σ) ≠ 0` for real `σ > 0`.
  The proof is that the Mellin integral of a nonnegative function vanishes only if `f(iy) = 0`
  a.e., which would make every `a_f(n)` zero (Mathlib's `LSeries_eventually_eq_zero_iff'`).
  Positivity on the imaginary axis holds for `Δ`. It also holds for `ΔE₄` and `ΔE₄²` (weights
  16 and 20), since `E₄(iy) > 0`, but those forms are not formalized as eigenforms here. It fails
  for `ΔE₆`, because `E₆(i) = 0`.
  In general `L(f,(k+1)/2) ≠ 0` needs more than this method gives. The standard routes are
  Landau's lemma applied to `ζ²L(f)²L(Sym²f)`, which needs the continuation of `R(s)` to
  `Re s ≤ 1/2`, or Jacquet–Shalika. In the abstract layer this hypothesis is the class
  `RealEdge`.
- **`[DeligneBoundF f]`**: `a_f(p)² ≤ 4p^{k−1}`. This is Deligne's theorem (1974), the analogue
  of the repo's `DeligneBound`, which supplies the `Δ` instance. It is used for the majorant
  `|Λ_f| ≤ 2Λ` and for the `k ≥ 2` terms of `log ζ(2s)R(s)`, exactly as in `TauPNT`.
- **Wiener–Ikehara is not a hypothesis.** The proved `WienerIkehara.wienerIkehara` is used.

## Structure of the proof

The proof is abstracted once and then specialized.

- `Data.lean`: class `EData`. Its fields are real `λ(n)` with `λ(1) = 1` and `λ(0) = 0`,
  multiplicative, satisfying `λ(p^{e+2}) = λ(p)λ(p^{e+1}) − λ(p^e)`; Rankin's
  `|∑_{n≤N} λ(n)² − cN| ≤ CN^{3/5}` with `c > 0`; and an entire `L` with
  `L = ∑ λ(n)n^{−s}` on `Re s > 1` and `L(s̄) = conj L(s)`.
  From these fields alone the file proves:
  - `R(s) = ∑ λ²n^{−s}`: summability, the Abel bound `R − cζ = O(‖s‖/(σ−3/5))`, and the Euler
    product;
  - absolute convergence of `∑ λ n^{−s}`, using `|λ| ≤ (1+λ²)/2`;
  - the Euler product of `L` (generalizing `HeckeZeros.tauL_eulerProduct`) and `L ≠ 0` on
    `Re s > 1`;
  - the Satake parameters, `‖α_p‖² ≤ p` without Deligne, and the local factors.
- `Edge.lean`: the 25-parameter positivity argument for `Π = 1 ⊞ f|·|^{it} ⊞ f|·|^{−it}`,
  reusing `EdgeNonvanishing.Local`. This gives `L(1+it) ≠ 0` for `t ≠ 0`.
- `PNT.lean`, `PNTSigns.lean`: `TauPNT` copied onto `EData`. Partial summation is generalized
  to weight `n^r` with `r > 0`.
- `Eigenform.lean`: `IsNormalizedEigenform`, and `eigenData f hf : EData` with
  `λ = a_f(n)/(√n)^{k−1}`, `L(s) = fL f (s+(k−1)/2)` and `c = rsConst f`. The construction uses
  `RankinExact.rankinSelberg_exact_general`, `HeckeConvexGeneral.fL_eq_LSeries`/`fL_entire`,
  `HardyZerosGeneral.heckeLambda_conj` and `rsConst_pos`. The file also contains the edge
  headlines, and the strip theorem via `fL_functional_equation`.
- `RealPoint.lean`: imaginary-axis positivity implies the real point; the `Δ` instance.
- `PNTEigen.lean`: `DeligneBoundF`, and the PNT and sign-change corollaries for `f` and for `Δ`.

## Gaps

- The real edge point `L(f,(k+1)/2) ≠ 0` for general `f` (see above). Discharging it would take
  the meromorphic continuation of the Rankin–Selberg `R(s)` to `Re s > 1/2` (or the entire
  `ζ(2s)R(s)`) plus Landau's lemma.
- Deligne's bound for general `f` remains a named class. A Deligne-free PNT would need
  `L(Sym²f, 1+it) ≠ 0`; see TAU_PNT.md.
- There is no zero-free region and no error term.
- Only `Δ` is exhibited as an instance. Other eigenforms (`ΔE₄`, …) would need their own
  multiplicativity proofs, which require Hecke operators that are missing from Mathlib.

## Literature

Hecke (1937); Rankin (1939); Ogg, *Modular forms and Dirichlet series* (1969); Moreno (1974);
Jacquet–Shalika (1976); Deligne (1974); Iwaniec–Kowalski, *Analytic Number Theory*, §5.
