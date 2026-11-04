# Rationality of the Kloosterman L-function and amplification (`RamanujanTau/KloostermanL/`)

> **Update (2026-11-04):** `StepanovKloostermanEventually` is proved (`StepanovAS.stepanovKloostermanEventually`), so
> `WeilPrimeBound` and `τ(n) = O(n^{23/4+ε})` are unconditional (`StepanovAS.weilPrimeBound`,
> `StepanovAS.tau_isBigO_23_4_unconditional`); see [STEPANOV_ARTIN_SCHREIER](STEPANOV_ARTIN_SCHREIER.md).
> The text below describes this directory as written.

**Status (2026-11-04).** Parts (1) rationality and (3) amplification of the Weil-bound route are
proved, axiom-clean. So Weil's bound `WeilKloosterman.WeilPrimeBound`, and with it
`τ(n) = O(n^{23/4+ε})`, now follows from one named hypothesis, `StepanovKloosterman`: a bound
`|K_r| ≤ C·p^{r/2}` for Kloosterman sums over `F_{p^r}`. That hypothesis is part (2) of the route
and is the target of the Stepanov track. No sorry, no new axiom, no `native_decide`.

Build (only these files):
`nice -n 10 lake build RamanujanTau.KloostermanL.Main`. The `#print axioms` block at the end of
`Main.lean` prints `[propext, Classical.choice, Quot.sound]` for every headline theorem.
These files were written outside the root import; they have since been added to `RamanujanTau.lean`. Nothing in `WeilKloosterman/` or
`TauBound/` was modified; both are only imported.

| File | Lines | Content |
|---|---|---|
| `KloostermanL/Amplify.lean` | 53 | complex amplification lemma |
| `KloostermanL/Lambda.lean` | 253 | the character `λ` on `F[X]`, its multiplicativity, and the degree sums `A_n` |
| `KloostermanL/Newton.lean` | 206 | `n A_n = Σ_{k=1}^n V_k A_{n−k}`, by unique factorization |
| `KloostermanL/Roots.lean` | 170 | `V_k` equals the Kloosterman sum over any extension of degree `k` |
| `KloostermanL/Main.lean` | 209 | rationality, `K_r = −(α^r+β^r)`, the hypothesis `StepanovKloosterman`, Weil's bound |
| `scripts/kloostermanL/check_rationality.py` | | numerical check |

## Notation

`F` is a finite field with `q` elements, `ψ : AddChar F ℂ`, and `a, b ∈ F`.

On `f ∈ F[X]`, define `λ(f) = 0` if `f(0) = 0`. Otherwise
`λ(f) = ψ(−a·nextCoeff f − b·f₁/f₀)`, where `f₀, f₁` are the coefficients of `X⁰` and `X¹`.
For `f = X^n + c₁X^{n−1} + … + c_n` this is `ψ(−a c₁ − b c_{n−1}/c_n)`.

The definitions in Lean:

* `degSum n = A_n = Σ_{f monic, deg f = n} λ(f)`;
* `klF ψ a b = Σ_{u ∈ F^×} ψ(a u + b u⁻¹)`;
* `klL L ψ a b = Σ_{x ∈ L^×} ψ(Tr_{L/F}(a x + b x⁻¹))`;
* `vM k = Σ_{P monic irreducible, deg P ∣ k} deg P · λ(P)^{k/deg P}`;
* `klGF p r a b = klL (GaloisField p r) ZMod.stdAddChar a b`. This is the brief's `K_r`.

## Evidence levels

### (1) Lean, axiom-clean, no hypotheses

| Theorem | Statement |
|---|---|
| `norm_add_le_two_sqrt_of_powSum_bound` | `αβ = p > 0` and `‖α^r+β^r‖ ≤ C√p^r` for all `r ≥ r₀` ⟹ `‖α‖ ≤ √p`, `‖β‖ ≤ √p`, `‖α+β‖ ≤ 2√p` |
| `lam_mul` | `λ(fg) = λ(f)λ(g)` for monic `f, g` |
| `degSum_zero`, `degSum_one`, `degSum_two`, `degSum_eq_zero` | `A₀ = 1` and `A₁ = klF`. For primitive `ψ` and `a, b ≠ 0`: `A₂ = q`. For `ψ ≠ 1`, `a ≠ 0`, `n ≥ 3`: `A_n = 0`. |
| `newton_identity` | `n A_n = Σ_{k ∈ [1,n]} vM k · A_{n−k}`, for all `n` |
| `vM_eq_klL` | for every finite extension `L/F` with `[L:F] = k ≥ 1`, `vM k = klL L ψ a b` |
| **`kloosterman_L_rational`** | the facts above together: `L(T) = 1 + K₁T + qT²`, and `T L'/L = Σ_k K_k T^k` in coefficient form |
| `vM_recurrence` | `K_n = −K₁K_{n−1} − qK_{n−2}` for `n ≥ 3` |
| **`klL_eq_neg_pow_add`** | `α + β = −K₁` and `αβ = q` imply `klL L = −(α^r + β^r)`, where `r = [L:F] ≥ 1` |
| `klF_eq_kl` | `klF ZMod.stdAddChar a b = TauBound.kl p a b`. The `K₁` here is exactly the `kl p 1 b` in `WeilPrimeBound`. |
| **`klGF_eq_neg_pow_add`** | for `b ≠ 0` there exist `α, β ∈ ℂ` with `α + β = −kl p 1 b`, `αβ = p`, and `klGF p r 1 b = −(α^r+β^r)` for all `r ≥ 1` |

`newton_identity` and `vM_eq_klL` together give `exp(Σ_r K_r T^r/r) = 1 + K₁T + qT²`. That
statement is not written as a `PowerSeries` identity in Lean. The coefficient form plus the
`α, β` form are what the bound uses.

### (2) Lean, conditional on a named hypothesis (axiom-clean)

This is the exact hypothesis shape for the Stepanov track:

```lean
def StepanovKloosterman : Prop :=
  ∃ C : ℝ, ∀ (p : ℕ) (hp : p.Prime), haveI : Fact p.Prime := ⟨hp⟩
    ∀ r : ℕ, 1 ≤ r → ∀ b : ZMod p, b ≠ 0 → ‖klGF p r 1 b‖ ≤ C * Real.sqrt p ^ r

-- weaker, and already sufficient: C and r₀ may depend on p and b
def StepanovKloostermanEventually : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), haveI : Fact p.Prime := ⟨hp⟩
    ∀ b : ZMod p, b ≠ 0 → ∃ (C : ℝ) (r₀ : ℕ), ∀ r : ℕ, r₀ ≤ r →
      ‖klGF p r 1 b‖ ≤ C * Real.sqrt p ^ r
```

`klGF_def` lets you unfold `klGF` with any `Fintype (GaloisField p r)` instance.

| Theorem | Statement |
|---|---|
| `weilPrimeBound_of_stepanovEventually` | `StepanovKloostermanEventually → WeilKloosterman.WeilPrimeBound` |
| **`weilPrimeBound_of_stepanov`** | `StepanovKloosterman → WeilKloosterman.WeilPrimeBound` |
| **`tau_isBigO_23_4_of_stepanov`** | `StepanovKloosterman → ∀ ε > 0, τ(n) = O(n^{23/4+ε})` |

Because the eventual form suffices, the Stepanov track may:

* assume `r` is large relative to the degree. Stepanov's method needs `q = p^r ≫ deg`.
* use any constant depending on `p`.

The track could also prove the bound only for even `r`. That case needs a small variant of
`norm_le_of_powSum_bound`, where any infinite set of exponents works, and it has not been written.

### (4) Numerical

`scripts/kloostermanL/check_rationality.py` checks, for `p ∈ {2, 3, 5, 7}`, all `a, b ≠ 0`,
and `r ≤ 4` (`r ≤ 3` for `p = 7`):

* the recurrence `K_r = −K₁K_{r−1} − pK_{r−2}` (maximum error 1.4e−13);
* `A_n = 1, K₁, p, 0, 0` for `n = 0, …, 4`;
* `|K₁| ≤ 2√p`.

## How the proof goes

1. **Multiplicativity.** For monic `f, g`:
   * `nextCoeff(fg) = nextCoeff f + nextCoeff g` (`Monic.nextCoeff_mul`);
   * `(fg)₁/(fg)₀ = f₁/f₀ + g₁/g₀`.

   No reversed polynomials are needed for this step.
2. **Degree sums.**
   * For `n ≥ 3`: the shift `f ↦ f + tX^{n−1}` is a bijection of the monic polynomials of degree `n`.
     It multiplies `λ` by `ψ(−at)`, so `A_n = 0`.
   * `A₁` is `K₁`, after the substitution `u ↦ −u`.
   * `A₂ = Σ_{c₀≠0} Σ_{c₁} ψ(c₁(−a − b/c₀)) = q`, using `AddChar.sum_mulShift`.
3. **Newton identity**, with no Euler product.
   * By `normalizedFactors`: `deg f = Σ_P v_P(f) deg P`, and `P^j ∣ f ⟺ j ≤ v_P(f)`. So
     `deg f = Σ_{P monic irreducible} Σ_{1≤j≤n} [P^j ∣ f] deg P`.
   * Summing `λ(f)` over the multiples of `P^j` of degree `n` gives `λ(P)^j A_{n−j·deg P}`, via `h ↦ P^j h`.
   * Regroup by `k = j·deg P`.
4. **Roots.**
   * Write `K_k = Σ_{x∈L} λ(minpoly x)^{k/deg}`. The point `x = 0` contributes `λ(X) = 0`.
     For `x ≠ 0`, use `trace_eq_finrank_mul_minpoly_nextCoeff`. Use
     `minpoly x⁻¹ = (minpoly x)(0)⁻¹ · reverse(minpoly x)`, proved by `minpoly.unique` with a
     reverse-degree argument. It gives `Tr x⁻¹ = (k/d)·(−P₁/P₀)`.
   * Fibre count: each monic irreducible `P` with `deg P ∣ k` has exactly `deg P` roots in `L`. The
     inputs are:
     * an `F`-embedding `F[X]/(P) → L`, from `FiniteField.nonempty_algHom_of_finrank_dvd`;
     * normality, from the `IsGalois` instance for finite fields;
     * separability, from `PerfectField`;
     * `card_rootSet_eq_natDegree`.
5. **Recurrence.** From step 3, using step 2's values of `A_n`:
   * `n = 1, 2` give `K₁` and `K₂ = 2q − K₁²`;
   * `n ≥ 3` gives the 3-term recurrence.

   Strong induction then gives `K_r = −(α^r+β^r)`. The roots `α, β` come from
   `IsAlgClosed.exists_pow_nat_eq`.
6. **Amplification.** Suppose `|α| > √p`. Then `|β| = p/|α| < √p`, so
   `|α|^r − √p^r ≤ |K_r| ≤ C√p^r`. That makes `(|α|/√p)^r` bounded, a contradiction.

## What remained for `WeilPrimeBound` (now done in `StepanovAS/`)

Only part (2), `StepanovKloosterman` or its eventual form: a Stepanov-type bound for
`Σ_{x∈F_q^×} ψ(Tr(x + b/x))` over `F_q`, `q = p^r`. The constant must not depend on `r`. That is
the Artin–Schreier curve `y^p − y = x + b/x`.

## Literature

* Weil, *On some exponential sums*, PNAS 34 (1948).
* Iwaniec–Kowalski, *Analytic Number Theory*, §11.7: rationality via `λ` on monic polynomials.
* Schmidt, *Equations over Finite Fields*, Ch. II: Stepanov's method for Artin–Schreier curves.
