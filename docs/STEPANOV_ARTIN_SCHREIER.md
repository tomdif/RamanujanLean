# Stepanov's method for the Kloosterman curve, and Weil's bound unconditionally (`RamanujanTau/StepanovAS/`)

**Status (2026-11-04).** `KloostermanL.StepanovKloostermanEventually` is proved. With
`weilPrimeBound_of_stepanovEventually` from `KloostermanL/Main.lean`, this gives Weil's bound
`WeilKloosterman.WeilPrimeBound`, `|S(1,b;p)| ≤ 2√p`, and `τ(n) = O(n^{23/4+ε})`, all with no
hypotheses. No sorry, no new axiom, no `native_decide`. Every headline theorem prints
`[propext, Classical.choice, Quot.sound]`.

Build (only these files): `nice -n 10 lake build RamanujanTau.StepanovAS.Main`. The `#print axioms`
block at the end of `Main.lean` covers the headlines. These files were written outside the root
import; they have since been added to `RamanujanTau.lean`. Nothing in `KloostermanL/`, `WeilKloosterman/`, `TauBound/` or `Stepanov/` was
modified; the first three are only imported.

| File | Lines | Content |
|---|---|---|
| `StepanovAS/Hasse.lean` | 70 | Hasse derivatives in char `p`: polynomials in `X^{p^s}` are constants for orders `< p^s`; multiplicity from vanishing Hasse derivatives |
| `StepanovAS/Aux.lean` | 309 | abstract Stepanov bound with Hasse derivatives (auxiliary polynomial, dimension count, nonvanishing by distinct degrees, root counting) |
| `StepanovAS/Kloosterman.lean` | 241 | the curve `y^p − y = x + b/x`: the polynomials `Y`, `Z`, the identity `Y(x)x^e = Z(x)` on trace fibres, degrees, parameter choice, fibre bound |
| `StepanovAS/Main.lean` | 156 | fibre decomposition of `K_r`, from one-sided fibre bounds to `\|K_r\|`, then `StepanovKloostermanEventually`, Weil, τ |
| `scripts/stepanovAS/check_counts.py` | | numerical check |

## Headline theorems (evidence level 1: Lean, axiom-clean, no hypotheses)

| Theorem | Statement |
|---|---|
| `hasseDeriv_mul_expand` | `ℓ < p^s` ⟹ `D^{(ℓ)}(f · expand (p^s) g) = D^{(ℓ)} f · expand (p^s) g` (char `p`) |
| `le_rootMultiplicity_of_hasseDeriv` | `f ≠ 0` and `D^{(ℓ)}f(x) = 0` for all `ℓ < M` ⟹ `M ≤ rootMultiplicity x f` |
| **`stepanov_hasse_card_le`** | abstract Stepanov bound: `M·\|S\| ≤ A − 1 + q(J−1) + (P−1)·deg Y` (hypotheses below) |
| `eval_Y_mul_eq_Z` | on `S_c`: `Y(x)·x^{p^{s−1}} = Z(x)` |
| **`card_traceFiber_le`** | `[L:F_p] = s+t`, `1 ≤ s ≤ t`, `3 ≤ t`, any `b, c`: `#{x ∈ L^× : Tr(x + b/x) = c} ≤ p^{s−1}p^t + 3p·p^t` (i.e. `q/p + 3p·p^t`) |
| `sum_units_eq_sum_fiber` | `Σ_{x∈L^×} ψ(Tr(x + b/x)) = Σ_{c∈F_p} #S_c · ψ(c)` |
| `norm_sum_le_of_fiber_le` | `ψ ≠ 1` and `#S_c ≤ B` for all `c` ⟹ `\|Σ_c #S_c ψ(c)\| ≤ pB − (q−1)` |
| **`norm_klL_le`** | `[L:F_p] = r ≥ 6`: `\|K_r(1,b)\| ≤ 3p²·p^{r−⌊r/2⌋} + 1` |
| `norm_klGF_le` | `r ≥ 6`: `‖klGF p r 1 b‖ ≤ (3p²+1)√p · √p^r` |
| **`stepanovKloostermanEventually`** | `KloostermanL.StepanovKloostermanEventually`, with `C = (3p²+1)√p` and `r₀ = 6` |
| **`weilPrimeBound`** | `WeilKloosterman.WeilPrimeBound`: `\|S(1,b;p)\| ≤ 2√p` for all primes `p`, `b ≢ 0` |
| **`tau_isBigO_23_4_unconditional`** | `∀ ε > 0, τ(n) = O(n^{23/4+ε})` |

## The argument

Let `q = p^r`, `r = s + t` with `1 ≤ s ≤ t`, `Q = p^s`, `e = p^{s−1}`, and
`S_c = {x ∈ F_q^× : Tr(x + b/x) = c}`.

1. **Splitting the trace.** For `x ∈ F_q^×` we have `Tr(x + b/x) = Σ_{i<r}(x^{p^i} + b x^{−p^i})`
   (`FiniteField.algebraMap_trace_eq_sum_pow`, Frobenius, `b^{p^i} = b`). Split this into `i < s`
   (the low part `A(x)`) and `s ≤ i < r`. Using `x^q = x`, the high part times `x` is
   `Y(x) = Σ_{i<t}(x^{q+p^{s+i}} + b x^{q−p^{s+i}})`. Here `Y = expand Q Y₀` is a polynomial in
   `X^Q`, of degree `q + q/p`, and it has no negative powers. On `S_c`, `Y(x) = x(c − A(x))`, so
   `Y(x)x^e = Z(x)` with `Z = cX^{e+1} − Σ_{i<s}(X^{e+1+p^i} + bX^{e+1−p^i})` and `deg Z ≤ 2e+1`.
2. **Auxiliary polynomial.** Let `Φ = Σ_{j<J, k<p} r_{jk}(X) X^{qj} Y^k` with `deg r_{jk} < A = q/p`.
   For `ℓ < Q`, `X^{qj}Y^k` is a polynomial in `X^Q`, so `D^{(ℓ)}Φ = Σ D^{(ℓ)}(r_{jk}) X^{qj} Y^k`
   (Lucas-free proof: `(1+X)^{Qm} = expand Q ((1+X)^m)`). On `S_c` this gives
   `x^{e(p−1)} D^{(ℓ)}Φ(x) = Ψ_ℓ(x)`, where `Ψ_ℓ = Σ D^{(ℓ)}(r_{jk}) X^j Z^k X^{e(p−1−k)}`, and
   `deg Ψ_ℓ < A + J + (p−1)(2e+1)`.
3. **Dimension count.** With `M = Q`, require `Ψ_ℓ = 0` for all `ℓ < M`. That is
   `M(A + J + (p−1)(2e+1))` linear conditions on `JpA` unknowns. With `J = p^{s−1} + 2p`, `s ≤ t`
   and `t ≥ 3`, the unknowns outnumber the conditions (`arith_dim`).
4. **Nonvanishing.** The degree of the `(j,k)` term is `n + q(j+k) + k·q/p`, where `n < q/p` and
   `k < p`. These are distinct digit expansions, so the leading terms cannot cancel and `Φ ≠ 0`
   (`exps_inj`, `degree_sum_eq_of_disjoint`). The multiplicity theorem in Hasse-derivative form
   holds in every characteristic. So `Q·|S_c| ≤ deg Φ`, which gives `|S_c| ≤ q/p + 3p·p^t`
   (`arith_card`).
5. **Character sum.** `K_r = Σ_c ψ(c)#S_c = Σ_c ψ(c)(#S_c − B)`, because `Σψ = 0`. So
   `|K_r| ≤ Σ_c (B − #S_c) = pB − (q−1) = 3p²p^t + 1`. Only the upper bounds are needed; the lower
   bounds come for free from `Σ_c #S_c = q − 1`.
6. **Parameters.** Take `s = ⌊r/2⌋` and `t = ⌈r/2⌉` for `r ≥ 6`. Then `p^t ≤ √p·√p^r`. This is the
   eventual bound, and amplification (`KloostermanL`) upgrades it to `|K₁| ≤ 2√p`.

This differs from the hyperelliptic track (`Stepanov/`), which uses ordinary derivatives and so
needs multiplicity `≤ p`. Here the multiplicity is `p^s ≈ √q`, which is far larger than `p`, so the
Hasse-derivative versions are essential. They take about 50 lines on top of Mathlib's
`hasseDeriv_mul` and `taylor_coeff`.

## Numerical check (evidence level 4)

`scripts/stepanovAS/check_counts.py` builds `F_{p^r}` by brute force and checks:

* the identity `Y(x)x^e = Z(x)` on every `S_c`;
* `#S_c ≤ q/p + 3p·p^t`;
* `|K_r| ≤ 3p²p^t + 1`.

The cases are `p = 2` with `r ≤ 11`, `p = 3` with `r ≤ 7`, `p = 5` with `r ≤ 4`, and `p = 7` with
`r ≤ 3`, for all `b ≠ 0`. Observed values are `max |K_r|/√q ≤ 1.999` (consistent with Weil's 2) and
`max |#S_c − (q−1)/p|/√q ≤ 1.33`.

## Gaps

None for `WeilPrimeBound` and `τ = O(n^{23/4+ε})`. The constant in the Stepanov step is not sharp
(`(3p²+1)√p`), but amplification makes this irrelevant. Not formalized: the general
`|S(a,b;c)| ≤ τ(c)√(gcd)·√c`, which is not needed.

## Literature

* Stepanov (1969–72); Bombieri, *Counting points on curves over finite fields* (Sém. Bourbaki 430, 1973).
* Schmidt, *Equations over Finite Fields: An Elementary Approach*, Ch. II (equations `y^q − y = f(x)`).
* Iwaniec–Kowalski, *Analytic Number Theory*, Ch. 11.
* Weil, *On some exponential sums*, PNAS 34 (1948).
