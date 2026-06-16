# RamanujanTau

A Lean 4 + Mathlib formalization of **Ramanujan's τ function**, the coefficient
sequence of the modular discriminant
`Δ(q) = q · ∏_{n≥1} (1 - q^n)^{24} = Σ_{n≥1} τ(n) qⁿ`.

Filling a Mathlib gap: Mathlib has the discriminant cusp form
`ModularForm.discriminant z = (eta z)^24 : ℍ → ℂ`, but it does not extract
`τ : ℕ → ℤ` as a computable function. This repo does.

| | |
|---|---|
| Modules | 18 (12 top-level + 6 congruence sub-modules) |
| Build | `lake build` → **3257 jobs, 0 errors** |
| `sorry` count | **0** |
| New `axiom` declarations | **0** |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` + Mathlib |

## Definition

We work with a small computable `List ℤ` representation (Mathlib's `Polynomial`
is noncomputable), giving:

```lean
def tau (n : ℕ) : ℤ :=
  let p   := eulerProductTrunc n n   -- ∏_{k=1}^{n} (1 - X^k), truncated to deg n
  let p24 := truncPowList n p 24      -- (·)^24, also truncated
  coeffList (shiftList 1 p24) n       -- [X · (·)^24].coeff n
```

This is `native_decide`-reducible: every value `τ(n)` reduces by computation.

The Euler product truncation through `n` factors agrees with the infinite product
on coefficients of degree `≤ n` (each omitted factor `(1 - q^j)` for `j > n`
contributes only at degree `≥ j > n`), so this gives exact values.

## Verified content

### `Basic.lean`
- Computable polynomial-list arithmetic: `coeffList`, `addList`, `mulList`,
  `truncList`, `shiftList`, `oneMinusXk`, `truncPowList`, `eulerProductTrunc`
- The `tau` function and the `τ` notation
- `tau_zero : τ 0 = 0`
- `tau_one : τ 1 = 1`

### `SmallValues.lean`
Exact values of `τ(n)` for `n = 2, 3, …, 12`, each proved by `native_decide`:

| n | τ(n) |
|---|---|
| 2 | -24 |
| 3 | 252 |
| 4 | -1472 |
| 5 | 4830 |
| 6 | -6048 |
| 7 | -16744 |
| 8 | 84480 |
| 9 | -113643 |
| 10 | -115920 |
| 11 | 534612 |
| 12 | -370944 |

Plus the multiplicativity instance check `τ(12) = τ(3) · τ(4)` (since
`gcd(3,4) = 1`).

### `Multiplicativity.lean`
Hypothesis class `TauMultiplicative` packaging Mordell's theorem
(`τ(mn) = τ(m) · τ(n)` for coprime `m, n`). Under the class, `tauArith`
extends `τ` to a Mathlib `ArithmeticFunction ℤ`, with
`tauArith_isMultiplicative` proven.

The full Hecke-theoretic proof is deferred (requires Hecke operators on
weight-12 cusp forms + the fact that the space of weight-12 cusp forms is
1-dimensional).

### `HeckeRecurrence.lean`
Hypothesis class `TauHeckeRecurrence`:
```
τ(p^{r+1}) = τ(p) · τ(p^r) − p^{11} · τ(p^{r-1})
```
for every prime `p` and `r ≥ 1`. Numerical sanity checks for `(p, r) = (2,1)`,
`(2,2)`, `(3,1)` are proved by `norm_num`.

### `HeckeTheory.lean`
A single master hypothesis class `TauHeckeMaster` (the action of `T_p` on the
q-expansion of the weight-12 eigenform) from which **both** `TauHeckeRecurrence`
and `TauMultiplicative` are *derived as instances* — full Lean proofs, by induction
on the prime factorization. One deep input; everything else follows mechanically.

### `EulerFactor.lean`
The Hecke theory of `τ` at a prime, all **proven** under `TauHeckeRecurrence`:
- `tau_prime_sq : τ(p²) = τ(p)² − p¹¹` and `tau_prime_cube : τ(p³) = τ(p)³ − 2p¹¹τ(p)`,
  as general theorems (∀ primes), superseding the earlier numerical checks
- `euler_factor_coeff` — the three-term recurrence reindexed for all `r ≥ 0`
- `euler_factor` — the **local Euler factor** of `L(Δ, s)`, as a power-series identity:
  `(1 − τ(p) X + p¹¹ X²) · Σ_r τ(p^r) X^r = 1` in `ℤ⟦X⟧`
- `tauArith_eq_prod_factorization` (under `TauMultiplicative`) —
  `τ(n) = ∏_{p^k ‖ n} τ(p^k)`: `τ` is determined by its prime-power values.

### `HeckePowers.lean`
Higher prime-power closed forms `τ(p⁴) … τ(p⁷)` as polynomials in `τ(p)` and `p`,
e.g. `τ(p⁷) = τp⁷ − 6p¹¹τp⁵ + 10p²²τp³ − 4p³³τp`. These were **proposed by an LLM
generator and verified by the Lean kernel** (each via `rw [recurrence, lower forms]; ring`),
chained on the verified predecessors — only kernel-certified forms are kept.

### `Gegenbauer.lean`
The **general** closed form for `τ(p^r)`, via the Gegenbauer / Chebyshev-U polynomial
family `G_r(s,q)` defined by `G_0 = 1`, `G_1 = s`, `G_{r+2} = s·G_{r+1} − q·G_r`:
- `tau_ppow_eq_gegen : τ(p^r) = G_r(τ p, p¹¹)` for **all** `r` — one theorem subsuming
  `τ(p²) … τ(p⁷)`
- `gegen_eq_sum` — the explicit Gegenbauer/Chebyshev binomial formula
  `G_r(s,q) = Σ_j (−1)^j C(r−j, j) q^j s^{r−2j}` (proved via Pascal's rule, three boundary cases)
- `tau_ppow_eq_sum : τ(p^r) = Σ_j (−1)^j C(r−j, j) p^{11j} τ(p)^{r−2j}`

### `Deligne.lean`
Deligne's bound (a consequence of the Weil conjectures, 1974): class `DeligneBound`
(`τ(p)² ≤ 4 p¹¹`, i.e. `|τ(p)| ≤ 2 p^{11/2}`), with the bound **verified by
`native_decide` for every prime `p ≤ 13`**.

### `Lehmer.lean`
Lehmer's conjecture (open, 1947): class `LehmerConjecture` (`τ(n) ≠ 0 ∀ n ≥ 1`),
plus kernel-verified finite evidence `lehmer_below_101 : τ(n) ≠ 0` for all
`1 ≤ n ≤ 100` (`native_decide`). The universal statement is open; the range is certified.

### `Congruences.lean`
- `sigma11 (n : ℕ) : ℤ := Σ_{d | n} d^{11}`, with computed values for `n = 1..4`
- Numerical checks of the mod-691 congruence `τ(n) ≡ σ₁₁(n) (mod 691)` for
  `n = 1, 2, 3, 4` (verified by `decide`)
- Hypothesis class `TauMod691` for the general statement

## Cryptographic / mathematical assumptions surface

The discipline mirrors that of [PlonkLean](https://github.com/tomdif/PlonkLean):
deep theorems are exposed as named typeclasses, never asserted as `axiom`s.

| Class | Statement | Discharge route |
|---|---|---|
| `TauHeckeMaster` | `T_p`-action master identity on the q-expansion of Δ | weight-12 cusp forms are 1-dim ⟹ Δ is a Hecke eigenform |
| `TauMultiplicative` | `τ(mn) = τ(m)τ(n)` for coprime `m,n` | **derived** from `TauHeckeMaster` |
| `TauHeckeRecurrence` | `τ(p^{r+1}) = τ(p)τ(p^r) − p^{11}τ(p^{r-1})` | **derived** from `TauHeckeMaster` |
| `TauMod691` | `τ(n) ≡ σ₁₁(n) (mod 691)` | `691 \| numerator(B_{12})` + `E_{12} = E_4³ − 720 Δ` |
| `DeligneBound` | `τ(p)² ≤ 4 p^{11}` for all primes `p` | Deligne 1974 (étale cohomology / Weil I) |
| `LehmerConjecture` | `τ(n) ≠ 0` for all `n ≥ 1` | **open** — no known proof |

Everything in `EulerFactor`, `HeckePowers`, and `Gegenbauer` is fully proven *given*
`TauHeckeRecurrence` (in turn derived from the single class `TauHeckeMaster`); `Deligne`
and `Lehmer` certify their statements on a finite range by computation.

## Bridge to Mathlib

Mathlib has `ModularForm.discriminant : ℍ → ℂ` already, plus a `q`-expansion
framework for cusp forms. The downstream theorem connecting our `tau` to that
q-expansion is:

```lean
-- statement (proof TBD)
theorem tau_coeff_discriminant (z : ℍ) (n : ℕ) :
    qExpansion ModularForm.discriminant n = tau n
```

Once this bridge is proven, every property here transfers to Mathlib's
modular-form-level discriminant, and conversely Mathlib's modular-form proofs
transfer to numerical properties of `tau`.

## What's next (multi-session)

- **Discharge `TauHeckeMaster`** — formalize Hecke operators on `CuspForm Γ(1) 12`,
  prove Δ is a Hecke eigenform, and instantiate the master identity. This single
  step then turns `TauMultiplicative`, `TauHeckeRecurrence`, and every result in
  `EulerFactor` / `HeckePowers` / `Gegenbauer` into unconditional theorems.
- **Mod-691 congruence** — Bernoulli number `B_{12}` numerator `= -691 · …`,
  plus Eisenstein-series identity `E_{12} = E_4³ − 720·Δ`.
- **Bridge to Mathlib's `discriminant`** via the `q`-expansion framework.
- **Deligne's bound** — discharge `DeligneBound` (or extend the verified range of primes).
- **Lehmer's conjecture** — the `LehmerConjecture` class and the verified range
  `n ≤ 100` are in place; the universal statement remains open.

## Build

```sh
lake build
```

Cache hit on Mathlib master gets it down to seconds.

## License

MIT.

## References

- Ramanujan, S. (1916). "On certain arithmetical functions."
  *Trans. Cambridge Philos. Soc.* **22**.
- Mordell, L. J. (1917). Multiplicativity of τ.
- Deligne, P. (1974). Bound `|τ(p)| ≤ 2 p^{11/2}` (Weil conjectures, weight 1).
- Lehmer, D. H. (1947). "The vanishing of Ramanujan's function τ(n)." *Duke Math. J.* **14**.
- Apostol, T. M. *Modular Functions and Dirichlet Series in Number Theory* —
  Hecke operators, the Euler product of `L(Δ, s)`, and the prime-power recurrence.
- Diamond & Shurman, *A First Course in Modular Forms*, §1.2.
- OEIS [A000594](https://oeis.org/A000594) — Ramanujan's τ.
