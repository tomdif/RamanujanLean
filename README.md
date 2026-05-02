# RamanujanTau

A Lean 4 + Mathlib formalization of **Ramanujan's τ function**, the coefficient
sequence of the modular discriminant
`Δ(q) = q · ∏_{n≥1} (1 - q^n)^{24} = Σ_{n≥1} τ(n) qⁿ`.

Filling a Mathlib gap: Mathlib has the discriminant cusp form
`ModularForm.discriminant z = (eta z)^24 : ℍ → ℂ`, but it does not extract
`τ : ℕ → ℤ` as a computable function. This repo does.

| | |
|---|---|
| Files | 5 |
| Build | `lake build` → **1171 jobs, 0 errors** |
| `sorry` count | **0** |
| New `axiom` declarations | **0** |
| Lean toolchain | Lean 4 + Mathlib master |

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
| `TauMultiplicative` | `τ(mn) = τ(m)τ(n)` for coprime `m,n` | Hecke operators on Δ |
| `TauHeckeRecurrence` | `τ(p^{r+1}) = τ(p)τ(p^r) − p^{11}τ(p^{r-1})` | Hecke eigenform property |
| `TauMod691` | `τ(n) ≡ σ₁₁(n) (mod 691)` | `691 \| numerator(B_{12})` + `E_{12} = E_4³ − 720 Δ` |

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

- **Multiplicativity proof** — formalize Hecke operators on `CuspForm Γ(1) 12`,
  prove Δ is a Hecke eigenform, conclude `τ(mn) = τ(m)τ(n)` for coprime `m,n`.
- **Hecke recurrence proof** — same infrastructure; the eigenvalue at `T_p`
  gives the recurrence directly.
- **Mod-691 congruence** — Bernoulli number `B_{12}` numerator `= -691 · …`,
  plus Eisenstein-series identity `E_{12} = E_4³ − 720·Δ`.
- **Bridge to Mathlib's `discriminant`** via the `q`-expansion framework.
- **Lehmer's conjecture** (open: `τ(n) ≠ 0 ∀ n ≥ 1`) — beyond formalization;
  state as `LehmerConjecture` class.

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
- Diamond & Shurman, *A First Course in Modular Forms*, §1.2.
- OEIS [A000594](https://oeis.org/A000594) — Ramanujan's τ.
