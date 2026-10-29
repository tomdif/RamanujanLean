# RamanujanLean

[![Repository checks](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml)

Lean 4 + Mathlib proofs in Ramanujan's mathematics: modular forms, partitions,
q-series, mock theta identities, and finite certificates for infinite arithmetic laws.

[Theorem catalog](docs/RESULTS.md) · [Current status](docs/STATUS.md) ·
[Finite arithmetic](docs/FINITE_ARITHMETIC.md) · [Documentation guide](docs/README.md)

The Lean package is named `RamanujanTau`; modules use `import RamanujanTau.…`.
Partition theorems are connected to Mathlib's actual `Nat.Partition` cardinalities.
Proofs use kernel-checked finite computations, without `sorry`, added axioms, or
`native_decide`. Explicit hypotheses in conditional theorems remain visible in
those theorems' statements.

## Selected results

| Area | Formalized result | Entry point |
|---|---|---|
| Ramanujan's τ | Multiplicativity, the Hecke recurrence, and the mod-691 congruence for the computable Euler-product coefficients | [TauModular](RamanujanTau/TauModular.lean) |
| Classical q-series | Jacobi's triple product, Euler's pentagonal theorem, and Jacobi's cube identity | [Theorem catalog](docs/RESULTS.md) |
| Partition congruences | Ramanujan's congruences modulo 5, 7, and 11, and their prime-power developments | [Theorem catalog](docs/RESULTS.md) |
| Rank and crank | Rank equidistribution modulo 5; crank equidistribution modulo 5, 7, and 11 | [Theorem catalog](docs/RESULTS.md) |
| Mock theta functions | The two Hickerson identities and the χ₀ identity with its partition-rank interpretation | [Method](MOCK_THETA_METHOD.md) |
| Partition asymptotics | Hardy–Ramanujan asymptotics, Rademacher's exact formula, and log-concavity for every n ≥ 26 | [Theorem catalog](docs/RESULTS.md) |
| Primes 13, 17, 19, 23 | A single p-adic multiplier gives the partition recurrence at b = m modulo p^m | [OrdQuot.Atkin](RamanujanTau/OrdQuot/Atkin.lean) |
| Every power of 29 | One 29-adic multiplier gives the partition recurrence for every b ≥ 2m−1 modulo 29^m | [AllPowers29](RamanujanTau/FiniteArithmetic/AllPowers29.lean) |
| Finite arithmetic | Finite operator relations imply recurrences for every iterate; applications include partition residues and exact weighted tilings | [Framework and examples](docs/FINITE_ARITHMETIC.md) |

**The prime-29 starting threshold is exact.** For every m ≥ 1 and positive B,
a scalar multiplier works for all admissible partition progressions from
b = B onward modulo 29^m if and only if B ≥ 2m−1.
[Complete29](RamanujanTau/FiniteArithmetic/Complete29.lean) proves this for
actual partition counts; the full build and expanded axiom audit passed.
See the [verification record](docs/STATUS.md#verification).

Work on the proposed all-prime Theorem A now proves that, for every prime
ℓ ≥ 13, U_ℓ cannot kill a nonzero reduced level-six form of weight ℓ−3
with the two prescribed U₂/U₃ eigenvalues. This applies to reductions of
actual complex modular forms over embedded coefficient rings. Lean proves
the integral polynomial model, Hasse divisibility, minimal-weight theta-cycle
laws, and a full weight-six operator identity; no filtration or lifting
hypothesis remains in this result.
Full Theorem A still needs the eigenvalue formulas for the stated newform
Atkin–Lehner class, the Shimura comparison, and the Boylan–Webb identification.
See the [precise boundary](docs/THEOREM_A.md).

## Build and verify

With Lean's `elan` toolchain manager installed:

```sh
git clone https://github.com/tomdif/RamanujanLean.git
cd RamanujanLean
lake exe cache get
lake build
```

[lean-toolchain](lean-toolchain) selects Lean `v4.30.0-rc2`.
[lake-manifest.json](lake-manifest.json) pins Mathlib; keep it when reproducing a
build. A Mathlib cache download does not include this project's certificates.
Fresh certificate checks can take substantial time and memory; later builds
reuse the compiled proofs.

After a successful build, run the theorem audits and a recurrence demonstration:

```sh
lake env lean scripts/audit/atkin_obrien_closure.lean
lake env lean scripts/audit/finite_arithmetic.lean
lake env lean scripts/audit/theorem_a.lean
lake env lean --run scripts/finite_arithmetic/demo.lean 1000000000000
```

The audits report axiom dependencies. The finite-arithmetic audit also checks
small counting values and an enormous recurrence exponent. The expected axiom
set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

Fast repository checks are separate from Lean verification:

```sh
python3 scripts/check_repository.py
python3 scripts/boylanwebb/check_cert29_error.py
```

GitHub's **Repository checks** workflow runs these lightweight checks. It does
not substitute for `lake build` or the Lean axiom audits.

## Research and contributions

The [documentation guide](docs/README.md) distinguishes current results from
historical plans, numerical experiments, and proposed paper arguments.
Current open work includes efficient high-precision seed computation, extending
certified arithmetic representations beyond prime 29, and the remaining
multi-quintuple classification problem. Deligne's τ bound is not formalized here;
Lehmer's conjecture remains open.

See [CONTRIBUTING.md](CONTRIBUTING.md) for proof, certificate, and documentation
conventions. The project is [MIT licensed](LICENSE).
