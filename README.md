# RamanujanLean

[![Repository checks](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml)
[![Lean checks](https://github.com/tomdif/RamanujanLean/actions/workflows/lean-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanLean/actions/workflows/lean-checks.yml)

Lean 4 proofs of Ramanujan’s mathematics: modular forms, partition congruences,
q-series, mock theta identities, and finite certificates for infinite arithmetic laws.

**[Theorem catalog](docs/RESULTS.md) · [Current status](docs/STATUS.md) ·
[Documentation guide](docs/README.md) · [Contributing](CONTRIBUTING.md)**

The package and import namespace are `RamanujanTau`. Partition theorems are
connected to Mathlib’s actual `Nat.Partition` cardinalities. Proofs use Lean’s
kernel, with no `sorry`, added axioms, or `native_decide`. Conditional results
retain their missing mathematical inputs as explicit hypotheses.

## Selected results

| Area | Proved results | Guide |
|---|---|---|
| Ramanujan’s τ | Euler-product/modular-form bridge, multiplicativity, Hecke recurrence, mod-691 congruence, and Weil’s bound `τ(n) = O(n^{23/4+ε})` | [τ results](OPEN_QUESTIONS.md) |
| Classical identities | Jacobi’s triple product, Euler’s pentagonal theorem, Rogers–Ramanujan identities, and all forty Rogers–Ramanujan function identities | [Forty identities](docs/FORTY_IDENTITIES.md), [catalog](docs/RESULTS.md) |
| Mock and septic theta functions | All ten fifth-order mock theta identities; the septic identities and the Lost Notebook’s page-206 evaluation | [Mock theta](docs/MOCK_THETA5_ALL.md), [septic](docs/SEPTIC_SON.md) |
| Partitions | Congruences modulo 5, 7, 11 and prime powers; rank/crank results; Hardy–Ramanujan, Rademacher, and log-concavity for `n ≥ 26` | [Catalog](docs/RESULTS.md) |
| Theorem A and stabilization | Unconditional Theorem A for every prime `ℓ ≥ 13`; `b_ℓ(m) ≤ 2m−1`; exact thresholds at every prime from 13 through 139 | [Theorem A](docs/THEOREM_A.md), [finite certificates](docs/FINITE_ARITHMETIC.md) |
| Analytic number theory | Rankin–Selberg asymptotics and functional equations, critical zeros and mean squares, a τ prime number theorem, and unconditional subconvexity | [Analytic guides](docs/README.md#analytic-and-congruence-write-ups-2026-11-0304) |
| Jensen polynomials | Eventual hyperbolicity in every degree for partitions and Riemann Ξ; all-index degree-2 Turán inequalities for Ξ; exact partition thresholds in degrees 6 and 7 | [Ξ](docs/GORZ_XI.md), [thresholds](docs/JENSEN_THRESHOLDS.md) |
| Product classification | Complete admissible sparse triple classification, fixed four-factor classifications, and infinite vanishing families | [Classification](RESEARCH_MULTI_QUINTUPLE.md#current-theorem), [review manuscript](output/pdf/sparse-triples.pdf) |
| Occupation spaces and entropy | Colored partition counts, finite-shell adjoints, completed occupation Hilbert space, self-adjoint energy operator, and `4π√n` leading entropy for the specified 24-species charge shells | [Fock-space proof](docs/BOSONIC_FOCK.md) |
| Nested radicals | The classical values 3 and 4, a complete affine classification, and exponential error bounds | [Catalog](docs/RESULTS.md#ramanujans-nested-radical) |

Exact hypotheses, normalizations, and theorem names are in the linked guides.
An axiom audit checks a theorem’s dependencies; it does not discharge explicit
hypotheses or establish that the statement matches its intended interpretation.

## Build and verify

Install Lean’s `elan` toolchain manager, then:

```sh
git clone https://github.com/tomdif/RamanujanLean.git
cd RamanujanLean
lake exe cache get
lake build
```

[lean-toolchain](lean-toolchain) selects Lean `v4.30.0-rc2`;
[lake-manifest.json](lake-manifest.json) pins the dependencies. Keep both files
when reproducing a build. The default root includes the occupation/entropy
modules and the completed Fock-space construction.

Run the public theorem checks, or the full root build and headline audits:

```sh
python3 scripts/verify_lean.py
python3 scripts/verify_lean.py --full
python3 scripts/check_repository.py
python3 scripts/boylanwebb/check_cert29_error.py
```

The default verifier builds and audits all forty identities and the completed
Fock space. `--full` also builds the root library and audits the celebrated
analytic and arithmetic targets. It rejects unexpected axioms and saves build
and audit logs under `/tmp/ramanujan-lean-verification` (override with
`--output-dir`). Additional topic-specific audits live in [scripts/audit](scripts/audit).

Fresh full builds require substantial memory: individual packed `RankRAt*`
certificates have used about 21 GB, and `GORZXiEff.CVData*` about 9 GB. Build
large certificates sequentially on smaller machines. GitHub runs the lightweight
repository checks and the focused Lean checks; a green focused check does not
certify the entire root. See [verification status](docs/STATUS.md#verification)
for dated full-build records.

## What remains

- **Deligne’s bound:** the best unconditional bound here is Weil’s exponent
  `23/4`. The companion [RamanujanWeil](https://github.com/tomdif/RamanujanWeil)
  develops routes to Deligne’s `11/2`, still conditional on named geometric inputs.
- **Uniform Boylan–Webb sharpness:** the all-prime lower bound needs the seed
  nonvanishing argument and its arithmetic identification. [Current boundary](docs/BW_SHARPNESS_ALL_PRIMES.md).
- **Further classifications:** arbitrary four-factor products, uniform witness
  bounds, and higher-precision structure at prime 607. [Research status](docs/STATUS.md#four-direction-follow-up-2026-11-01).
- **Analytic extensions:** higher-order Turán inequalities for Ξ and the exact
  Andrews–Dragonette series. [Ξ degree 3](docs/GORZ_XI_D3.md), [exact series](docs/ANDREWS_DRAGONETTE_EXACT.md).
- **Physical interpretation:** colored logarithmic corrections, a physical
  state identification, and the quarter-BPS mock Jacobi construction remain
  separate from the proved occupation model. [Scope](docs/BOSONIC_FOCK.md#scope).

Lehmer’s conjecture remains open; the proved finite nonvanishing range is
`1 ≤ n < 214,928,639,999`. Research notes retain their dated history; current
status summaries identify results that supersede earlier gaps.

## Related repositories

- [RamanujanWeil](https://github.com/tomdif/RamanujanWeil): Weil RH and the
  remaining geometric steps toward Deligne’s τ bound, on a newer Lean toolchain.
- [RamanujanPartitions](https://github.com/tomdif/RamanujanPartitions): the
  earlier, small computational companion. Its all-index congruences remain
  hypotheses; this repository contains the general proofs for actual counts.

[MIT license](LICENSE).
