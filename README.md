# RamanujanLean

[![Repository checks](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml)

Lean 4 + Mathlib proofs in Ramanujan's mathematics: modular forms, partitions,
q-series, mock theta identities, and finite certificates for infinite arithmetic laws.

[Theorem catalog](docs/RESULTS.md) · [Current status](docs/STATUS.md) ·
[Multi-quintuple classification](RESEARCH_MULTI_QUINTUPLE.md#current-theorem) ·
[Finite certificates](docs/FINITE_ARITHMETIC.md) · [Documentation guide](docs/README.md)

The Lean package is named `RamanujanTau`; modules use `import RamanujanTau.…`.
Partition theorems are connected to Mathlib's actual `Nat.Partition` cardinalities.
Proofs use kernel-checked finite computations, without `sorry`, added axioms, or
`native_decide`. Explicit hypotheses in conditional theorems remain visible in
those theorems' statements.

## Selected results

| Area | Formalized result | Entry point |
|---|---|---|
| Ramanujan's τ | Multiplicativity, the Hecke recurrence, and the mod-691 congruence for the computable Euler-product coefficients | [TauModular](RamanujanTau/TauModular.lean) |
| Kloosterman's bound for τ | τ(n) = O(n^{47/8+ε}), the first bound below Hecke's n⁶, with Kloosterman's sum bound, Poincaré-series unfolding, and the cusp-form property all proved | [Unconditional](RamanujanTau/TauBound/Unconditional.lean), [write-up](docs/TAU_SUBHECKE_BOUND.md) |
| Jensen polynomials, every degree | Griffin–Ono–Rolen–Zagier for p(n): for every d the degree-d Jensen polynomial is real-rooted for all large n, and the renormalized polynomials converge to Hermite polynomials | [GORZ](RamanujanTau/GORZ/Main.lean), [write-up](docs/GORZ_PARTITIONS.md) |
| Jensen thresholds d = 6, 7 | The degree-6 Jensen polynomial of p is real-rooted for every n ≥ 610 and not at 609; degree 7: every n ≥ 908, not at 907 | [Final](RamanujanTau/JensenThreshold/Final.lean), [write-up](docs/JENSEN_THRESHOLDS.md) |
| Andrews' 1966 asymptotic | α(n) equals Andrews' printed sum over k ≤ √n of A_{2k}·I_{1/2} terms up to O(√n log n) (Andrews' own error term), via uniform bounds on f ± b near every root of unity | [SharpHb](RamanujanTau/MockCusp/SharpHb.lean), [write-ups](docs/ANDREWS_1966_ASYMPTOTIC.md), [cusps](docs/MOCK_THETA_CUSPS.md) |
| Dragonette's asymptotic | The coefficients of Ramanujan's f(q), i.e. N(0,2,n)−N(1,2,n), satisfy α(n) ~ (−1)^{n+1} e^{π√(n/6−1/144)}/(2√(n−1/24)), and (−1)^{n+1}α(n) > 0 for every n ≥ 1, so even- and odd-rank partitions alternate in which is more numerous | [Literal](RamanujanTau/Dragonette/Literal.lean), [sign](RamanujanTau/Andrews/Main.lean), [write-ups](docs/ANDREWS_DRAGONETTE.md), [sign proof](docs/ANDREWS_1966.md) |
| Ono–Weaver congruences | 13 ∣ p(157525693n+111247), 17 ∣ p(48037937n+1122838), and 81 Ono- and Atkin-type families for ℓ ∈ {13,17,19,23,29,31} and every hit prime Q < 500 (e.g. 19 ∣ p(41743n+669), 29 ∣ p(142477n+31778)), via Hecke equivariance of the Shimura lift; Atkin's 13 ∣ p(17303n+237) and 15 further twisted mod-13 families for Q < 500, via an explicit Hecke operator T(Q²) on η-multiplier forms and Gauss's sign theorem | [WeaverUnconditional](RamanujanTau/AtkinSporadic/WeaverUnconditional.lean), [all families](RamanujanTau/OnoWeaverMore/All.lean), [write-ups](docs/ATKIN_SPORADIC_CONGRUENCES.md), [table](docs/ONO_WEAVER_EXTENSIONS.md), [Atkin](RamanujanTau/AtkinSporadic/Atkin13Unconditional.lean), [T(Q²)](docs/HALF_INTEGRAL_HECKE.md) |
| Classical q-series | Jacobi's triple product, Euler's pentagonal theorem, and Jacobi's cube identity | [Theorem catalog](docs/RESULTS.md) |
| Nested radicals | The classical radicals equal 3 and 4; affine radicands with linear limits have a full classification, with exponential error bounds | [Classification](RamanujanTau/NestedRadicalClassification.lean) and [accuracy](RamanujanTau/NestedRadicalAffine.lean) |
| Partition congruences | Ramanujan's congruences modulo 5, 7, and 11, and their prime-power developments | [Theorem catalog](docs/RESULTS.md) |
| Rank and crank | Rank equidistribution modulo 5; crank equidistribution modulo 5, 7, and 11 | [Theorem catalog](docs/RESULTS.md) |
| Mock theta functions | The two Hickerson identities and the χ₀ identity with its partition-rank interpretation | [Method](MOCK_THETA_METHOD.md) |
| Partition asymptotics | Hardy–Ramanujan asymptotics, ordinary and colored partition entropy (including the 24-color reciprocal-discriminant coefficients), Rademacher's exact formula, and log-concavity for every n ≥ 26 | [Theorem catalog](docs/RESULTS.md) |
| Bosonic occupation model | Exact equivalence with colored partitions; finite Hilbert spaces with an occupation basis; 24-species charge-shell entropy grows as 4π√n with a specified vacuum offset | [Standalone module](RamanujanTau/BosonicOccupation.lean) |
| Algebraic oscillators | Creation and annihilation satisfy the canonical commutation relations; Hamiltonian eigenspaces have exactly the colored partition dimensions | [Operators](RamanujanTau/BosonicOscillator.lean) and [spectrum](RamanujanTau/BosonicSpectrum.lean) |
| Finite-shell adjoints | Factorial normalization gives square-root occupation coefficients; creation and annihilation are proved Hilbert adjoints between finite energy shells | [Normalization](RamanujanTau/BosonicNormalization.lean) and [adjoints](RamanujanTau/BosonicAdjoint.lean) |
| Primes 13, 17, 19, 23 | A single p-adic multiplier gives the partition recurrence at b = m modulo p^m | [OrdQuot.Atkin](RamanujanTau/OrdQuot/Atkin.lean) |
| Every power of 29 | One 29-adic multiplier gives the partition recurrence for every b ≥ 2m−1 modulo 29^m | [AllPowers29](RamanujanTau/FiniteArithmetic/AllPowers29.lean) |
| Sparse triple products | Persistent coefficient vanishing is equivalent to an exact projective root certificate for every admissible triple and canonical residue | [Full converse](RamanujanTau/MultiQuintupleFullConverse.lean) |
| Fixed four-factor classifications | At 41 the zero residues are 21,25,26,30; at 53 they are 29,31,36,38. Every other residue has a witness by N=5 and N=8 respectively | [41](RamanujanTau/MultiQuintupleFourFortyOneConverse.lean) and [53](RamanujanTau/MultiQuintupleFourFiftyThreeConverse.lean) |
| Infinite four-factor family | Four explicit progressions vanish for every parameter t≥0, at modulus 5184t²+720t+41; primality is not required | [All-parameter theorem](RamanujanTau/MultiQuintupleFourFamily.lean) |
| Four-factor reflection families | Infinite vanishing at p=m²+n² when 9 divides one of m,n,m−n,m+n, with explicit size and coprimality conditions; the sixteen maps have an exact branch-compatibility classification | [Uniform theorem](RamanujanTau/MultiQuintupleFourReflection.lean) and [map criterion](RamanujanTau/MultiQuintupleFourReflectionCriterion.lean) |
| A second four-factor family | Two permanent zero progressions at p=450t²+180t+43 for every t≥0; every even t gives a modulus outside all integer sums of two squares | [All-parameter theorem](RamanujanTau/MultiQuintupleFourBinaryFamily.lean) |
| Four-factor witness obstructions | Exact first witnesses N=7 at prime 17 and N=632 at prime 2521; any universal linear cutoff N≤cp for admissible four-tuples requires c≥7/17 | [Lower bound](RamanujanTau/MultiQuintupleFourWitnessBound.lean) and [2521](RamanujanTau/MultiQuintupleFourWitness2521.lean) |
| Canonical quintuple products | For every odd p ≥ 5, the full canonical product vanishes in every nonsquare residue class | [Canonical family](RamanujanTau/MultiQuintupleCanonical.lean) |
| Finite arithmetic | Finite operator relations imply recurrences for every iterate; applications include partition residues and exact weighted tilings | [Framework and examples](docs/FINITE_ARITHMETIC.md) |

**The admissible sparse triple classification is complete.** For prime p≠3,
0<i<j<k, 2k<p, p dividing i²+j²+k², and 0≤R<p, every coefficient of
`Q(qⁱ,qᵖ) Q(qʲ,qᵖ) Q(qᵏ,qᵖ)` at degrees pN+R vanishes if and only if
there is a projective root certificate with the required residue condition.
The theorem concerns the actual infinite products and assumes no additional
analytic, geometric, or generation statement. The published proof passed a
9,336-job full build and a 251-declaration axiom audit. See the
[exact statement and proof map](RESEARCH_MULTI_QUINTUPLE.md#current-theorem)
and [verification record](docs/verification/full_converse_lean.json).

**Four follow-up directions now have checked results.** The four-factor example
at 41 has a complete Lean classification and now extends to an infinite family
with four proved zero progressions at every parameter. The saved prime-607 minor is now identified with
actual partition data, so the stable module needs exactly 25 generators at every
precision m≥2 (`Rank607Final.rEll_607`); at m=2 the module is
(ℤ/607²)²⁴ ⊕ ℤ/607, with 24 free summands (`Rank607Structure.lamEquiv`), and at m=1
it is free of rank 24 (`Rank607One.rEll_607_one`). The threshold there is exact:
b₆₀₇(2) = 3 (`Rank607Threshold.bEll_607_two`). Five finite seed models have proved
survival for every iterate; their partition-operator identifications remain
open; the Hasse denominator modulo p² is now identified uniformly for every
prime p≥5. The quarter-prime witness conjecture passed 5,339 expanded tests; a
23-step delay at prime 103 is proved in Lean. The universal four-factor
classification, all-prime sharpness, and universal witness bound remain open.
See the [four-direction status](docs/STATUS.md#four-direction-follow-up-2026-11-01).

**The four-factor search now reaches a different quadratic family.** Lean proves
infinite vanishing at `p=2m²+n²` under explicit hypotheses, including an
unconditional family starting at 43. Infinitely many of these moduli cannot
occur in the earlier `m²+n²` family. Separately, Lean now proves a first
nonzero coefficient at N=632 for prime 2521, beyond ⌊2521/4⌋=630. A stronger
example at prime 17 has its first witness at N=7; any universal four-factor
linear bound must therefore allow c≥7/17, about 0.412. Sufficiency of that
constant is not claimed. The original triple-product conjecture remains open. See the
[theorem and counterexample](RESEARCH_MULTI_QUINTUPLE.md#a-second-quadratic-family-beyond-sums-of-two-squares).

**The prime-29 starting threshold is exact.** For every m ≥ 1 and positive B,
a scalar multiplier works for all admissible partition progressions from
b = B onward modulo 29^m if and only if B ≥ 2m−1.
[Complete29](RamanujanTau/FiniteArithmetic/Complete29.lean) proves this for
actual partition counts; the full build and expanded axiom audit passed.
[Complete31](RamanujanTau/FiniteArithmetic/Complete31.lean) proves the same threshold at ℓ = 31.
[ExactThreshold](RamanujanTau/FiniteArithmetic/ExactThreshold.lean) translates both into
Boylan–Webb's own invariant: b₂₉(m) = b₃₁(m) = 2m−1 for every m ≥ 1
(`Exact29.bEll_29`, `Exact31.bEll_31`), where Boylan–Webb computed b₂₉ for m ≤ 3.
The same holds at the four rank-two primes 37, 41, 43, 47 (`Rank2At37.bEll_37`, …), by a
second-order error recurrence and one packed mod-ℓ² kernel evaluation per prime
([Rank2Packed](RamanujanTau/FiniteArithmetic/Rank2Packed.lean)); Boylan–Webb computed these only for m ≤ 2.
It also holds at 53 and 59 (`RankSAt53.bEll_53`, `RankSAt59.bEll_59`), where the error is a
vector moved by a 2×2 matrix ([RankSPacked](RamanujanTau/FiniteArithmetic/RankSPacked.lean)), and at every
prime 61 ≤ ℓ ≤ 139 (`RankRAt61.bEll_61`, …, `RankRAt139.bEll_139`) by an order-r version
([RankRPacked](RamanujanTau/FiniteArithmetic/RankRPacked.lean)). So b_ℓ(m) is known for every m at
every prime 13 ≤ ℓ ≤ 139.
At ℓ = 13, 17, 19, 23 the threshold is smaller:
[SmallThreshold](RamanujanTau/FiniteArithmetic/SmallThreshold.lean) proves
b_ℓ(m) ≤ 2⌊m/2⌋+1 for every m, and b_ℓ(2) = b_ℓ(3) = 3;
[SmallThresholdFive](RamanujanTau/FiniteArithmetic/SmallThresholdFive.lean) adds b_ℓ(4) = b_ℓ(5) = 5, and
[AtkinExact](RamanujanTau/FiniteArithmetic/AtkinExact.lean) proves b_ℓ(m) = 2⌊m/2⌋+1 for every m:
the Atkin–O'Brien index b = m is exact at every precision (`ExactAtkin13.exact`, …), also stated for
partition numbers in [AtkinExactPartition](RamanujanTau/FiniteArithmetic/AtkinExactPartition.lean).
See the [verification record](docs/STATUS.md#verification).

Work on the proposed all-prime Theorem A now proves that, for every prime
ℓ ≥ 13, U_ℓ cannot kill a nonzero reduced level-six form of weight ℓ−3
with the two prescribed U₂/U₃ eigenvalues. This applies to reductions of
actual complex modular forms over embedded coefficient rings. Lean proves
the integral polynomial model, Hasse divisibility, minimal-weight theta-cycle
laws, and a full weight-six operator identity; no filtration or lifting
hypothesis remains in this result.
The eigenvalues are now derived from the Atkin–Lehner signs, using Mathlib's
actual trace. So every normalized T_ℓ-eigenform in the class has a unit ℓ-th
coefficient above ℓ, unconditionally. Injectivity of U_{ℓ²} on the
half-integral-weight space, and of Boylan–Webb's X̄ on V, is also proved
unconditionally, with a formal proof of modularity of the explicit Shimura lifts
(Ahlgren–Andersen–Dicks) by a theta kernel. It follows that b_ℓ(m) ≤ 2m−1 for every
prime ℓ ≥ 13 and that d_ℓ = 0, in the partition case of the Belmont–Lee–Musat–Trebat-Leder
conjecture. These proofs are machine-checked and have not been reviewed by a human expert.
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
reuse the compiled proofs. The multi-quintuple proof includes eight stable
small-prime certificate blocks; [regeneration commands](docs/FINITE_ARITHMETIC.md#multi-quintuple-classification-certificates)
are documented separately.

After a successful build, run the theorem audits and a recurrence demonstration:

```sh
lake env lean scripts/audit/atkin_obrien_closure.lean
lake env lean scripts/audit/finite_arithmetic.lean
lake env lean scripts/audit/theorem_a.lean
lake env lean scripts/audit/multi_quintuple.lean
lake env lean scripts/audit/four_directions.lean
lake env lean scripts/audit/four_family.lean
lake env lean scripts/audit/four_plane.lean
lake env lean scripts/audit/four_reflection.lean
lake env lean scripts/audit/four_binary.lean
lake env lean scripts/audit/four_witnesses.lean
lake env lean scripts/audit/nested_radical.lean
lake env lean scripts/audit/nested_radical_affine.lean
lake env lean scripts/audit/celebrated_targets.lean
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
certified arithmetic representations beyond prime 29, and extensions beyond
the proved admissible sparse triple multi-quintuple classification, such as
four-factor products and quantitative first-witness bounds. The
[four-factor results](RESEARCH_MULTI_QUINTUPLE.md#a-second-quadratic-family-beyond-sums-of-two-squares)
now include families at both m²+n² and 2m²+n². Complete fixed-product coefficient
classifications are proved at 41 and 53; infinite zero progressions are also
proved at 43 and 97. Deligne's τ bound
is not formalized here; Lehmer's conjecture remains open.

See [CONTRIBUTING.md](CONTRIBUTING.md) for proof, certificate, and documentation
conventions. The project is [MIT licensed](LICENSE).
