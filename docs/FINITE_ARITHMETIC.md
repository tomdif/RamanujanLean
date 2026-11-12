# Finite arithmetic certificates

[Overview](../README.md) · [Verification status](STATUS.md) · [Documentation index](README.md)

Module paths below are relative to `RamanujanTau/`.

| Entry point | Purpose |
|---|---|
| [Orbit](../RamanujanTau/FiniteArithmetic/Orbit.lean) | Finite relations, recurrence, and survival |
| [AllPowers29](../RamanujanTau/FiniteArithmetic/AllPowers29.lean) | The unconditional partition recurrence at every precision |
| [Complete29](../RamanujanTau/FiniteArithmetic/Complete29.lean) | Proved exact starting threshold at every precision |
| [Evaluate29Powers](../RamanujanTau/FiniteArithmetic/Evaluate29Powers.lean) | Executable recurrence from two actual starting residues |
| [WeightedTilings](../RamanujanTau/FiniteArithmetic/WeightedTilings.lean) | A second counting problem with an identified finite representation |
| [FormalSturm](../RamanujanTau/FiniteArithmetic/FormalSturm.lean) | Finite coefficient determination over rings, including prime powers |
| [EnvelopePrecision](../RamanujanTau/FiniteArithmetic/EnvelopePrecision.lean) | Proved reconstruction of actual partition iterates modulo prime squares |
| [PrecisionSquare](../RamanujanTau/FiniteArithmetic/PrecisionSquare.lean) | Exact Hasse series and its inverse squared modulo p², for every prime p≥5 |
| [DeterminantRank](../RamanujanTau/FiniteArithmetic/DeterminantRank.lean) | Generator bounds from nonzero determinants; conditional prime-607 target |
| [RankLifting](../RamanujanTau/FiniteArithmetic/RankLifting.lean) | A divided-relation criterion predicting when a hidden direction becomes visible |
| [Rank607Witness](../RamanujanTau/FiniteArithmetic/Rank607Witness.lean) | Checked determinant of the saved matrix; `actual_rank_of_entries` reduces the rank to entry identification |
| [PackedSeries](../RamanujanTau/FiniteArithmetic/PackedSeries.lean) | Power-series prefixes packed into one integer, with certified lane-parallel reduction for kernel evaluation |
| [Rank607Final](../RamanujanTau/FiniteArithmetic/Rank607Final.lean) | Entry identification at 607; unconditional `rEll_607` |
| [Rank607Structure](../RamanujanTau/FiniteArithmetic/Rank607Structure.lean) | The module at 607 modulo 607²: `lamEquiv : (ℤ/607²)²⁴ × ℤ/607² ⧸ (607) ≃ Λ^odd(3,2)` |
| [Rank607One](../RamanujanTau/FiniteArithmetic/Rank607One.lean) | The module at 607 modulo 607: `lamEquiv1 : (ℤ/607)²⁴ ≃ Λ^odd(1,1)` and `rEll_607_one` |
| [Rank607Threshold](../RamanujanTau/FiniteArithmetic/Rank607Threshold.lean) | `bEll_607_two`: b₆₀₇(2) = 3, since L(1) ∉ Λ^odd(3,2) |
| [ExactThreshold](../RamanujanTau/FiniteArithmetic/ExactThreshold.lean) | `bEll_29`, `bEll_31`: b_ℓ(m) = 2m−1 for every m at ℓ = 29, 31, via `BLBound.not_mem_of_errors` ([Threshold](../RamanujanTau/BLBound/Threshold.lean)) |
| [PartitionPrefix](../RamanujanTau/FiniteArithmetic/PartitionPrefix.lean) | Certified packed prefix of the partition generating function modulo any Q ≤ 2²¹ |
| [SmallThreshold](../RamanujanTau/FiniteArithmetic/SmallThreshold.lean) | b_ℓ(m) ≤ 2⌊m/2⌋+1 and b_ℓ(2) = b_ℓ(3) = 3 at ℓ = 13, 17, 19, 23 |
| [SmallThresholdFive](../RamanujanTau/FiniteArithmetic/SmallThresholdFive.lean) | b_ℓ(4) = b_ℓ(5) = 5 at ℓ = 13, 17, 19, 23 (up to 6.7M partition numbers mod ℓ⁴) |
| [AtkinExact](../RamanujanTau/FiniteArithmetic/AtkinExact.lean) | b_ℓ(m) = 2⌊m/2⌋+1 for all m at ℓ = 13, 17, 19, 23; Atkin–O'Brien index exact (finite error model mod ℓ², `ExactAtkin`) |
| [RankRPacked](../RamanujanTau/FiniteArithmetic/RankRPacked.lean) | b_ℓ(m) = 2m−1 for all m at every prime 61 ≤ ℓ ≤ 139 (`RankRAt61` … `RankRAt139`): order-r recurrence (`OrbitLiftR`, `BLBound/ThresholdR`, `RankRMod`, `RankRLift`, `RankRError`, `RankRMain`), window determinant det₀·(det C)ⁿ |
| [RankSPacked](../RamanujanTau/FiniteArithmetic/RankSPacked.lean) | b_ℓ(m) = 2m−1 for all m at ℓ = 53, 59 (`RankSAt53`, `RankSAt59`): the rank-two model with s + 2 forms and s observations (`RankSMod`, `RankSLift`, `RankSError`, `RankSMain`), error vector moved by an invertible s × s matrix Θ |
| [Rank2Packed](../RamanujanTau/FiniteArithmetic/Rank2Packed.lean) | b_ℓ(m) = 2m−1 for all m at ℓ = 37, 41, 43, 47 (`Rank2At37`…`Rank2At47`), from one packed mod-ℓ² kernel evaluation per prime (`PackedPrime`) and the rank-two error model (`Rank2Mod`, `Rank2Lift`, `Rank2Error`, `Rank2Main`) |
| [AtkinExactPartition](../RamanujanTau/FiniteArithmetic/AtkinExactPartition.lean) | the same exactness for partition numbers: ℓ^(b+1) ∤ p((ℓ^(b+2)n+1)/24) − c·p((ℓ^b n+1)/24) for some n, every b ≥ 1 and c ∈ ℤ_ℓ |
| [SeedModels](../RamanujanTau/FiniteArithmetic/SeedModels.lean) | All-iterate survival in five checked finite models; arithmetic identification remains |
| [Audit](../scripts/audit/finite_arithmetic.lean) | Axiom dependencies and executable examples |


`FiniteArithmetic/Orbit.lean` supplies a reusable algebraic interface for turning finite operator
certificates into statements about every iterate. An `OrbitModel` includes a finite transition,
an initial vector, a linear map into the actual arithmetic space, and proofs that the initial state
and operator action agree. A checked relation among orbit vectors then gives a recurrence for every
iterate and every linear observation, including coefficients of a generating function.

The recurrence theorem works over commutative rings, including `ZMod (p^m)`. Over a field, an orbit
in dimension `s` survives forever exactly when its `s`-th iterate is nonzero; the full operator need
not be invertible.

There are two applications with proofs identifying their finite representations:

* **Partition residues modulo 29** (`FiniteArithmetic/Partition29.lean`): for every `b ≥ 1` and
  `24 ∣ 29^b n + 1`,
  `p((29^(b+2)n+1)/24) = 3 p((29^b n+1)/24) (mod 29)`.
  In particular, for every `t ≥ 0`,
  **`p((19·29^(1+2t)+1)/24) = 8·3^t (mod 29)`**.
  These are cardinalities of `Nat.Partition`, including a proof of the initial residue `p(23) = 8`
  modulo 29. `ModularCertificate.lean` turns finite coefficient checks into identities of full
  series using the proved Sturm bound and a Hasse lift. `Cert29.lean` checks the coefficient lists
  through degree 1073 in Lean's kernel. The odd line is spanned by `Δ²E₄`; its even image is
  `3ΔE₄⁴ + 6Δ²E₄`. The generator discovers the image coefficients by solving a two-dimensional
  system in this supplied basis, then checks the entire required Sturm prefix. Python generates
  the certificate but is not trusted by the proof.
  **Every power of 29** (`FiniteArithmetic/AllPowers29.lean`): there is a single
  `κ ∈ ℤ_[29]`, with `κ = 3 (mod 29)`, such that, for every `m ≥ 1`, `b ≥ 2m−1`, and
  `24 ∣ 29^b n + 1`,
  **`p((29^(b+2)n+1)/24) = κ p((29^b n+1)/24) (mod 29^m)`**.
  `partition_padic` proves this for actual partition cardinalities, with no remaining
  operator-bound hypotheses. `partition_residues_iterate` gives the resulting scalar-power
  formula for every future iterate in `ZMod (29^m)`.
  The proof uses the established Katz bounds, the vanishing of the constant and q¹ terms
  in the odd image, and a Sturm-certified q² line in weight 28. `OrbitLift.lean` lifts a
  rank-one leading digit through arbitrarily many precisions. `Cert29Image.lean` also checks
  the additional identity `D(Δ²E₄) = 21Δ²E₄ (mod 29)`; `Image29.lean` proves the rank-one
  image of D on all of M₂₈ modulo 29.
* **Exact weighted tilings** (`FiniteArithmetic/WeightedTilings.lean`): the sum over all tilings of
  a strip with monomers of weight `a` and dominoes of weight `b` has transition matrix
  `[[a,b],[1,0]]`. The proof constructs an `OrbitModel` from the combinatorial sum over the tilings.
  It works over any commutative ring, so it includes exact integer counts, rational weights,
  and reduction modulo prime powers. It makes no claim about arbitrary probabilistic models.

`Evaluate.lean` provides repeated squaring with stored intermediate matrices and proves its result
equals the operator power. `Partition29.residue_correct` and `WeightedTilings.evaluate_correct`
connect executable answers to the actual counting problems. A query can specify the exponent
without constructing the enormous partition index. For arbitrary progressions the initial partition
residue remains a separate input cost; the displayed family includes that initial calculation.
At higher powers, `Evaluate29Powers.lean` specifies the multiplier as the ratio of the two initial
partition residues in the family starting at `b = 2m−1`, `n = 19`, and proves that the denominator
is invertible modulo `29^m`. Its `evaluate_correct` theorem connects repeated squaring from those
two inputs to the actual partition count for every future iterate. Computing the two initial
residues efficiently at high precision remains a separate problem.

**Exact starting threshold — kernel verified** (`FiniteArithmetic/Complete29.lean`): for every `m ≥ 1` and positive
starting index `B`, a scalar multiplier works for every `b ≥ B` and every admissible partition
progression if and only if **`B ≥ 2m−1`**. `partition_threshold` is the unconditional entry point and states this for actual cardinalities
of `Nat.Partition`. At every precision `m ≥ 2`, `partition_count_obstruction` proves that every
proposed multiplier has a partition-count counterexample at the preceding index `b = 2m−2`.

The sharpness proof observes the divided error through `λ(F) = 3[q²]F − [q]F`. Its residue is
`12·23^n (mod 29)`, which never vanishes. `Error29.tail_killed` controls the contribution of the
entire Katz remainder; `lift_padic_mem` in `OrbitLift.lean` retains the envelope of each divided error.
Three finite observations modulo 841, checked in the kernel through degree 1682 in `Cert29Error.lean`, supply
the scalar law and its initial value. `CertifyError29.lean` identifies those observations with
the actual 29-adic operator, including the weight-28 Eisenstein denominator at precision 841.
The original experimental scalar orbit starting at `8` remains a separate example in the audit.

**Prime 31 — kernel verified** (`FiniteArithmetic/Complete31.lean`): the same theorems hold at ℓ = 31, the other prime with
one stable term and a two-dimensional cusp space. For every `m ≥ 1` and positive `B`, a scalar works from `b = B` onward modulo `31^m`
if and only if **`B ≥ 2m−1`**. The basis is `f = Δ²E₆`, `g = 29ΔE₄³E₆ + 14Δ²E₆`, with `U(Δ⁴⁰) = 10f`, `Uf = g`, `U(Δ⁴⁰g) = 30f`
and `U(Δ⁴⁰f) = 29f` modulo 31. The observation is `λ(F) = 29[q²]F − 2[q]F`, and the divided error has residue `24·2^n (mod 31)`.
Regenerate with `gen_cert31.py`, `gen_cert31_image.py` and `gen_cert31_error.py` in `scripts/boylanwebb`; `check_cert31_error.py`
independently checks its 17 products and 521 blocks. The files are per-prime ports of the prime-29 modules, not a general theorem:
`Cert31.lean` alone took about 49 minutes to check.

After building, run the kernel checks and the executable demonstration:

```sh
lake env lean scripts/audit/finite_arithmetic.lean
lake env lean --run scripts/finite_arithmetic/demo.lean 1000000000000
```

The audit prints axiom dependencies and checks boundary cases, known small weighted counts, and a
large partition-family exponent. Regenerate the finite coefficient certificate with
`python3 scripts/boylanwebb/gen_cert29.py > RamanujanTau/FiniteArithmetic/Cert29.lean`.
Checking the certificate from scratch is the expensive step; subsequent queries reuse its compiled proof.
The sharpness certificate is regenerated by
`python3 scripts/boylanwebb/gen_cert29_error.py --output-dir RamanujanTau/FiniteArithmetic`.
This writes the public certificate, `Cert29ErrorData.lean`, and the 16 modules in
`Cert29ErrorProducts/`. The product modules check 429 blocks with at most 64 coefficients
in each left factor. `ChunkedCertificate.lean` proves that their assembly gives the full
product congruences. Divisor-sum observations are also checked in bounded intervals.
The modules form a serial import chain so independent large checks do not compete for
memory, and completed products are reused by later builds. Each block retains only
the coefficient precision needed after its final shift.
`python3 scripts/boylanwebb/check_cert29_error.py` independently checks all 16 products
and 429 blocks using packed-integer multiplication. Lean's kernel remains the proof authority.

## Multi-quintuple classification certificates

The [full admissible triple theorem](../RamanujanTau/MultiQuintupleFullConverse.lean)
uses finite certificates for its short-generation argument and its exceptional
modulus-13 case. It also proves the analytic bridge to actual infinite-product
coefficients. These inputs are part of an unconditional theorem under the
stated admissibility and residue hypotheses.

| Certificate | Coverage | Lean entry point |
|---|---|---|
| Small isotropic box | All 468 nonsingular symmetric ternary Gram forms over F₃ | [SmallIsotropicBox](../RamanujanTau/MultiQuintupleSmallIsotropicBox.lean) |
| Short dual generators | 14,369 certificates; normalized-line coverage across 201 primes from 7 through 1249, excluding 13 from the generation conclusion | [FiniteGenerators](../RamanujanTau/MultiQuintupleFiniteGenerators.lean) and its eight `Block` imports |
| Modulus 13 | Two canonical triples, six root certificates, and 20 nonzero coefficients | [ConverseThirteen](../RamanujanTau/MultiQuintupleConverseThirteen.lean) |

Determinant gcd calculations certify generation over ℤ. The Lean framework
also proves normalization and completeness of the finite coverage. For p≥1250,
[LargePrimeGeneration](../RamanujanTau/MultiQuintupleLargePrimeGeneration.lean)
proves generation geometrically, so no finite prime sweep stands in for that
infinite range. The cutoff is sufficient, not claimed minimal.

Build and audit from the repository root:

```sh
lake build RamanujanTau.MultiQuintupleFullConverse
lake env lean scripts/audit/multi_quintuple.lean
lake build
```

Regenerate the Lean tables from their documented inputs:

```sh
python3 scripts/generate_small_isotropic_box.py
python3 scripts/generate_lean_short_generators.py
git diff --exit-code -- RamanujanTau/MultiQuintupleSmallIsotropicBox.lean \
  RamanujanTau/MultiQuintupleFiniteGenerators.lean \
  RamanujanTau/MultiQuintupleFiniteGenerators
```

The first command deterministically constructs the mod-three box. The second
reads [short_watson_generators.json](verification/short_watson_generators.json)
and writes the normalized row tables. Both generators are untrusted producers:
`decide +kernel` checks their finite arithmetic inside Lean. Keep the eight
certificate blocks stable while editing downstream proofs so completed kernel
checks can be reused. A fresh check can take substantial time and memory.

The independent standard-library Python checker can be run separately:

```sh
python3 scripts/check_short_watson_generators.py \
  docs/verification/short_watson_generators.json \
  --output /tmp/short-watson-generators-check.json
```

Its `lean_checked: false` field identifies the independent checker's method.
The [full Lean record](verification/full_converse_lean.json) and
[axiom report](verification/full_converse_lean.axioms.txt) establish the formal
status. The published proof snapshot passed 9,336 build jobs and 251 audited
multi-quintuple declarations. Regeneration was checked byte for byte.


## Four-direction follow-up certificates

The [current status](STATUS.md#four-direction-follow-up-2026-11-01) distinguishes
actual-product theorems from finite-model results and open universal claims.
Build and audit the new results with:

```sh
lake build RamanujanTau.MultiQuintupleFourFortyOneConverse RamanujanTau.MultiQuintupleWitness103 RamanujanTau.FiniteArithmetic.Rank607Witness RamanujanTau.FiniteArithmetic.SeedModels
lake env lean scripts/audit/four_directions.lean
lake build RamanujanTau.MultiQuintupleFourFamily RamanujanTau.FiniteArithmetic.PrecisionSquare
lake env lean scripts/audit/four_family.lean
lake env lean scripts/audit/four_plane.lean
lake env lean scripts/audit/four_reflection.lean
lake env lean scripts/audit/four_binary.lean
lake env lean scripts/audit/four_witnesses.lean
python3 scripts/check_four_reflection.py
python3 scripts/check_four_plane.py
python3 scripts/check_four_binary.py --output /tmp/four-binary-check.json
```

Regenerate the numerical matrix certificates (Python-FLINT is needed for the
seed inverses) and compare the resulting Lean sources:

```sh
python3 scripts/generate_rank607_witness.py
python3 scripts/generate_seed_model_certificates.py
```

The 607 checker proves `E*M=U`, upper triangularity, and a nonzero product of
diagonal entries. No determinant expansion or external arithmetic oracle is
trusted. The hypothesis in `actual_rank_of_entries` identifies M with the
actual infinite partition iterates. `Rank607Final` discharges it with a separate kernel
evaluation; regenerate its untrusted coordinate table with
`python3 scripts/generate_rank607_coords.py`. The check needs about 18 GB of memory. Each saved seed model similarly has a kernel-checked
left inverse and nonzero seed. Its survival for all powers is proved, but
identifying the model with the actual second-order partition operator remains
an arithmetic obligation.

Discover and independently verify the four-factor certificates:

```sh
python3 scripts/four_quintuple_certificates.py --prime 41 --indices 1,4,5,9 --output /tmp/four41.json
python3 scripts/check_four_quintuple_certificate.py docs/verification/four_quintuple_41.json --negative-control
python3 scripts/check_four_quintuple_certificate.py docs/verification/four_quintuple_53.json --negative-control
python3 scripts/check_four_quintuple_certificate.py docs/verification/four_quintuple_97.json --negative-control
```

The discoverer uses Python-FLINT; the independent identity checker uses only
the standard library. The Lean modules separately prove the complete actual
four-factor classifications at 41, 53 and 97. At 97 the first sixteen terms
are an exact finite test, and the cutoff is optimal (residue 54 first becomes
nonzero at N=15). The [review verification](verification/quintuple_review.json)
and [reproduction script](../scripts/verify_quintuple_review.py) cover the
new coefficients and the centered-root classifier for admissible triples.

The complete prime reflection-family converse is now proved in
[FourPrimeConverse](../RamanujanTau/MultiQuintupleFourPrimeConverse.lean).
The seven additional small-prime witness modules are reproducible with
`python3 scripts/generate_four_prime_small.py --check`; their numerical
claims are checked by Lean's kernel against actual-product coefficient formulas.

The all-parameter theorem in
[FourFamily](../RamanujanTau/MultiQuintupleFourFamily.lean) separately proves
four zero progressions for p=5184t²+720t+41, without a primality premise.
Regenerate its polynomial affine maps with SymPy, then compare the actual
Pochhammer products against Watson sums using only Python integers:

```sh
python3 scripts/generate_four_quintuple_family.py
python3 scripts/check_four_quintuple_family.py --output /tmp/four-family-check.json
```

The generator reproduces
[FourFamilyData](../RamanujanTau/MultiQuintupleFourFamilyData.lean) and the
[symbolic data](verification/four_quintuple_family.json) byte for byte. Lean
checks every polynomial identity for all t; the generator is outside the
trusted proof. The [independent finite check](verification/four_quintuple_family_check.json)
compares all coefficients through seven terms of each progression for t=0,…,4.

The second quadratic family in
[FourBinaryFamily](../RamanujanTau/MultiQuintupleFourBinaryFamily.lean) proves
two zero progressions at p=450t²+180t+43 for every natural t. Its
[audit](verification/four_binary.axioms.txt) covers 20 declarations, including
the proof that every even t gives a modulus outside integer sums of two squares.
The [independent check](verification/four_binary_check.json) compares 259,467
coefficients across 17 pairs using direct Pochhammer multiplication and Watson
sums. The all-N result comes from Lean's affine involution proof.

Reproduce the four-factor witness-bound counterexample and the broader finite
search using only Python's standard library:

```sh
python3 scripts/check_four_quarter_counterexample.py --output /tmp/four-quarter-counterexample.json
python3 scripts/check_four_witnesses.py --output /tmp/four-witnesses-check.json
python3 scripts/scan_four_quintuple_frontier.py --output /tmp/four-frontier.json
```

The [counterexample](verification/four_quarter_counterexample.json) at
`(2521;1,35,36,71)` compares two Watson term enumerators and two factorizations
of the convolution. It establishes first witnesses N=631 and 632, beyond
⌊2521/4⌋=630, by exact integer computation. Residue 2273 now also has an
actual-product Lean proof of first witness N=632; residue 67 remains
computational. A second Lean proof at `(17;2,3,5,8;R=5)` gives first witness
N=7 and implies the necessary universal linear-bound constant c≥7/17.
These results concern four factors; the original triple-product conjecture
remains open. The [frontier search](verification/four_quintuple_frontier.json)
tests all 3,174 distinct canonical isotropic tuples at primes through 71 and
retains 289 products with zero candidates through N=2p. Those finite candidates
require further proof.

Regenerate the large witness certificate with
`python3 scripts/generate_four2521_certificate.py`. Lean checks all 82 slices
against their defining bounded enumeration with `decide +kernel`, then checks
the sorted signed lists. The proof bounds every contributing integer and uses
the residue equation to recover the fourth branch uniquely, so no unchecked
completeness assumption is present. The
[independent checker](../scripts/check_four_witnesses.py) also verifies that
regeneration matches the saved Lean file byte for byte.

For the 607 reconstruction, `map_E_square_general` and
`map_Einv_square_squared_general` prove, for every prime p≥5,
`E ≡ 1−2pS` and `Einv² ≡ 1+4pS (mod p²)`, where
`S=Σ σ_(p−2)(n)q^n`. This uses von Staudt–Clausen and the square-zero
identity p²=0 in the coefficient ring. It removes a Bernoulli-number
calculation from the denominator identification; the actual matrix entries
still require certification.

Reproduce the bounded searches with Python-FLINT:

```sh
python3 scripts/frontier/pattern/seed_survival_scan.py --output /tmp/seed-survival.json
python3 scripts/scan_quarter_witness_bound.py --output /tmp/quarter-bound.json
```

The seed scan checks Katz depths 3 and 4 at five primes. Agreement at both
depths is evidence, not an identification proof. The quarter-bound scan tests
all canonical triples through 151 and 800 sampled projective rescalings up to
3000 with a fixed random seed. Neither finite range proves an all-prime theorem.
The prime-103 first-witness benchmark has a separate actual-product Lean proof.
