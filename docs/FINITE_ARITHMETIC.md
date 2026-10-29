# Finite arithmetic certificates

[Overview](../README.md) · [Verification status](STATUS.md) · [Documentation index](README.md)

Module paths below are relative to `RamanujanTau/`.

| Entry point | Purpose |
|---|---|
| [Orbit](../RamanujanTau/FiniteArithmetic/Orbit.lean) | Finite relations, recurrence, and survival |
| [AllPowers29](../RamanujanTau/FiniteArithmetic/AllPowers29.lean) | The unconditional partition recurrence at every precision |
| [Complete29](../RamanujanTau/FiniteArithmetic/Complete29.lean) | Exact-threshold construction; final certificate verification pending |
| [Evaluate29Powers](../RamanujanTau/FiniteArithmetic/Evaluate29Powers.lean) | Executable recurrence from two actual starting residues |
| [WeightedTilings](../RamanujanTau/FiniteArithmetic/WeightedTilings.lean) | A second counting problem with an identified finite representation |
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

**Exact starting threshold — final kernel certificate pending** (`FiniteArithmetic/Complete29.lean`): for every `m ≥ 1` and positive
starting index `B`, a scalar multiplier works for every `b ≥ B` and every admissible partition
progression if and only if **`B ≥ 2m−1`**. `partition_threshold` is the proposed unconditional entry point and states this for actual cardinalities
of `Nat.Partition`. At every precision `m ≥ 2`, `partition_count_obstruction` proves that every
proposed multiplier has a partition-count counterexample at the preceding index `b = 2m−2`.

The sharpness proof observes the divided error through `λ(F) = 3[q²]F − [q]F`. Its residue is
`12·23^n (mod 29)`, which never vanishes. `Error29.tail_killed` controls the contribution of the
entire Katz remainder; `lift_padic_mem` in `OrbitLift.lean` retains the envelope of each divided error.
Three finite observations modulo 841, submitted for kernel checking through degree 1682 in `Cert29Error.lean`, supply
the scalar law and its initial value. `CertifyError29.lean` identifies those observations with
the actual 29-adic operator, including the weight-28 Eisenstein denominator at precision 841.
The original experimental scalar orbit starting at `8` remains a separate example in the audit.

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
`python3 scripts/boylanwebb/gen_cert29_error.py > RamanujanTau/FiniteArithmetic/Cert29Error.lean`.
`python3 scripts/boylanwebb/check_cert29_error.py` provides a fast independent check of its 16 products
using packed-integer multiplication. Lean's kernel checks remain the proof authority.
