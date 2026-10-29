# Current status

Updated 2026-10-29. [Overview](../README.md) · [Documentation guide](README.md)

## Formal developments

| Track | Current boundary | Source or guide |
|---|---|---|
| τ function | The Euler-product bridge, multiplicativity, Hecke recurrence, and mod-691 congruence are proved. Deligne's bound is not formalized; Lehmer's conjecture is open. | [τ questions](../OPEN_QUESTIONS.md) |
| Classical q-series and partitions | The triple product, pentagonal and cube identities, partition congruences, and rank/crank results have formal proofs. | [Catalog](RESULTS.md) |
| Mock theta conjectures | The f₀, f₁, and χ₀ targets are proved, including the stated rank interpretation. | [Method](../MOCK_THETA_METHOD.md) |
| Analytic partition formulas | Hardy–Ramanujan, Rademacher, and log-concavity for n ≥ 26 are formalized. | [Catalog](RESULTS.md) |
| Primes 13, 17, 19, 23 | The unconditional partition recurrence at b = m is proved. The displayed public theorems establish sufficiency, not minimality of that starting index. | [Public theorems](../RamanujanTau/OrdQuot/Atkin.lean) |
| Prime 29, every power | The unconditional recurrence for b ≥ 2m−1 and its evaluator from two actual seeds passed a full build and axiom audit. | [AllPowers29](../RamanujanTau/FiniteArithmetic/AllPowers29.lean) |
| Prime-29 exact threshold | The exact positive starting threshold B ≥ 2m−1 for actual partition counts is proved at every precision m ≥ 1. The numerical kernel certificate, full build, and expanded axiom audit passed. | [Complete29](../RamanujanTau/FiniteArithmetic/Complete29.lean) |
| Finite operator framework | Recurrence, survival, and evaluation theorems are proved; weighted tilings supply another identified counting model. | [Finite arithmetic](FINITE_ARITHMETIC.md) |
| Universal Theorem A | The algebraic reduction and actual bad-prime Hecke operators on Γ₀(N), with q-expansion and integral-reduction compatibility, are formalized. Filtration, the actual weight-six annihilator, and the correspondence remain open. | [Formalization boundary](THEOREM_A.md) |
| Multi-quintuple products | The canonical family and the stated specializations are proved. The corrected general converse remains a research problem. | [Research record](../RESEARCH_MULTI_QUINTUPLE.md) |

## Verification

The prime-29 milestone's full build passed 9,131 jobs.
The expanded finite-arithmetic audit checked 52 declarations. Its axiom
dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or additional axiom. The
[verification record](verification/prime29.json) pins the source revision,
toolchain, Mathlib revision, and checked commands. The
[raw axiom report](verification/finite_arithmetic.axioms.txt) lists the audited declarations.

After adding the Theorem A foundations and actual bad-prime operators, the full
build passed 9,141 jobs. The [dedicated audit](verification/theorem_a.axioms.txt)
checked 27 declarations with the same three standard axioms. These include the
analytic operator construction, q-expansion identification, and integral
reduction. The assembled ordinarity theorem retains its explicit modular
hypotheses.

The independent sharpness checker verifies 16 polynomial products, their 429 bounded blocks, divisor-sum
formulas, Euler coefficients, shifts, a linear combination, and three observations.
It checks the generated data with a different arithmetic algorithm; Lean's kernel
remains the proof authority.

The sharpness certificate uses blocks of at most 64 coefficients and separate
cached product modules to reduce the memory pressure of the original monolithic
check. The assembly rule and all 429 product blocks passed Lean verification,
along with the bounded divisor-sum checks.

GitHub's **Repository checks** workflow checks documentation links, source hygiene,
project imports, and that independent arithmetic. A green workflow is not evidence
that a fresh full Lean build has completed. Reproduce the mathematical verification
with the build and audit commands in the [overview](../README.md#build-and-verify).

## Open work

- Compute the two high-precision partition seeds efficiently. The proved evaluator
  is fast once those residues are supplied; it does not make seed acquisition free.
- Identify and certify finite representations for further primes and counting
  problems. Experimental Katz matrices require their own arithmetic identification
  and remainder bounds.
- Resolve the general sharpness and higher-precision rank questions in the
  [Boylan–Webb research draft](BL_SHARPNESS_PROOF.md). The prime-29 construction
  does not establish those claims for every prime.
- Supply the level-six filtration and Hecke inputs and the half-integral-weight
  correspondence needed by the [Theorem A formalization](THEOREM_A.md).
- Resolve the corrected multi-quintuple classification problem. Its existing
  finite experiments and reductions do not prove the universal converse.

The research documents retain historical calculations and proposed arguments.
Their labels such as “proved here” refer to paper arguments unless they identify
a Lean theorem and its discharged hypotheses. Claims of mathematical novelty
require literature and expert review independently of kernel verification.
