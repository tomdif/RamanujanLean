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
| Prime-29 exact threshold | Implementation complete; final numerical kernel certificate and dependent full build/audit are pending. Conditional sharpness proofs and independent arithmetic checks passed. | [Complete29](../RamanujanTau/FiniteArithmetic/Complete29.lean) |
| Finite operator framework | Recurrence, survival, and evaluation theorems are proved; weighted tilings supply another identified counting model. | [Finite arithmetic](FINITE_ARITHMETIC.md) |
| Multi-quintuple products | The canonical family and the stated specializations are proved. The corrected general converse remains a research problem. | [Research record](../RESEARCH_MULTI_QUINTUPLE.md) |

## Verification

The last completed full build before the sharpness addition passed 9,099 jobs.
Its finite-arithmetic audit checked 34 declarations and found only standard
Lean axioms. A new full build and expanded audit are required before the
prime-29 exact-threshold result is marked complete here.

The independent sharpness checker verifies 16 polynomial products, their 429 bounded blocks, divisor-sum
formulas, Euler coefficients, shifts, a linear combination, and three observations.
It checks the generated data with a different arithmetic algorithm; Lean's kernel
remains the proof authority.

The sharpness certificate now uses blocks of at most 64 coefficients and separate
cached product modules to reduce the memory pressure of the original monolithic
check. The assembly rule is proved in Lean; the replacement certificate still
requires its complete build and audit before the result is marked verified here.

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
- Resolve the corrected multi-quintuple classification problem. Its existing
  finite experiments and reductions do not prove the universal converse.

The research documents retain historical calculations and proposed arguments.
Their labels such as “proved here” refer to paper arguments unless they identify
a Lean theorem and its discharged hypotheses. Claims of mathematical novelty
require literature and expert review independently of kernel verification.
