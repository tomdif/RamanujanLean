# Documentation guide

[Project overview](../README.md) · [Current status](STATUS.md) · [Detailed theorem catalog](RESULTS.md)

Use the status page for current verification boundaries. The documents below
include historical plans; their dated open questions can be superseded by the
current status at the top of the file. The admissible sparse triple converse
is complete; the [current statement](../RESEARCH_MULTI_QUINTUPLE.md#current-theorem)
and [verification record](verification/full_converse_lean.json) supersede its
earlier open-problem and partial-formalization notes.

## Current guides

| Document | Purpose |
|---|---|
| [Finite arithmetic certificates](FINITE_ARITHMETIC.md) | Partition recurrences and sharpness, executable counting, and the multi-quintuple generator certificates |
| [Shimura-lift proof map](AAD_BLUEPRINT.md) | How the formal proof of modularity of the lifts is organized |
| [Theorem A formalization](THEOREM_A.md) | Unconditional Theorem A in integer and half-integral weight, and what remains |
| [Mock theta method](../MOCK_THETA_METHOD.md) | The formal proof architecture for the Mock Theta Conjectures |
| [τ closure status](../OPEN_QUESTIONS.md) | Proved τ results and the Deligne/Lehmer boundary |
| [Atkin–O'Brien proof record](ATKIN_OBRIEN_PROOF.md) | Public theorems for 13, 17, 19, 23, followed by the historical development |
| [Multi-quintuple classification](RESULTS.md#multi-quintuple-products-complete-admissible-triple-classification) | Exact theorem, scope, proof modules, and verification |
| [Multi-quintuple development record](../RESEARCH_MULTI_QUINTUPLE.md) | Current statement followed by historical experiments, counterexamples, and the paper proof |
| [Nested radicals](RESULTS.md#ramanujans-nested-radical) | Values 3 and 4, the affine family and full converse for linear limits, and exponential error bounds proved in Lean |
| [Contribution guide](../CONTRIBUTING.md) | Proof policy, verification commands, and documentation conventions |

## Analytic and congruence write-ups (2026-11-03/04)

Each file records its own evidence levels; later results are noted in a status line at the top where an
earlier section is superseded. The summary table is [Results of 2026-11-03](STATUS.md#results-of-2026-11-03).

| Document | Topic |
|---|---|
| [TAU_SUBHECKE_BOUND](TAU_SUBHECKE_BOUND.md), [WEIL_KLOOSTERMAN](WEIL_KLOOSTERMAN.md), [KLOOSTERMAN_L](KLOOSTERMAN_L.md), [STEPANOV](STEPANOV.md), [STEPANOV_ARTIN_SCHREIER](STEPANOV_ARTIN_SCHREIER.md) | τ(n) = O(n^{47/8+ε}), then O(n^{35/6+ε}) (Salié), then O(n^{23/4+ε}) (Weil) |
| [LEHMER_SMALL_N](LEHMER_SMALL_N.md) | τ(n) ≠ 0 for n < 21,492,863,999 |
| [RANKIN_SELBERG](RANKIN_SELBERG.md), [EISENSTEIN_REAL](EISENSTEIN_REAL.md) | Mean square of τ: order of magnitude, then the asymptotic with Zagier's constant |
| [JENSEN_THRESHOLDS](JENSEN_THRESHOLDS.md), [GORZ_PARTITIONS](GORZ_PARTITIONS.md) | Jensen polynomials of p(n): N(6), N(7), and GORZ in every degree |
| [GORZ_XI](GORZ_XI.md), [GORZ_XI_EFFECTIVE](GORZ_XI_EFFECTIVE.md), [GORZ_XI_D3](GORZ_XI_D3.md) | Jensen polynomials of Riemann Ξ: GORZ Theorem 1, Turán (d = 2) for every n, and the d = 3 reduction |
| [ANDREWS_DRAGONETTE](ANDREWS_DRAGONETTE.md), [ANDREWS_1966](ANDREWS_1966.md), [ANDREWS_1966_ASYMPTOTIC](ANDREWS_1966_ASYMPTOTIC.md), [MOCK_THETA_CUSPS](MOCK_THETA_CUSPS.md), [ANDREWS_DRAGONETTE_EXACT](ANDREWS_DRAGONETTE_EXACT.md) | Coefficients of f(q): Dragonette, the sign for every n, Andrews 1966 with O(√n log n), and the limits of the method for the exact formula |
| [ATKIN_SPORADIC_CONGRUENCES](ATKIN_SPORADIC_CONGRUENCES.md), [HALF_INTEGRAL_HECKE](HALF_INTEGRAL_HECKE.md), [GAUSS_SIGN](GAUSS_SIGN.md), [ONO_WEAVER_EXTENSIONS](ONO_WEAVER_EXTENSIONS.md), [ATKIN_TWISTED_ALL_Q](ATKIN_TWISTED_ALL_Q.md) | Atkin's 13 ∣ p(17303n+237), Ono–Weaver families, T(Q²) on η-multiplier forms, Gauss's sign |
| [BW_SHARPNESS_ALL_PRIMES](BW_SHARPNESS_ALL_PRIMES.md) | Uniform Boylan–Webb sharpness: what is proved, and the open seed condition G5 |

## Research records and completed plans

| Document | How to read it |
|---|---|
| [Boylan–Webb sharpness draft](BL_SHARPNESS_PROOF.md) | Proposed general-prime arguments with named gaps; distinct from the prime-29 Lean construction |
| [Prime-dependent threshold experiments](BL_PATTERN.md) | Bounded numerical results; includes the correction to universal rank attainment at 607 |
| [Literature check](LIT_CHECK.md) | Dated definitions and literature notes; not a formal proof or a current exhaustive literature search |
| [Frontier probes](FRONTIER_FINDINGS.md) | Historical experiments, including Jensen-polynomial thresholds |
| [Cylindric positivity and black hole research](CYLINDRIC_RESEARCH.md) | Exact rank-four scans, slice lemmas, partition entropy, the reciprocal-discriminant bridge, bosonic spectra and finite-shell adjoints, and reusable unifiedtheory estimates |
| [13-power plan](ATKIN13_PLAN.md) | An earlier modular-equation route; the target recurrence was reached via overconvergence |
| [17/19/23 reduction](ATKIN_OBRIEN_17_19_23.md) | Historical conditional reductions preceding the unconditional public theorems |
| [11-power plan](ATKIN_11_PLAN.md) | Completed Atkin development and its intermediate calculations |
| [Rademacher plan](RADEMACHER_PLAN.md) | Completed plan for the exact partition formula |
| [Watson R1 proof](watson1937_R1_proof.md) | Mathematical guide to the formalized χ₀ relation |
| [Mock theta gap map](../MTC_GAP_MAP.md) | Completed targets followed by the historical working record |
| [Bailey roadmap](../MOCKTHETA_BAILEY_ROADMAP.md) | Superseded campaign plan; Watson's method closed its target |
| [Bailey reach map](../AQ_BAILEY_REACH.md) | Diagnostic record of the attempted Bailey route |
| [Bilateral-theta design](../ZZQ_FRAMEWORK.md) | Historical design; the pentagonal theorem used a different route |

## Multi-quintuple verification records

| Record | Status |
|---|---|
| [Full Lean proof](verification/full_converse_lean.json) and [axiom report](verification/full_converse_lean.axioms.txt) | Current proof authority: complete admissible converse; published build and audit results |
| [Initial Lean progress](verification/short_converse_lean.json) | Historical partial formalization, superseded by the full proof |
| [Paper argument](verification/full_converse_paper.json) | Historical computer-assisted argument and independent finite checks |
| [Phase pairing](verification/phase_pairing.json) | Earlier algebraic result; its missing analytic and geometric connections are now proved |
| [Short-generator data](verification/short_watson_generators.json) and [independent check](verification/short_watson_generators_check.json) | Reproducible finite data used by the kernel-checked generator modules |
| [Infinite four-factor family](verification/four_family.json) and [axiom report](verification/four_family.axioms.txt) | All-parameter coefficient theorem and the uniform Hasse denominator identity modulo prime squares |
| [Two-parameter plane theorem](verification/four_plane.json) and [axiom report](verification/four_plane.axioms.txt) | Infinite vanishing criterion at p=m²+n² and complete classification of the fixed product at 53 |
| [Uniform reflection theorem](verification/four_reflection.json) and [axiom report](verification/four_reflection.axioms.txt) | Four congruence families, actual infinite vanishing at 97, and the exact compatibility criterion for sixteen reflection maps |
| [Second quadratic family](verification/four_binary.json) and [axiom report](verification/four_binary.axioms.txt) | Actual infinite vanishing at p=2m²+n²; an unconditional family with unboundedly many moduli outside sums of two squares |
| [Rank at 607](verification/rank607_final.json) and [axiom report](verification/rank607_final.axioms.txt) | Unconditional `rEll 607 m = 25` for m≥2, from a kernel evaluation of packed series; includes the open question about the rank definition in Boylan–Webb |
| [Four-factor witness proofs](verification/four_witnesses.json) and [axiom report](verification/four_witnesses.axioms.txt) | Actual-product first witnesses at 17 and 2521; any universal four-factor linear bound requires c≥7/17 |
| [Earlier four-factor quarter-bound computation](verification/four_quarter_counterexample.json) | Historical exact replay at 2521; residue 2273 now has a Lean proof, while residue 67 remains computational; the original triple-product conjecture is unaffected |
| [Four-factor frontier](verification/four_quintuple_frontier.json) | Finite search through prime 71; 289 candidate products, without an infinite-vanishing claim |

Historical verification files are snapshots, not live status pages. In particular,
`lean_checked: false` in an independent Python report describes that checker's
method; it does not negate the later Lean proof of the same finite obligations.

The [four-direction follow-up](STATUS.md#four-direction-follow-up-2026-11-01)
records the completed four-factor case at 41, checked finite seed models, the
607 numerical minor, and the prime-103 first-witness benchmark. It separates
those results from the remaining universal conjectures. The subsequent
[infinite family](../RESEARCH_MULTI_QUINTUPLE.md#an-infinite-four-factor-family)
extends the example at 41 to unbounded moduli, including composite moduli.
The later [plane theorem](../RESEARCH_MULTI_QUINTUPLE.md#two-parameter-plane-theorem)
handles two parameters and gives a complete fixed-product classification at 53.
The [second quadratic family](../RESEARCH_MULTI_QUINTUPLE.md#a-second-quadratic-family-beyond-sums-of-two-squares)
proves additional infinite zero progressions starting at 43.
Reproduction commands
are in the [certificate guide](FINITE_ARITHMETIC.md#four-direction-follow-up-certificates).
