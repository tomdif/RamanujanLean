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
| [Contribution guide](../CONTRIBUTING.md) | Proof policy, verification commands, and documentation conventions |

## Research records and completed plans

| Document | How to read it |
|---|---|
| [Boylan–Webb sharpness draft](BL_SHARPNESS_PROOF.md) | Proposed general-prime arguments with named gaps; distinct from the prime-29 Lean construction |
| [Prime-dependent threshold experiments](BL_PATTERN.md) | Bounded numerical results; includes the correction to universal rank attainment at 607 |
| [Literature check](LIT_CHECK.md) | Dated definitions and literature notes; not a formal proof or a current exhaustive literature search |
| [Frontier probes](FRONTIER_FINDINGS.md) | Historical experiments, including Jensen-polynomial thresholds |
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

Historical verification files are snapshots, not live status pages. In particular,
`lean_checked: false` in an independent Python report describes that checker's
method; it does not negate the later Lean proof of the same finite obligations.
