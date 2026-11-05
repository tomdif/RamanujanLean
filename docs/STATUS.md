# Current status

Updated 2026-11-04. [Overview](../README.md) · [Documentation guide](README.md)

## Formal developments

| Track | Current boundary | Source or guide |
|---|---|---|
| τ function | The Euler-product bridge, multiplicativity, Hecke recurrence, and mod-691 congruence are proved. Weil's bound τ(n) = O(n^{23/4+ε}) is proved unconditionally (`StepanovAS.tau_isBigO_23_4_unconditional`), superseding the earlier Kloosterman 47/8 (`TauBound.tau_isBigO_47_8_unconditional`) and Salié 35/6 (`Stepanov.tau_isBigO_35_6_unconditional`) exponents. Deligne's bound (11/2) is not formalized; Lehmer's conjecture is open (τ(n) ≠ 0 is proved for n < 214,928,639,999 (Lehmer 1947), `LehmerSmall.lehmer_below_214928639999`). | [τ questions](../OPEN_QUESTIONS.md) |
| Classical q-series and partitions | The triple product, pentagonal and cube identities, partition congruences, and rank/crank results have formal proofs. | [Catalog](RESULTS.md) |
| Nested radicals | The classical radicals equal 3 and 4. A three-parameter affine family converges to x+d; the sharper classical error is at most 3 log(N+3)/2^N, with a certified error below 10⁻¹⁰ at depth 40. | [Proof and scope](RESULTS.md#ramanujans-nested-radical) |
| Mock theta conjectures | The f₀, f₁, and χ₀ targets are proved, including the stated rank interpretation. | [Method](../MOCK_THETA_METHOD.md) |
| Analytic partition formulas | Hardy–Ramanujan, Rademacher, and log-concavity for n ≥ 26 are formalized. | [Catalog](RESULTS.md) |
| Partition entropy | `log p(n)=π√(2n/3)−log n−log(4√3)+o(1)` for actual partition counts; the leading exponent equals the minimum of the Cardy saddle at `C=1/12`, `E=n≥1`. A physical microstate interpretation and mock Jacobi coefficient asymptotics remain outside this result. | [Entropy](../RamanujanTau/HardyRamanujan/Entropy.lean), [research record](CYLINDRIC_RESEARCH.md#what-unifiedtheory-contributes-to-black-hole-work) |
| Colored partition entropy | For every fixed `k>0`, the actual finite count satisfies `log p_k(n)/√n → π√(2/3)√k`. The 24-color series is identified with `q/Δ`; its shifted coefficients `d(n)=p_24(n+1)` satisfy `log d(n)/√n → 4π` and the Cardy ratio at `C=2` tends to 1. Colored logarithmic corrections and physical state identification remain outside this result. | [Counting model](../RamanujanTau/ColoredPartitions.lean), [entropy](../RamanujanTau/ColoredPartitionEntropy.lean) |
| Bosonic occupation model | Occupation arrays at energy `N` are explicitly equivalent to colored partitions. Finite shell Hilbert spaces have dimension `p_k(N)` and an occupation-number orthonormal basis. With 24 species and a specified vacuum offset of −1, charge-shell log-dimension divided by `√n` tends to `4π`. Full oscillator operators and identification with the physical string theory remain outside this construction. | [Occupation model](../RamanujanTau/BosonicOccupation.lean) |
| Algebraic oscillator spectrum | Creation and annihilation satisfy the canonical commutation relations and Hamiltonian energy shifts. Actual energy eigenspaces are linearly equivalent to the preceding shells, with dimension `p_k(N)`. The specified 24-species `H−I` charge eigenspaces have dimension `p_24(n+1)` and entropy constant `4π`. Hilbert adjoints, completion, and physical string/gravity identification remain outside the result. | [Operators](../RamanujanTau/BosonicOscillator.lean), [spectrum](../RamanujanTau/BosonicSpectrum.lean) |
| Finite-shell adjoints | Factorial-normalized polynomial monomials give square-root occupation amplitudes. The restrictions of the existing creation and annihilation maps are actual Hilbert adjoints between finite shells, with the same colored partition dimensions. Infinite Hilbert completion, unbounded-operator adjoints, and the physical interpretation remain outside the result. | [Normalization](../RamanujanTau/BosonicNormalization.lean), [adjoints](../RamanujanTau/BosonicAdjoint.lean) |
| Primes 13, 17, 19, 23 | The unconditional partition recurrence at b = m is proved, and the starting index is minimal: `ExactAtkin{13,17,19,23}.exact` show no scalar works one power higher, at every b ≥ 1. | [Public theorems](../RamanujanTau/OrdQuot/Atkin.lean) |
| Prime 29, every power | The unconditional recurrence for b ≥ 2m−1 and its evaluator from two actual seeds passed a full build and axiom audit. | [AllPowers29](../RamanujanTau/FiniteArithmetic/AllPowers29.lean) |
| Prime-29 exact threshold | The exact positive starting threshold B ≥ 2m−1 for actual partition counts is proved at every precision m ≥ 1. The numerical kernel certificate, full build, and expanded axiom audit passed. | [Complete29](../RamanujanTau/FiniteArithmetic/Complete29.lean) |
| Prime 31 exact threshold | The exact positive starting threshold B ≥ 2m−1 for actual partition counts is proved at every precision m ≥ 1, by the same method as prime 29. | [Complete31](../RamanujanTau/FiniteArithmetic/Complete31.lean) |
| Boylan–Webb b_ℓ(m) at 13, 17, 19, 23 | **b_ℓ(m) = 2⌊m/2⌋+1 for every m ≥ 1** (`AtkinExact.bEll_13`, …, `bEll_23`). This follows from exactness of the Atkin–O'Brien recurrence at every index: for every b ≥ 1 no scalar c gives ℓ^(b+1) ∣ L(b+2) − cL(b) (`ExactAtkin13.exact`, …, `ExactAtkin23.exact`), so the starting index b_ℓ(m) = m is minimal. Method: the normalized error g_b = (L(b+2) − κL(b))/ℓ^b reduces to a cusp form of weight 2(ℓ−1) mod ℓ; the offset-3 tail of one U or D step lands in 𝔽_ℓ + 𝔽_ℓ f̄ (`ExactAtkin.tail_env`, `tail_reduce`); finitely many coefficients mod ℓ² of U(B_k/E²), D(B_k/E²) and a kernel-decided finite check propagate ḡ_b ≠ 0 (`ExactAtkin.exact_of_model`); the base case is the mod-ℓ² partition determinant. In partition numbers: for every b ≥ 1 and c ∈ ℤ_ℓ some n with 24 ∣ ℓ^b n+1 has ℓ^(b+1) ∤ p((ℓ^(b+2)n+1)/24) − c·p((ℓ^b n+1)/24) (`AtkinExactPartition.partition_13`, …, `partition_23`). Earlier partial results: `SmallThreshold`, `SmallThresholdFive`. | [AtkinExact](../RamanujanTau/FiniteArithmetic/AtkinExact.lean), [AtkinExactPartition](../RamanujanTau/FiniteArithmetic/AtkinExactPartition.lean), [ExactAtkin](../RamanujanTau/FiniteArithmetic/ExactAtkin.lean), [record](verification/atkin_exact.json) |
| Boylan–Webb b_ℓ(m) at 61–139 | **b_ℓ(m) = 2m−1 for every m ≥ 1 at every prime 61 ≤ ℓ ≤ 139** (`RankRAt61.bEll_61`, …, `RankRAt139.bEll_139`), so b_ℓ(m) is known for every m at every prime 13 ≤ ℓ ≤ 139. **Verification:** the [record](verification/rank2_threshold.json) (full build, 40-declaration audit) covers 37–113; all certificates through 139, including `RankRAt137`/`RankRAt139` (built 2026-11-04, ~15–18 min and ~21 GB each, `bEll_137`/`bEll_139` axiom-clean), compiled in the 2026-11-04 full root build. Order-r odd recurrence (r = 3, 4, 5): generic Hensel lift `lift_padic_memR`, criterion `BLBound.not_mem_of_errorsR` (inverse-matrix recovery), window determinant det₀·(det C)ⁿ (`RankR.Data.det_eq`), s observations with invertible s×s Θ. One kernel evaluation per prime (≤ 4 min, ≤ 16 GB). Not covered: ℓ ≥ 149 in Lean (finite hypotheses hold numerically to 257); no uniform (all-prime) proof — G5 (ū₀ ≠ 0) is open. | [RankRPacked](../RamanujanTau/FiniteArithmetic/RankRPacked.lean), [RankRMain](../RamanujanTau/FiniteArithmetic/RankRMain.lean), [record](verification/rank2_threshold.json) |
| Boylan–Webb b_ℓ(m) at 53, 59 | **b_ℓ(m) = 2m−1 for every m ≥ 1** (`RankSAt53.bEll_53`, `RankSAt59.bEll_59`). First primes with dim S_{ℓ−1} = 4 and dim K̄ = 2: D kills a₀, a₁, a₂ (2ℓ < δ), the odd recurrence is still second order, and the error is a vector (obs₁, obs₂)(U Gₙ) moved by an invertible 2×2 matrix Θ (`RankS.Data2.divided_step`; charpolys (x+18)(x+28), (x+46)(x+58), matching the Katz-model table). Generic in the number s of killed coefficients (`RankSMod` … `RankSPacked`); one kernel evaluation per prime of packed series mod ℓ² through degree 4ℓ²+1. 61–73 (order-three recurrence) not covered. | [RankSPacked](../RamanujanTau/FiniteArithmetic/RankSPacked.lean), [RankSMain](../RamanujanTau/FiniteArithmetic/RankSMain.lean), [record](verification/rank2_threshold.json) |
| Boylan–Webb b_ℓ(m) at 37, 41, 43, 47 | **b_ℓ(m) = 2m−1 for every m ≥ 1** (`Rank2At37.bEll_37`, …, `Rank2At47.bEll_47`). These are the four primes with dim S_{ℓ−1} = 3: the odd partition series span a rank-two lattice mod ℓ and dim K̄ = 1. Method: a second-order ℓ-adic recurrence L(2n+5) − κ₁L(2n+3) − κ₀L(2n+1) = ℓ^(n+1)Gₙ (`Rank2.odd_padic2`, from the generic Hensel lift `lift_padic_mem2`), the rank-two non-membership criterion `BLBound.not_mem_of_errors2`, and the error law obs(U Gₙ₊₁) ≡ θ·obs(U Gₙ) (mod ℓ) (`Rank2.Data2.divided_step`; θ = 20, 31, 31, 17). All finite data come from one kernel evaluation per prime of packed series modulo ℓ² through degree 3ℓ²+1 (`PackedPrime.prelude`, `Rank2Packed.bEll_of_ok`). BW computed b_ℓ(2) for ℓ ≤ 89 and nothing beyond m = 3. | [Rank2Packed](../RamanujanTau/FiniteArithmetic/Rank2Packed.lean), [Rank2Main](../RamanujanTau/FiniteArithmetic/Rank2Main.lean), [record](verification/rank2_threshold.json) |
| Boylan–Webb b_ℓ(m) at 29 and 31 | BW's literal invariant (least odd b with X : Λ^odd(b,m) → Λ^odd(b+2,m) bijective) is b₂₉(m) = b₃₁(m) = 2m−1 for every m ≥ 1 (`Exact29.bEll_29`, `Exact31.bEll_31`). BW computed b₂₉ only for m ≤ 3. The general criterion is `BLBound.bEll_eq_of_not_mem` with the ℓ-adic test `BLBound.not_mem_of_errors`. | [ExactThreshold](../RamanujanTau/FiniteArithmetic/ExactThreshold.lean), [record](verification/exact_threshold.json) |
| Finite operator framework | Recurrence, survival, and evaluation theorems are proved; weighted tilings supply another identified counting model. | [Finite arithmetic](FINITE_ARITHMETIC.md) |
| Universal Theorem A | For every prime ℓ ≥ 13: the ℓ-th coefficient of a normalized eigenform in the Atkin–Lehner class is a unit above ℓ, and T_ℓ has determinant prime to ℓ on the integer sign lattice (unconditional). Injectivity of U_{ℓ²} on the half-integral space and of X̄ on V is proved unconditionally, including modularity of the explicit lifts (Ahlgren–Andersen–Dicks, Theorem 1.1): `ThetaLift.theoremA_unconditional`, `ThetaLift.aadModularity`. The upper bound b_ℓ(m) ≤ 2m−1 and the condition d_ℓ = 0 follow for every ℓ ≥ 13 (`BLBound.bEll_le`, `BLBound.dEll_eq_zero`, `BLBound.chain_stable`). Machine-checked; not yet reviewed by a human expert. | [Formalization boundary](THEOREM_A.md) |
| Multi-quintuple products | The canonical family, specializations, and sparse family with moduli `9t²+15t+7` are formal. The complete admissible sparse triple Root–Vanishing equivalence is proved in Lean for the actual infinite products. | [Research record](../RESEARCH_MULTI_QUINTUPLE.md) |

## Verification

### Current build state (2026-11-05)

**Full root build completed 2026-11-05** (`lake build RamanujanTau`, 9,793 jobs, base `7abbd21`, exit 0). The audit
[celebrated_targets.lean](../scripts/audit/celebrated_targets.lean) printed only `propext`, `Classical.choice`,
`Quot.sound` for all 120 audited declarations (output in
[celebrated_targets.axioms.txt](verification/celebrated_targets.axioms.txt)).

Earlier record: **Full root build completed 2026-11-04** (`lake build RamanujanTau`, 9,699 jobs, base `f3be2fe`, exit 0, no errors),
after the 2026-11-03/04 campaign. The audit [celebrated_targets.lean](../scripts/audit/celebrated_targets.lean)
(imports the whole root) then printed only `propext`, `Classical.choice`, `Quot.sound` for all 70 audited
declarations. `RankRAt137` and `RankRAt139` were compiled in this round (`bEll_137`, `bEll_139` axiom-clean).
The earlier 9,430-job record in [rank2_threshold.json](verification/rank2_threshold.json) (base `7987c63`) predates
the campaign. Memory-heavy modules: the packed `RankRAt*` certificates (about 21 GB peak each) and
`GORZXiEff.CVData*` (about 9 GB).

### Partition entropy (2026-11-03)

The [entropy module](../RamanujanTau/HardyRamanujan/Entropy.lean) and isolated
[saddle algebra](../RamanujanTau/CardySaddle.lean) passed a focused build.
All ten declarations in the [dedicated audit](../scripts/audit/partition_entropy.lean)
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The [verification record](verification/partition_entropy.json) records the
build status, source hashes, exact normalization, and remaining physical
identification and mock Jacobi obligations.
The new module is available through `import RamanujanTau.HardyRamanujan.Entropy`
and is not added to the root import graph. The full build was stopped after
roughly 24 minutes while two pre-existing arithmetic certificates were still
computing under heavy memory pressure; a successful full build is not claimed.

### Colored partition entropy (2026-11-03)

The standalone import `RamanujanTau.ColoredPartitionEntropy` passed its
**8,501-job focused build**. All **23 declarations** in the
[axiom audit](../scripts/audit/colored_partition_entropy.lean) depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The
[verification record](verification/colored_partition_entropy.json) covers the
finite counting model, exact generating-series and analytic-discriminant
bridges, general positive-color entropy limit, coefficient shift, and Cardy
normalization at `C=2`.

This completes the colored leading-entropy step that was pending in the
earlier ordinary-partition record. Colored logarithmic corrections,
quantitative remainders, a physical state equivalence, and the quarter-BPS
mock Jacobi construction remain outside the result. The public root import
is unchanged; the earlier full-build limitation still applies, and no full
build is claimed for this step.

### Bosonic occupation model (2026-11-03)

The standalone import `RamanujanTau.BosonicOccupation` passed its
**8,502-job focused build**. The **23-declaration**
[audit](../scripts/audit/bosonic_occupation.lean) checks the occupation/partition
equivalence, energy-derived mode bounds, unique vacuum, orthonormal basis,
shell dimensions, discriminant identity, charge shift, and entropy limits.
All dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`.
The [verification record](verification/bosonic_occupation.json) records the
source snapshot and repository checks.

This supplies an explicit mathematical occupation model and its finite shell
Hilbert spaces. The offset −1 is specified, not derived from a regularized
vacuum energy. A full Fock representation with creation and annihilation
operators, a physical string-state equivalence, and a black-hole area law
remain outside the proof. The public root import is unchanged; no new full
build is claimed, and the earlier full-build limitation still applies.

### Algebraic oscillator spectrum (2026-11-03)

The standalone import `RamanujanTau.BosonicSpectrum`, including
`RamanujanTau.BosonicOscillator`, passed its **8,504-job focused build**.
All **30 declarations** in the
[audit](../scripts/audit/bosonic_spectrum.lean) depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The
[verification record](verification/bosonic_spectrum.json) records the exact
source hashes and repository checks.

This extends the occupation model with algebraic operators satisfying all
three canonical commutation relations, their Hamiltonian commutators, and
an exact identification of the Hamiltonian's eigenspaces with the earlier
finite shells. The 24-species charge eigenspaces have dimension `p_24(n+1)`
and the proved leading entropy constant `4π`.

The representation uses an unnormalized monomial basis. Hilbert-space
adjoints, completion, an unbounded self-adjoint Hamiltonian, and an analytic
infinite trace are not established. The vacuum offset remains an input;
physical string/gravity identification and the quarter-BPS mock Jacobi
construction remain open here. No full build is claimed; the public root
import graph is unchanged and the earlier full-build limitation still applies.

### Finite-shell adjoints (2026-11-03)

The standalone import `RamanujanTau.BosonicAdjoint`, including
`RamanujanTau.BosonicNormalization`, passed its **8,506-job focused build**.
All **29 declarations** in the
[audit](../scripts/audit/bosonic_adjoint.lean) depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The
[verification record](verification/bosonic_adjoint.json) records the checked
source snapshot and repository checks.

The normalized monomials have the square-root occupation amplitudes. Their
coordinates identify the exact polynomial energy eigenspaces with finite
Euclidean shells. Transported restrictions of the original polynomial
operators satisfy `annihilateShell a n = (createShell a n).adjoint`, with the
inner-product identity proved for arbitrary shell vectors. Their dimensions
remain the earlier colored partition counts.

This closes the finite-shell adjoint step. Infinite Hilbert completion,
unbounded-operator domains and adjoints, and the physical string/gravity
identification remain outside this result. The vacuum offset remains an
input. The public root import graph is unchanged; no full build is claimed
and the previously recorded full-build limitation remains.

### Nested radical (2026-11-01)

[NestedRadical](../RamanujanTau/NestedRadical.lean) supplies a quantitative
convergence proof of the classical identity. The
[verification record](verification/nested_radical.json) and
[six-declaration audit](../scripts/audit/nested_radical.lean) cover the finite
bounds, exact error identity, error estimate, general limit, and classical
specialization. This is separate from the open four-direction research targets.
The **9,352-job full build** and all six audit declarations passed. Axiom
dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`.

The subsequent [affine-family development](../RamanujanTau/NestedRadicalAffine.lean)
proves convergence of the whole family and the sharper exponential error
estimate. [The converse](../RamanujanTau/NestedRadicalClassification.lean)
classifies exactly which nonnegative affine radicands yield a positive-offset
linear limit for every nonnegative starting value.
See its [verification record](verification/nested_radical_affine.json) and
[dedicated audit](../scripts/audit/nested_radical_affine.lean). The earlier
record preserves the original reciprocal-depth bound and proof snapshot.
The follow-up passed a **9,354-job full build** and a **16-declaration axiom
audit**, again with only the three standard axioms.

### Four-direction follow-up (2026-11-01)

| Target | Checked progress | Remaining theorem |
|---|---|---|
| Four-factor classification | Complete classifications at `(41;1,4,5,9)` and `(53;5,2,7,9)`. Infinite vanishing families now cover both m²+n² and 2m²+n²; an unconditional family at 450t²+180t+43 includes unboundedly many moduli outside sums of two squares. The earlier sixteen reflection maps have an exact branch-compatibility classification. | A classification for arbitrary admissible four-factor products; exclusion of extra zeros in the parameter families |
| All-prime exact stabilization | Lean proves survival for every iterate in five saved finite models, at 233, 257, 307, 401, 607. Two Katz truncation depths agree on each matrix and seed. Exact thresholds on actual partition data: `bEll 607 2 = 3` (`Rank607Threshold.bEll_607_two`), and `bEll 29 m = bEll 31 m = 2m−1` for every m (`ExactThreshold`). | Identification with the actual second-order partition operator, and an all-prime seed argument |
| Delayed rank at 607 | **Proved unconditionally:** `rEll 607 m = 25` for every m≥2 (`Rank607Final.rEll_607`). The saved 25×25 minor is identified with actual partition coefficients by one kernel evaluation. See the [verification record](verification/rank607_final.json). At m=2 the module itself is proved: Λ ≅ (ℤ/607²)²⁴ ⊕ ℤ/607 (`Rank607Structure.lamEquiv`), so 25 generators but 24 free summands. At m=1 it is (ℤ/607)²⁴ and `rEll 607 1 = 24` (`Rank607One`). | Whether this contradicts Boylan–Webb depends on their undefined notion of rank for a non-free module; expert review. The Smith profile for m≥3 is not proved. |
| Triple-product quarter-prime witness bound | Exact tests cover all 4,539 canonical triples through 151 and 800 sampled projective rescalings up to 3000, without a failure. Lean proves the first witness at `(103;1,22,37;R=63)` is N=23. | Prove N≤⌊p/4⌋ uniformly for triples, including control of signed cancellation |

The initial follow-up's **9,348-job full build** and **23-declaration axiom audit** passed, with
dependencies limited to `propext`, `Classical.choice`, and `Quot.sound`.
The [verification record](verification/four_directions.json) and
[dedicated audit](../scripts/audit/four_directions.lean) cover these changes.
The saved finite-model theorems are not unconditional partition theorems.
The four-factor and prime-103 coefficient theorems concern the actual infinite
products. The subsequent **9,351-job full build** and **11-declaration axiom
audit** also passed, with the same standard axiom dependencies. The
[infinite-family follow-up record](verification/four_family.json)
and [dedicated audit](../scripts/audit/four_family.lean) cover the subsequent
all-parameter theorem and uniform denominator identity. The
[research statement](../RESEARCH_MULTI_QUINTUPLE.md#an-infinite-four-factor-family)
lists the four residue polynomials and the exact scope. The subsequent
[two-parameter record](verification/four_plane.json) covers the plane theorem
and the full converse at 53; its [research statement](../RESEARCH_MULTI_QUINTUPLE.md#two-parameter-plane-theorem)
lists the hypotheses and the remaining universal-converse gap. The later
[uniform-reflection record](verification/four_reflection.json) covers the
four congruence families and the exact converse for the specified maps.
The latest [second-family record](verification/four_binary.json) covers actual
infinite vanishing at p=2m²+n² and the unconditional all-parameter family.
Its **9,364-job full build** and **20-declaration axiom audit** passed with only
the same three standard axioms. An [independent product comparison](verification/four_binary_check.json)
checks 259,467 coefficients across 17 parameter pairs.

The [witness follow-up](verification/four_witnesses.json) now gives actual-product
Lean proofs of two **four-factor** counterexamples: `(17;2,3,5,8;R=5)` first
becomes nonzero at N=7, and `(2521;1,35,36,71;R=2273)` at N=632. Lean also proves
that any universal linear cutoff N≤cp for admissible four-tuples requires
c≥7/17. Neither p/4 nor 2p/5 works. This does not establish a sufficient bound.
The [earlier integer replay](verification/four_quarter_counterexample.json)
also finds first witness N=631 for residue 67 at 2521; that separate residue
remains computational. The original triple-product conjecture is unaffected.
A [finite frontier scan](verification/four_quintuple_frontier.json)
saves 289 candidate products among 3,174 isotropic tuples through prime 71;
zero coefficients through N=2p are not an infinite-vanishing proof.

The map classification is not the universal coefficient converse. None of the
four original universal targets is complete. The earlier published snapshot
below remains unchanged.

### Latest published proof: admissible sparse triples

The proof snapshot in commit `1017be1` passed a **9,336-job full build**,
a **251-declaration multi-quintuple axiom audit**, the independent arithmetic
checks, and the repository checker (982 Lean source/audit files, 25 Markdown
files, and 232 local links). All audited dependencies are among `propext`,
`Classical.choice`, and `Quot.sound`. These counts describe the checked proof
snapshot; documentation-only updates may change the link count.

The [verification record](verification/full_converse_lean.json) also retains
the earlier 9,341-job development-worktree build. The difference is five
unrelated local modules omitted from the published snapshot, not a change to
the converse proof. The [raw report](verification/full_converse_lean.axioms.txt)
and [catalog](RESULTS.md#multi-quintuple-products-complete-admissible-triple-classification)
identify the theorem and its exact hypotheses.

### Earlier verification records

The prime-29 milestone's full build passed 9,131 jobs.
The expanded finite-arithmetic audit checks 76 declarations, including prime 31,
the prime-square reconstruction and determinant reductions, and the general
rank-lifting identities. Its axiom
dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or additional axiom. The
[verification record](verification/prime29.json) pins the source revision,
toolchain, Mathlib revision, and checked commands. The
[raw axiom report](verification/finite_arithmetic.axioms.txt) lists the audited declarations.
The [607 reconstruction record](verification/rank607-reconstruction.json)
records the subsequent full build (9,291 jobs), independent exact replay,
and the remaining numerical kernel-certificate boundary. The subsequent
[rank-lifting record](verification/rank_lifting.json) records a full build of
9,292 jobs and five additional audited algebraic theorems.

The [sparse-family verification record](verification/eisenstein_family.json)
records the subsequent build and the dedicated audit of the unconditional
all-parameter coefficient theorem. Independent direct Pochhammer products
agree with Watson sums for the first six parameters, including modulus 133.
The separate lattice symmetry argument remains a paper proof: its exact
checks cover 3,172 projective classes through prime 1000 and 9,376
automorphisms, without turning that finite census into a universal Lean proof.

The subsequent [phase-pairing verification record](verification/phase_pairing.json)
records a 9,294-job full build and the expanded six-declaration multi-quintuple
audit, with only the standard axioms. The new algebraic theorem forces
opposite-phase balance on complete antipodal shells without a size bound.
It does not prove a single geometric symmetry behind all the pairings.

The subsequent full-converse paper argument uses the actual Watson phases:
short partners preserve dot products modulo p², and the strict norm bound
turns these congruences into equalities. A geometric argument supplies
supported generators for every p>=1250. An independent checker verifies
14,369 short-generator certificates below that bound and settles the two
p=13 triples with explicit roots and 20 nonzero coefficients. Six new local
algebraic lemmas are formal in `MultiQuintupleShortCoherence.lean`. The
paper argument supplied the blueprint for the completed formalization below.
The [initial verification record](verification/full_converse_paper.json)
reports a successful 9,295-job full build and 12 audited declarations using
only the standard axioms, including the six new algebraic lemmas.

The complete admissible sparse triple converse is now proved in
[`MultiQuintupleFullConverse.lean`](../RamanujanTau/MultiQuintupleFullConverse.lean).
For prime p≠3, 0<i<j<k<p/2, p dividing i²+j²+k², and R<p,
`HasProjectiveRootTarget p i j k R` is equivalent to
`PersistentTripleVanishing p i j k R`. The theorem concerns the actual infinite
products. Poisson summation and shell separation, opposite phase partners,
integral short generation, and the exact root-target extraction are all
proved. The generation argument covers p≥1250 geometrically and the smaller
primes by kernel-checked certificates; p=13 has its separate complete proof.
The bound 1250 is sufficient, with no minimality claim.
See the [full Lean verification record](verification/full_converse_lean.json).
The [earlier progress record](verification/short_converse_lean.json) remains
an unchanged historical snapshot of the previous proof boundary.

The Theorem A development proves all-prime ordinarity on the prescribed
U₂/U₃ eigenspace of the level-six integral model and on reductions of actual
complex modular forms, and derives the eigenvalues from Atkin–Lehner signs.
The half-integral result includes a formal proof of `AADModularity` by a theta kernel. Its other inputs are proved eta bases, integral descent,
Serre differentiation, Hasse divisibility, minimal-weight theta-cycle laws,
and a finite certificate for the full weight-six operator identity.
The [dedicated audit](verification/theorem_a.axioms.txt)
checks 375 declarations with dependencies confined to the same three standard
axioms. The full build passed 9,288 jobs. Both generated eta certificate files
reproduce byte-for-byte. With the reconstruction and rank-lifting modules added, the
source/documentation checker passed 941 Lean source/audit files and 25 Markdown
files; all local links were checked. The remaining correspondence
input is listed in the [formalization boundary](THEOREM_A.md).

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

## Results of 2026-11-03

| Track | Lean status | Remaining |
|---|---|---|
| Kloosterman τ bound | `TauBound.tau_isBigO_47_8_unconditional`: τ(n) = O(n^{47/8+ε}), no hypotheses. **Superseded by Weil's exponent: `StepanovAS.weilPrimeBound` (\|S(1,b;p)\| ≤ 2√p) and `StepanovAS.tau_isBigO_23_4_unconditional` τ(n) = O(n^{23/4+ε}) (Weil 1948), unconditional**, via Stepanov for y^p − y = x + b/x over F_{p^r} with Hasse derivatives, rationality of the Kloosterman L-function (`KloostermanL.kloosterman_L_rational`, K_r = −(α^r+β^r), αβ = p) and amplification. Intermediate: `Stepanov.tau_isBigO_35_6_unconditional` τ(n) = O(n^{35/6+ε}) via Salié's bound (`saliePrimeBound`), from Stepanov's Hasse–Weil bound `hasseWeil_charSum_le` \|Σχ(f(x))\| ≤ 12m²√p and `hasse_elliptic` \|#E(F_p) − p\| ≤ 108√p. `WeilKloosterman`: sharp prime-power bound \|S(1,n;p^k)\| ≤ 6√(p^k) for k ≥ 2, and the conditional forms `tau_isBigO_35_6_of_salie` / `tau_isBigO_23_4_of_weil` (hypotheses now discharged). Order: 47/8 > 35/6 > 29/5 (Rankin, not formalized) > 23/4 | Deligne's 11/2 (not formalized) |
| Turán inequalities for Ξ | **`GORZXiEff.turan_gamma_unconditional`, `jensen2_gamma_unconditional`**: γ(n)γ(n+2) ≤ γ(n+1)² and J^{2,n}_γ hyperbolic for every n ≥ 0 (Csordas–Norfolk–Varga 1986; GORZ Theorem 2, d = 2), unconditional — `CV.cvHyp_holds` proves the Csordas–Varga monotonicity by an even Taylor model near 0 plus kernel-checked interval cells; `gamma_eq_mom` (γ(n) as moments of Riemann's Φ) unconditional. d ≤ 8 for n ≤ 300 checked numerically | d = 3 (Dimitrov–Lucas; see next row); 4 ≤ d ≤ 8 |
| Ξ Jensen d = 3 (Dimitrov–Lucas) | Reduction only: `GORZXiD3.hyperbolic_cubic`, `disc_jensen3` (Disc J^{3,n} = 27·HOT), Lipschitz reformulation `hot_nonneg_iff_lip`, unconditional. `jensen3_gamma` is conditional on `DLHyp`, which is **equivalent** to the higher-order Turán inequalities themselves (`dlHyp_iff`) — so this is a restatement, not progress on the analytic input. HOT checked numerically for n ≤ 10⁴ | an analytic proof of HOT for Ξ (Dimitrov–Lucas §2–3 not yet read) |
| Lehmer's conjecture, small n | `LehmerSmall.lehmer_below_214928639999`: τ(n) ≠ 0 for every 1 ≤ n < 214,928,639,999 (Lehmer 1947), unconditional (supersedes the earlier `lehmer_below_74627999`, `lehmer_below_258710399` and `lehmer_below_21492863999`); `tau_prime_pow_ne_zero` (least zero is prime); all-n congruences mod 7, 25, 3, 9, a 2-adic condition, and the deep prime-zero conditions mod 2⁹, 3⁵, 5³ from quasimodular integrality. See [LEHMER_SMALL_N](LEHMER_SMALL_N.md) | Lehmer's 1947 bound 214,928,639,999 (needs Wilton's (p/23) = −1, or 2¹¹, or 5⁴) |
| Rankin–Selberg, every level-one cusp form | `RankinSelbergGeneral.rankinSelberg_asymptotic`: for every f ∈ S_k(SL₂(ℤ)), (1/N)Σ_{n≤N}|a(n)|²/n^{k−1} → (3/π)(4π)^k‖f‖²/(k−1)!; `horocycle_tendsto` for ‖f‖²y^k; explicit instances at weights 16, 18, 20, 22, 26 and for ΔE₄ᵃE₆ᵇ; unconditional | Done: `RankinSharpGeneral.rankinSelberg_power_saving_sharp_general`, error O(N^{1−δ}) for every δ < 1/5 and every f ∈ S_k(SL₂(ℤ)) (supersedes `RankinErrorGeneral`'s 1/84), with integer instances in weights 16–26; higher level Γ₀(N) not attempted |
| Hecke's L-function of Δ | `HeckeL.heckeLambda_entire`, `heckeLambda_functional_equation` (Λ(12−s) = Λ(s) for Λ = (2π)^{−s}Γ(s)L(Δ,s)), `heckeLambda_bdd_strip`, `tauLSeries_entire`, `tauL_real_eq_zero_iff` (real zeros exactly 0, −1, −2, …), `tauLSeries_center_pos` (L(Δ,6) > 0), `tauL_bound_re_four`; **`HeckeConvex.LSeriesSummable_tau_of_gt_13_2`** (Rankin 1939: Σ|τ(n)|n^{−σ} < ∞ for σ > 13/2, from the Rankin–Selberg asymptotic by Cauchy–Schwarz); **`HeckeConvex.tauL_convexity`** (‖L(Δ,6+it)‖ ≪_ε (1+\|t\|)^{1/2+ε}) and `tauL_convexity_strip` (≪ (1+\|t\|)^{13/2−σ+ε} on 11/2 ≤ σ ≤ 13/2); unconditional. See [HECKE_CONVEXITY](HECKE_CONVEXITY.md). **All level-one cusp forms** (`HeckeConvexGeneral`): Hecke's theorem Λ(f,k−s) = i^k Λ(f,s) with Λ entire (`heckeLambda_functional_equation`), Σ_{n≤N}\|a_f(n)\| ≪ N^{(k+1)/2} and absolute convergence past (k+1)/2 (`LSeriesSummable_coef`), and the convexity bound \|L(f,k/2+it)\| ≪ (1+\|t\|)^{1/2+ε} (`fL_convexity`, strip version `fL_convexity_strip`); see [HECKE_CONVEXITY_GENERAL](HECKE_CONVEXITY_GENERAL.md). **Zeros** (`HeckeZeros`): Euler product and L(Δ,s) ≠ 0 on Re s > 13/2; for Re s < 11/2 the zeros are exactly 0, −1, −2, …; so `tauL_zeros_in_strip`: all nontrivial zeros have 11/2 ≤ Re s ≤ 13/2, symmetric under s ↦ 12−s and s ↦ s̄; see [HECKE_ZEROS](HECKE_ZEROS.md). **Edge non-vanishing** (`EdgeNonvanishing.tauL_ne_zero_edge`): L(Δ,13/2+it) ≠ 0 for all t, without Sym² or Deligne (a 25-parameter positivity product F = ζ·L²L̄²·(ζ(2s)R)²·…, Satake bound ‖α‖² ≤ p from Rankin, and Abel continuation of the Rankin–Selberg series from Rankin's O(N^{3/5})); so nontrivial zeros lie in the open strip 11/2 < Re s < 13/2; see [EDGE_NONVANISHING](EDGE_NONVANISHING.md). **PNT for τ** (`TauPNT`): unconditionally −L'/L(Δ,s+11/2) = Σ Λ_Δ(n)n^{−s} is continuous on Re s ≥ 1 and Σ_p τ(p)p^{−11/2}log p·p^{−σ} converges as σ → 1⁺ (`tau_PNT_smoothed`); conditional on `[DeligneBound]`: τ(p) changes sign infinitely often over primes (`tau_prime_sign_changes`); conditional on `[DeligneBound]` only: Σ_{p<N} τ(p) log p = o(N^{13/2}) (`WienerIkehara.tau_PNT_tau_deligne`), since `WienerIkehara.wienerIkehara` proves the Tauberian hypothesis; also the classical PNT `WienerIkehara.PNT_psi` (ψ(x)/x → 1); the Wiener–Ikehara proof is ported from PrimeNumberTheoremAnd (Apache-2.0); see [TAU_PNT](TAU_PNT.md), [WIENER_IKEHARA](WIENER_IKEHARA.md). **All level-one eigenforms** (`EigenformEdge`, f with `IsNormalizedEigenform f`: real, a(1)=1, multiplicative, Hecke recursion — true by Hecke 1937, proved for Δ): Euler product and L(f,s) ≠ 0 past (k+1)/2; `fL_ne_zero_edge_of_ne`: L(f,(k+1)/2+it) ≠ 0 for t ≠ 0, unconditional; conditional on the real point L(f,(k+1)/2) ≠ 0 (proved when f(iy) ≥ 0, e.g. Δ): all t, zeros in the open strip, smoothed PNT; additionally under `[DeligneBoundF f]`: PNT Σ_{p<N} a_f(p) log p = o(N^{(k+1)/2}) and sign changes over primes; see [EIGENFORM_EDGE](EIGENFORM_EDGE.md). **Hardy's theorem** (`HardyZeros.tauL_infinitely_many_critical_zeros`): infinitely many zeros on Re s = 6, via the Fourier identity ∫Λ(6+it)e^{αt}dt = 2πe^{6iα}Δ(ie^{iα}) and cusp decay at −1; see [HARDY_ZEROS](HARDY_ZEROS.md); for every nonzero level-one cusp form with real coefficients, all weights including root number −1 (`HardyZerosGeneral.fL_infinitely_many_critical_zeros`), see [HARDY_ZEROS_GENERAL](HARDY_ZEROS_GENERAL.md). **Zero count** (`HardyCount.tauL_critical_zero_gaps`, `tauL_critical_zeros_count`): every window [t₀ ± K t₀^{1/2+ε}] contains a critical zero, so N₀(T) ≫_ε T^{1/2−ε}; see [HARDY_COUNT](HARDY_COUNT.md); improved to **N₀(T) ≫ T/log log T** (`HardyCountLinear.tauL_critical_zeros_loglog`) by a Schur/Fubini mean-square bound for the windows and the doubly-exponential kernel exp(−exp(z²)); see [HARDY_COUNT_LINEAR](HARDY_COUNT_LINEAR.md); and finally **Hafner's N₀(T) ≫ T** (`HardyCountHafner.tauL_critical_zeros_linear`), from the uniform mean square ∫_T^{2T}\|L(Δ,6+x+it)\|² ≪ T/x for 0 < x ≤ 1 (`mean_square_uniform`, Hecke–Hafner Plancherel route); see [HARDY_COUNT_HAFNER](HARDY_COUNT_HAFNER.md). **Critical-line mean square** (`CriticalMeanSquare.critical_mean_square_upper`): ∫₀ᵀ\|L(Δ,6+it)\|² dt ≪ T log T, with an exact weighted Parseval identity `weighted_parseval`; with the matching lower bound `CriticalMeanSquareLower.critical_mean_square_isTheta`: ∫₀ᵀ\|L(Δ,6+it)\|² ≍ T log T (ray/block comparison with Rankin's Σ τ(n)²e^{−4πny} ≫ y^{−12}); Good's asymptotic (constant 2c ≈ 0.768, checked numerically) is not formalized; see [CRITICAL_MEAN_SQUARE](CRITICAL_MEAN_SQUARE.md), [CRITICAL_MEAN_SQUARE_LOWER](CRITICAL_MEAN_SQUARE_LOWER.md). **Partial sums** (`TauPartialSums.tau_partial_sum_bound`): Σ_{n≤x} τ(n) ≪_ε x^{181/30+ε}, and x^{(k−1)/2+8/15+ε} for every level-one cusp form (`cuspForm_partial_sum_bound`), by a Riesz-mean contour shift plus differencing with Rankin's O(N^{3/5}); see [TAU_PARTIAL_SUMS](TAU_PARTIAL_SUMS.md); improved to **x^{59/10+ε}** (x^{(k−1)/2+2/5+ε} in general, `TauPartialSumsSharp.tau_partial_sum_sharp`) by a degree-2 port of Landau's method: dual expansion `dual_rep`, sharp Bessel-type kernel `kernelZero_sharp` (J₀ ≪ y^{k/2−1/4}), signed Landau bracket; see [TAU_PARTIAL_SUMS_SHARP](TAU_PARTIAL_SUMS_SHARP.md). **Mean square** (`MeanSquare.mean_square_tauL`): (1/T)∫₀ᵀ\|L(Δ,σ+it)\|² dt → Σ τ(n)²n^{−2σ} for every σ > 37/6, with a Dirichlet-polynomial mean-value theorem `mv_poly`; see [MEAN_SQUARE](MEAN_SQUARE.md); **`MeanSquareFull.mean_square_tauL_full`**: the full classical range σ > 6 (Carlson–Potter), by a functional-equation bootstrap 1/6 → 1/10 → 1/14 → … with uniform Stirling `norm_tauL_left_le`; see [MEAN_SQUARE_FULL](MEAN_SQUARE_FULL.md) | subconvexity (Good 1982, \|t\|^{1/3+ε}) not attempted; critical zeros: positive proportion (Hafner 1987) needs mollifiers; critical-line mean square: Good's asymptotic not formalized (weighted version est. 400–600 lines, then a Karamata Tauberian step); partial sums: 2/5 is optimal for Landau's method with Rankin's short sums; 35/6 (Hafner–Ivić) needs Deligne-strength short sums or cancellation in the dual head sum; removing the +ε est. 600–900 lines; zero-free region left of Re s = 13/2 not attempted; PNT for τ: removing Deligne needs L(Sym²Δ,1+it) ≠ 0; general eigenforms: the real edge point needs Rankin–Selberg continuation to Re s > 1/2 + Landau's lemma (est. several thousand lines), and no other eigenform than Δ is exhibited (Mathlib lacks Hecke operators); edge non-vanishing for other eigenforms not done |
| Sign changes of τ | `TauSigns.tau_sign_changes` (τ(n) takes both signs beyond every N), `hecke_partial_sum` (Σ_{n≤M} τ(n) = O(M^{6+ε}), Hecke), `tau_sign_change_short_interval_limit` (both signs in every (x, x + A x^{θ}] for every θ > 3/4), `card_signChanges_ge_limit` (≫ X^{1/4−ε} sign changes up to X), the Hecke × Weil limit of the method, and versions parametrized by any power-saving exponent δ, unconditional | below x^{3/4} needs Deligne; ≫ X sign changes (Matomäki–Radziwiłł) out of reach |
| Non-vanishing of τ, counting | `TauDensity.tau_eq_zero_iff` (τ(n) = 0 ⇔ some prime p with τ(p) = 0 divides n to an odd power), `card_tau_ne_zero_ge_sqrt` (⌊√N⌋ ≤ #{n ≤ N : τ(n) ≠ 0}, from τ(m²) ≠ 0), `card_tau_ne_zero_ge_rpow` (Weil + Rankin–Selberg), `card_tau_ne_zero_ge_nine_tenths` (≥ 0.9N for log N ≤ 10⁹), unconditional | Done: `card_tau_ne_zero_ge_div_log`, #{n ≤ N : τ(n) ≠ 0} ≥ N/(585103(1+log N)) for every N (τ(x²+691y²) ≠ 0 plus a Cauchy–Schwarz energy bound). Remaining: N/(log N)^{1/690} needs Selberg–Delange / PNT in progressions mod 691; Serre's positive density needs Chebotarev |
| τ(n) = Ω(n^{11/2}) | **`TauOmega.tau_omega`**: \|τ(n)\| ≥ c n^{11/2} infinitely often; `tau_not_isBigO`: τ(n) ≠ O(n^{11/2−δ}) for δ > 0; unconditional, from `rankinSelberg_two_sided`; for every nonzero level-one cusp form, `coeff_omega` / `coeff_not_isBigO`. See [TAU_OMEGA](TAU_OMEGA.md). **Sign changes for all real cusp forms** (`LandauSigns.coeff_sign_changes`, via a new proof of Landau's theorem `LandauSigns.landau`); see [LANDAU_SIGNS](LANDAU_SIGNS.md) | — |
| Rankin–Selberg | `RankinSelberg.rankinSelberg_two_sided`: Σ_{n≤N} τ(n)²/n¹¹ ≍ N (both bounds, unconditional, ineffective constants c₁, c₂, via Parseval on horocycles and a Farey lower bound); numerically the constant is c ≈ 0.384084. **`EisensteinReal.rankinSelberg_asymptotic_zagier_unconditional`**: (1/N)Σ_{n≤N} τ(n)²/n¹¹ → (3/π)(4π)¹²‖Δ‖²/11!, unconditional (Rankin–Selberg asymptotic with Zagier's constant), via `horocycleLimit_zagier` (horocycle equidistribution by lattice-point counting, Möbius inversion and a box sandwich) and Karamata's Tauberian theorem | power-saving error proved unconditionally: **`RankinError.rankinSelberg_power_saving_84`**, Σ_{n≤N} τ(n)²/n¹¹ = cN + O(N^{1−1/84}) (`rsUnfold` proves the unfolding identity); Sharpened further: **`Stirling.rankinSelberg_power_saving_third`**, error O(N^{1−δ}) for every δ < 1/3, for τ and (`rankinSelberg_power_saving_third_general`) every level-one cusp form, via new complex-Γ ratio bounds in vertical strips (`Stirling.norm_Gamma_ratio_le_of_le`, two-sided Stirling `norm_Gamma_le_stirling`). Earlier: `RankinSharp.rankinSelberg_power_saving_sharp`, every δ < 1/5 (convexity bound for (s−1)ζ(2s)D(s) via exact Gamma ratios, square-twist and Möbius inversion). **Rankin's 2/5, unconditional:** **`KernelPhase.rankinSelberg_landau_uncond`** (τ), `rankinSelberg_landau_61_100_uncond` (error O(N^{61/100})) and `rankinSelberg_landau_general_uncond` (every level-one cusp form): error O(N^{1−δ}) for every δ < 2/5, by Landau's method (`RankinLandau.dual_rep`, `landau_core`) with the Γ-integral bound `KernelOneBound` proved in `KernelPhase` (sharp ‖J₁(y)‖ ≪ y^{9/8} via a bent contour through the saddle height, modulus-only). **Exact: `RankinExact.rankinSelberg_exact`**: Σ_{n≤N} τ(n)²/n¹¹ = cN + O(N^{3/5}) with no ε (Rankin 1939), and `rankinSelberg_exact_general` for every level-one cusp form, via the sharp top kernel `RankinExact.kernel_sharp` (‖J_j(y)‖ ≪ y^{3j/4+3/8}) and exact partial summation in place of Rankin's trick (`landau_sharp`). See [RANKIN_LANDAU](RANKIN_LANDAU.md), [KERNEL_PHASE](KERNEL_PHASE.md), [RANKIN_EXACT](RANKIN_EXACT.md). See [RANKIN_ERROR](RANKIN_ERROR.md) |
| GORZ for Riemann Ξ | **`GORZXi.xi_gorz_unconditional`**: for every d, the Jensen polynomials of the Taylor coefficients γ(n) of (−1+4z²)Λ(1/2+z) (Mathlib's `completedRiemannZeta`) are hyperbolic for all large n and the renormalized polynomials → H_d; no hypotheses (`xiKernelHyp_holds`, elementary Stein-identity moment bounds). Also the abstract GORZ Theorems 3 and 6 and the integral formula `gammaMathlib_eq` | effective thresholds; GORZ Theorem 2 for 3 ≤ d ≤ 8 (d = 2 is the Turán row above) |
| GORZ for p(n) | `GORZ.jensen_eventually_hyperbolic` (every d), `tendsto_coeff_Jhat` (Hermite limit), no hypotheses | explicit N(d) beyond d = 7 (the abstract GORZ Theorem 3 is `GORZXi.gorz_thm3`, row above) |
| Jensen thresholds | `JensenThreshold.jensen6_threshold_unconditional` (N(6)=610) and `jensen7_threshold_unconditional` (N(7)=908), Larson–Wagner convention, no hypotheses | d ≥ 8; Lean versions of d ≤ 5 |
| Dragonette | `Dragonette.dragonette_literal`; `Andrews.alpha_sign` and `Andrews.rank_parity_sign_all`: (−1)^{n+1}α(n) > 0 for every n ≥ 1, by an elementary argument (Watson's identity + distinct-odd-part partition bounds); no hypotheses | `Andrews66.andrews_k1_isBigO` (unconditional, k = 1 term with power saving); `Andrews66.andrews_1966_sqrt_log_of_Hb`: the full Andrews 1966 asymptotic α(n) = Σ_{k ≤ √n/2} main terms + O(√n log n), stated conditionally on the named bound `Hb` (now proved, see below). `Andrews66.andrews_1966_printed_isBigO_of_Hb` states it with Andrews' printed main term Σ_{k ≤ √n} (−1)^{⌊(k+1)/2⌋}A_{2k}(n − k(1+(−1)^k)/4)·π(24n−1)^{−1/4}I_{1/2}(π√(24n−1)/12k)/k, the identification proved unconditionally (`Ab_printed`, via the Dedekind congruence `T_cong`). **`MockCusp.Hb_holds` proves `Hb` at every cusp (D = 3/2), so `MockCusp.andrews_1966_unconditional` gives Andrews' 1966 theorem with his printed main term and error O(n log n), with no hypotheses** (inequality-only route: Appell–Lerch forms, Poisson summation, contour shift; Watson's f+b = 2φ(−q), f+4ψ(−q) = b). **`MockCusp.HbSharp_holds` (D = 1) gives `MockCusp.andrews_1966_sqrt_log_unconditional`: Andrews' exact error O(√n log n), unconditional.** Exact Andrews–Dragonette series: out of reach on this route ([analysis](ANDREWS_DRAGONETTE_EXACT.md)). `AndrewsDragonette.not_Hb_of_neg` proves no bound with D < 0 holds, so absolute-value circle-method bounds cannot give exactness; convergence (`adPartial_converges_of_HKS`) is proved conditional on a named Kloosterman-sum cancellation hypothesis `HKS` (θ < 1/2, Ahlgren–Dunn-type, needs Kuznetsov); exactness needs Zwegers/Bringmann–Ono, not started. (The uniform bound on f ∓ (−1)^k b near every h/2k, once listed here as remaining, is `Hb`, now proved.) |
| Ono–Weaver congruences | `AtkinSporadic.Weaver.ono_13_unconditional`, `weaver_17_unconditional`, 81 families in `OnoWeaverMore` (30 Ono type ℓQ⁴, 51 Atkin type ℓQ³ with (m/Q)=ε) for ℓ ∈ {13,…,31} and all hit primes Q < 500, table in [ONO_WEAVER_EXTENSIONS](ONO_WEAVER_EXTENSIONS.md); eigen-relations `etaHeckeMod_13/17/19/23`, `eigen_29/31` for every prime Q ≥ 5 | Q ≥ 500 (longer prefix); ℓ ≥ 37; overlap with Weaver's tables unchecked |
| Atkin 13 ∣ p(17303n+237) | `Atkin13.atkin_13_unconditional`, plus `atkin_13_class_unconditional` and `atkin_13_Q37_class_unconditional`; no hypotheses. `GaussSign.etaHecke_all`: T(Q²) on η⁻¹S_k for every prime Q ≥ 5 and k ≥ 2, unconditional, via Gauss's sign theorem `GaussSign.gaussQuad_eval` (every odd modulus, theta-function proof). Note: the auxiliary `HalfHecke.GaussSign Q k` is false for odd k when Q ≡ 3 (mod 4); it was only ever used at even k, and odd weight is handled by vanishing of odd-weight level-one forms | η^{−j} for other j. `AtkinTwisted.eigen_all`: the twisted mod-13 series is a T(Q²)-eigenform for every prime 5 ≤ Q < 500, Q ≠ 13, giving 16 congruence families (9 Atkin type 13Q³, 7 Ono type 13Q⁴), e.g. 13 ∣ p(9164597n+39275); see [ATKIN_TWISTED_ALL_Q](ATKIN_TWISTED_ALL_Q.md). Q ≥ 500 not done |
| All-prime BW sharpness | `BWSharpAll.tendsto_bEll`, determinant criterion `bEll_eq_all_of_int_dets`, `bEll_two_eq_three_iff` | G5 (ū₀ ≠ 0) at every prime ℓ ≥ 29; holds numerically for all 116 primes 29–691; 607 is not a sharpness exception |

Audit: `lake env lean scripts/audit/celebrated_targets.lean`. Details are in the linked write-ups:
[τ](TAU_SUBHECKE_BOUND.md), [Jensen](JENSEN_THRESHOLDS.md), [Dragonette](ANDREWS_DRAGONETTE.md),
[Atkin/Ono–Weaver](ATKIN_SPORADIC_CONGRUENCES.md), [BW sharpness](BW_SHARPNESS_ALL_PRIMES.md).
These proofs are machine-checked and have not been reviewed by a human expert; novelty claims are pending literature review.

## Discharged hypothesis classes (2026-11-04)

The long-standing hypothesis classes `TauMod7`, `TauMod25`, `TauMod23`, `TauMod27`, `TauMod2_8` and
`TauMatchesDiscriminant` now have global instances (`Discharge.*`, `LehmerSmall.TauModInstances`); `TauMod2_11` (Kolberg, n ≡ 1 mod 8) is proved by `KolbergTau.instTauMod2_11`; only
`DeligneBound` and `LehmerConjecture` remain hypotheses. About 40 conditional
Atkin–O'Brien variants and the uniform Stepanov bound now have unconditional corollaries. Full table:
[DISCHARGED_HYPOTHESES](DISCHARGED_HYPOTHESES.md).

## Open work

- Have an expert settle whether `Rank607Final.rEll_607` (25 generators for every m≥2)
  contradicts the rank reported by Boylan–Webb. Prove the Smith profile at 607 for m≥3
  (m=2 is proved: `Rank607Structure.lamEquiv`).
  An independent exact-integer replay gives 24 generators modulo 607. The infinite-series reconstruction bound is now proved in
  [EnvelopePrecision](../RamanujanTau/FiniteArithmetic/EnvelopePrecision.lean):
  102 coefficients determine each relevant series modulo 607². The new
  [RankGrowth](../RamanujanTau/BLBound/RankGrowth.lean) proves monotonicity and
  propagation of attainment of the FKO bound for actual partition modules.
  [DeterminantRank](../RamanujanTau/FiniteArithmetic/DeterminantRank.lean)
  reduces all higher ranks to one explicit actual coefficient determinant.
  The saved numerical matrix now has a kernel-checked nonzero determinant in
  [Rank607Witness](../RamanujanTau/FiniteArithmetic/Rank607Witness.lean);
  [PrecisionSquare](../RamanujanTau/FiniteArithmetic/PrecisionSquare.lean)
  identifies the full Hasse denominator modulo p² for every prime p≥5.
  [Rank607Final](../RamanujanTau/FiniteArithmetic/Rank607Final.lean) identifies its
  entries, giving `rEll 607 m = 25` for every m≥2. Details are recorded in
  [the research draft, §5.4](BL_SHARPNESS_PROOF.md#54-the-missing-direction-at-607-appears-at-precision-two-n-2026-11-01).
- Apply the general divided-relation prediction theorem to certified ordinary
  partition lattices. [RankLifting](../RamanujanTau/FiniteArithmetic/RankLifting.lean)
  proves the orbit-lattice identity and the exact determinant visibility
  threshold: an error `p^d` times a direction with unit replacement determinant
  becomes visible precisely at precision `d+1`. The general first-lift formula,
  spectral hypotheses, and computational controls are in the
  [research draft, §5.5](BL_SHARPNESS_PROOF.md#55-predicting-the-precision-of-rank-growth-proved-algebra-conditional-arithmetic-application-2026-11-01).
  These results do not classify all exceptional primes.
- Compute the two high-precision partition seeds efficiently. The proved evaluator
  is fast once those residues are supplied; it does not make seed acquisition free.
- Identify and certify finite representations for further primes and counting
  problems. Experimental Katz matrices require their own arithmetic identification
  and remainder bounds.
- Resolve the general sharpness and higher-precision rank questions in the
  [Boylan–Webb research draft](BL_SHARPNESS_PROOF.md). The prime-29 construction
  does not establish those claims for every prime.
- (Done; kept for the record.) Derive the prescribed bad-prime eigenvalues from the actual newform
  Atkin–Lehner class, then formalize the half-integral-weight correspondence
  and Boylan–Webb identification needed by the [Theorem A formalization](THEOREM_A.md).
  Theorem A is now unconditional (`ThetaLift.theoremA_unconditional`); its remaining
  obligation is the uniform lower bound b_ℓ(m) ≥ 2m−1.
- Independently review the mathematics and scope of the completed admissible
  sparse triple classification in the
  [multi-quintuple research record](../RESEARCH_MULTI_QUINTUPLE.md).
  The universal admissible converse is complete. Remaining directions include
  a universal four-factor classification beyond the completed cases at 41 and 53
  and the proved parameter families,
  a universal first-witness bound, and the first-spanning
  or first-perfect cutoff criteria. The separate prime-index automorphism
  argument remains a paper proof.
- Pursue the seed-survival criterion for exact stabilization: it requires
  `Theta^(dim K) u0` to be nonzero, even when Theta is singular. The generic
  finite-dimensional theorem is already proved; identifying the actual model
  and establishing the seed condition at all primes remain open.

The research documents retain historical calculations and proposed arguments.
Their labels such as “proved here” refer to paper arguments unless they identify
a Lean theorem and its discharged hypotheses. Claims of mathematical novelty
require literature and expert review independently of kernel verification.
