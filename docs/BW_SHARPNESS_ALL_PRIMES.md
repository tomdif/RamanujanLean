# Boylan–Webb sharpness b_ℓ(m) = 2m − 1 at every prime ℓ ≥ 29: what is proved, what is reduced, where it breaks (2026-11-03)

Lean: `RamanujanTau/BWSharpAll/`. Scripts: `scripts/bwsharpall/`.

**Outcome.** No uniform proof of sharpness was found. The uniform argument stops at one
non-vanishing statement (G5), and §3 explains why the available mod-ℓ tools cannot settle it.
This pass adds four things:

* new uniform, unconditional Lean theorems: b_ℓ(m) → ∞ for every prime ℓ ≥ 13, and a
  single-determinant criterion for b_ℓ(m) = 2m − 1;
* an exact Lean restatement of the first open step b_ℓ(2) = 3 as the absence of one explicit
  partition congruence modulo ℓ²;
* a classical formula for the seed (numerically confirmed): it comes from T_ℓ(Δ^δ);
* a numerical scan showing that seed survival holds at every prime 29 ≤ ℓ ≤ 691, with 607
  included.

Evidence labels: **[L]** Lean, axiom-clean (propext, Classical.choice, Quot.sound). **[L-cond]**
Lean, conditional on named hypotheses. **[P]** paper argument only. **[N]** numerical evidence
only.

---

## 1. What the lower bound needs at a general prime

Notation is that of [BL_SHARPNESS_PROOF](BL_SHARPNESS_PROOF.md). L(1) = U(Φ), X = D∘U, and
L(1) = y + z, where y is the unit-root part (rank R = ⌊(ℓ+12)/24⌋, by Theorem A) and z is the
part of positive slope. Write K̄ = ker D̄ ⊂ S_{ℓ−1}(𝔽_ℓ). It has dimension s = ⌊d/2⌋ = ⌊(ℓ²−1)/(24ℓ)⌋;
the formula was checked at every prime in the scan. The chain of reductions:

1. **[L]** b_ℓ(m) ≤ 2m − 1 (`BLBound.bEll_le`, Theorem A).
2. **[P]** b_ℓ(m) = 2m − 1 for all m ⟺ v(X^k z) = k+1 for all k ⟺ ū_k ≠ 0 for all k
   (§4.0–4.2 of the draft). Here ū_{k+1} = Θū_k, with Θ the second-order operator on K̄ and
   ū₀ = ρ(Uz/ℓ) ∈ K̄.

   For BW's literal invariant (odd chain only), the first steps are pinned as follows [P]:
   b_ℓ(3) = 5 ⟹ ū₀ ≠ 0 ⟹ b_ℓ(2) = 3. If u₀ ≡ 0 (mod ℓ), then Xz = D(u₀) ∈ ℓ³-lattice by the
   §4.1 step, so v(Xz) ≥ 3.
3. **[L, linear algebra]** All iterates survive ⟺ Θ^s ū₀ ≠ 0 (`FiniteArithmetic.orbit_nonzero_iff`).
   Invertibility of Θ is not needed.
4. **[P, §4.11, no expert review]** Θ is invertible unless ℓ ∣ a_ℓ(6.8.a.a). Through the lift
   Sh_t and Claim K, K̄ ≅ {z ∈ M̄_{ℓ−5}(Γ₀(6)) : U₂z = z/8, U₃z = z/27}, which is the newform class
   w₂ = −(2/ℓ), w₃ = −(3/ℓ). Under this identification Θ corresponds to (ε/5)·Ū with ε = (12/ℓ).
   The condition ℓ ∣ a_ℓ(h₈) is not met by any ℓ < 2·10⁶.

**G5, the seed condition, in classical terms.**

* **[P]** G5 says that the ℓ-adic Riesz projection of L(1) onto the slope-1 part of X has the
  minimal valuation 1. Equivalently, the non-ordinary part of L(1) is nonzero modulo ℓ².
* **[P, elementary] Seed formula, part 1.** L(1) = (q^ℓ;q^ℓ)_∞ Σ p(ℓn−δ)qⁿ. Also
  (q;q)^{ℓ²} ≡ (q^ℓ;q^ℓ)^ℓ (mod ℓ²). Together these give the exact congruence

  L(1) ≡ W · U(Δ^δ) ≡ W · T_ℓ(Δ^δ) (mod ℓ²), with W = η(ℓz)/η(z)^ℓ and Δ^δ ∈ S_{(ℓ²−1)/2}(SL₂ℤ).

  The second step uses U = T_ℓ − ℓ^{k−1}V in weight k = (ℓ²−1)/2.
* **[N, with a proof sketch] Seed formula, part 2.** η(z)^{2ℓ}/η(ℓz)² ≡ E_{ℓ−1}^{ℓ+1} (mod ℓ²).
  This was checked on 3000 coefficients at ℓ = 13, 17, 29, 37, 53, 61. Sketch: the logarithmic
  θ-derivatives of both sides are (ℓ/12)(E₂ − VE₂) mod ℓ², using θe₁ ≡ (E₂ − VE₂)/12. That
  leaves only an ℓ-th-power ambiguity in (F − G)/ℓ mod ℓ, which a filtration argument should
  remove. That argument has not been written out.

  Hence L(1) ≡ E_{ℓ−1}^{−(ℓ+1)/2} · T_ℓ(Δ^δ) (mod ℓ²). The seed of L(1) is the seed of the
  weight-0 avatar of the classical level-1 cusp form T_ℓ(Δ^δ). The Katz model confirms this
  directly: the seeds agree, coordinate by coordinate, at all 13 primes 29–113 tested
  (`seed_decomp_test.py`, `seed_decomp_test.log`).
* **[L] First step as a partition non-congruence** (`BWSharpAll.bEll_two_eq_three_iff`). For every
  prime ℓ ≥ 13, b_ℓ(2) = 3 holds iff there is *no* finitely supported c : ℕ → ℤ/ℓ² with

  p(ℓn − (ℓ²−1)/24) ≡ Σᵢ cᵢ · p(ℓ^{2i+3}n − (ℓ^{2i+4}−1)/24) (mod ℓ²) for all n ≥ 0

  (with p(x) = 0 for x < 0). This is the mod-ℓ² analogue of the Ahlgren–Boylan theorem that
  p(ℓn+β) ≡ 0 (mod ℓ) has no solutions for ℓ ≥ 13. Instances [L]:
  `no_first_step_congruence_607` and `no_first_step_congruence_29`, from the existing
  `bEll_607_two` and `bEll_29`.

## 2. Is 607 an exception to sharpness?

**No, as far as anything checked shows. The rank anomaly at 607 and sharpness concern different
parts of L(1).**

* The rank question concerns the unit-root part y. It asks whether L̄(1) is a cyclic vector for
  X̄|_V. At 607 it is not: the Krylov rank is 24 = R − 1, reproduced by this scan.
* Sharpness concerns the slope-positive part z, through ū₀ ∈ K̄. At 607 the finite Katz model
  gives the following. These are [N] here; the finite-model survival is [L] in
  `SeedModels`, but its identification with the actual operator is not proved.
  * s = 25;
  * Θ has full rank 25;
  * ū₀ ≠ 0, and Θ^{25}ū₀ ≠ 0;
  * Katz cutoffs N = 3 and N = 4 agree.
* Proved on actual partition data: b₆₀₇(2) = 3 (`Rank607Threshold.bEll_607_two`) [L]. Equivalently
  [L], there is no first-step congruence at 607.
* Structural difference [P/heuristic]:
  * **Cyclicity needs every primary component** of L̄(1) to be nonzero. For a random seed it
    fails with probability ≍ 1/ℓ, so infinitely many rank exceptions are expected, 607 being
    the first.
  * **Seed survival needs only some component** in the invertible Fitting summand of Θ. It fails
    with probability ≍ ℓ^{−s}, where s ≈ ℓ/24.
  * The same order holds on the Θ-singular route, which needs ℓ ∣ a_ℓ(h₈) (≍ 1/ℓ) and a further
    codimension-(s−1) coincidence.
  * The expected number of counterexamples beyond the scanned range is therefore astronomically
    small. The only primes where the heuristic failure probability is not negligible are
    29 ≤ ℓ ≤ 47 (s = 1), and those are proved in Lean.
* **Caveat.** The determinant criterion of §4.1 is lossy at rank-deficient primes such as 607.
  There the unit-root (R+1)-minor already carries an extra factor of ℓ. That is a limitation of
  the certificate, not evidence against sharpness.

## 3. Why the uniform argument breaks, stated precisely

1. **G5 is not a mod-ℓ statement about L̄(1)** [P, given §4.0–4.2]. On lattice vectors f with
   f̄ ∈ V, the seed map is affine in f mod ℓ². Its change under f ↦ f + ℓg is Ū(π_{ker X̄} ḡ),
   and this is onto K̄ = Ū(ker X̄), because X̄ is semisimple at 0 by Theorem A. So no property of
   L̄(1) decides G5: not its filtration, its theta cycle, or Hasse-invariant divisibility.

   The tools that proved Ahlgren–Boylan and Theorem A (Kiming–Olsson/Jochnowitz theta cycles,
   filtrations, the unit-coefficient T_ℓ argument) act on L̄(1). They would have to be applied to
   the specific mod-ℓ² object E^{−(ℓ+1)/2}T_ℓ(Δ^δ) together with the mod-ℓ² dynamics of X. No
   such mod-ℓ² theta-cycle theory is available.
2. **The components of ū₀ are expected to be L-values.**
   * In the identification of §1 item 4, ū₀ is a vector in the weight-(ℓ−5), level-6 newform
     class. Its coordinates along Hecke eigenforms are projections of the explicit form above.
   * The coordinates are expected to be Waldspurger/Kohnen-type twisted central L-values, or
     Rankin–Selberg values. This is [heuristic]; it is not derived here.
   * No uniform mod-ℓ non-vanishing is known for these values.
   * What is needed is only that the *vector* is nonzero (some coordinate), but no
     single-coefficient formula for ū₀ was found. Earlier tests in §4.12 of the draft also found
     no θʲ-twist of L(1) or L(2) that reproduces ū₀.
3. **The remaining uniform gaps**, named:
   * G5 itself, now known to be equivalent to a statement about E^{−(ℓ+1)/2}T_ℓ(Δ^δ) mod ℓ²;
   * ordinarity of h₈ = 6.8.a.a at every ℓ (an open Lang–Trotter-type question; the weak seed
     route avoids it only if the seed has a component in the invertible part);
   * Claim K of §4.11 (log-Cartier on X₀(6)) and the coordinates dictionary, neither in Lean;
   * W ≡ E^{−(ℓ+1)/2} mod ℓ² as a written proof (numerics only).

## 4. New Lean results ([L], all axiom-clean; files compiled individually with `lake build`)

### 4.1 `BWSharpAll/DetCriterion.lean`: uniform determinant criterion
For every prime ℓ ≥ 13. Let R = (ℓ+12)/24.

* `lt_bEll_of_det`: for every m ≥ 1 and k, offsets c : Fin (R+1) → ℕ and rows, if
  `det (coeff (rows i) (redm ℓ m (L ℓ (2(k + c j)+1)))) ≠ 0` in ℤ/ℓ^m, then
  `2k+1 < bEll ℓ m`.

  The proof combines `rank_Lam_le` (at most R generators of the stable module),
  `card_le_of_coeff_det_ne_zero`, and the propagation `Lam_eq_of_mem_bSet` / `Lam_eq_of_eq`.
* `lt_bEll_of_int_det`, and `bEll_eq_of_int_det` (m ≥ 2): if ℓ^m does not divide one integer
  (R+1)-minor of the actual series L(2m−3+2c_j), then **bEll ℓ m = 2m − 1**.
* `bEll_eq_all_of_int_dets`: if such a minor exists for every m ≥ 2, then bEll ℓ m = 2m − 1 for
  every m ≥ 1.

This reduces sharpness at each (ℓ, m) to the ℓ-adic valuation of one integer determinant, with
no Θ, no seed, no recurrence and no Katz model. Expected tightness [heuristic, cyclic primes]: the
minimal valuation of the minors at tail k equals v(X^k z), so sharpness corresponds to valuation
exactly k+1.

### 4.2 `BWSharpAll/Unbounded.lean`: b_ℓ(m) → ∞ for every prime ℓ ≥ 13
* `L_linIndep`: L(2k+1), L(2k+3), … are ℚ-linearly independent. The proof:
  * `L_eq_partition` writes L(2b+1) as a unit times P(2b+1) = Σ p(ℓ^{2b+1}n − e)qⁿ;
  * a rational relation would contradict growth of its top term;
  * that growth is `Growth.ratio_tendsto_atTop`, p(αn)/p(βn) → ∞ for 1 ≤ β < α, derived from the
    repository's `HardyRamanujan.hardy_ramanujan_isEquivalent`;
  * the helpers are `card_partition_mono` and `card_partition_pos`.
* `RowsDet.exists_rows_det_ne_zero`: n linearly independent power series over a field have a
  nonzero n×n coefficient minor.
* `lt_bEll_eventually : ∀ k, ∃ m₀, ∀ m ≥ m₀, 2k+1 < bEll ℓ m`, and
  **`tendsto_bEll : Tendsto (bEll ℓ) atTop atTop`**.

This is unconditional and uniform in ℓ. It is the only uniform lower-bound statement obtained,
and it is qualitative. A rate such as b ≳ 2 log_ℓ m would need a bound on the rows that is
uniform in k, which is not available. Novelty is unchecked; it is probably folklore-level.

### 4.3 `BWSharpAll/FirstStep.lean`, `Instances.lean`: the first step as a partition non-congruence
* `bEll_two_eq_three_iff_not_mem`: b_ℓ(2) = 3 ⟺ L(1) ∉ Λ^odd(3,2).
* `bEll_two_eq_three_iff`: the congruence form stated in §1.
* `no_first_step_congruence_607` and `no_first_step_congruence_29`.

### 4.4 `BWSharpAll/SeedSurvivalR.lean`: the per-prime route needs only seed survival
* `RankR.Data2.bEll_eq_of_survival` is the theorem `RankR.Data2.bEll_eq` with the hypotheses
  (θi, hθi, hinit), a left inverse of θ plus a nonzero seed, replaced by the single
  **`((Matrix.of D.θ)^s).mulVec (D.init k zL2) ≠ 0`**.
* `survival_of_left_inverse` shows that the old hypotheses imply the new one.

Per-prime certificates at a prime where Θ is singular but the seed survives therefore still
yield b_ℓ(m) = 2m − 1 for all m.

## 5. Numerical scan ([N], `scripts/bwsharpall/seed_scan_all.py`, results in `seed_scan_N3.json`)
The scan uses the same algorithm as `scripts/frontier/pattern/seed_survival_scan.py`, with the
truncated Katz model at precision ℓ² and cutoff N = 3. Earlier work found that N = 3 and N = 4
agree at 233, 257, 307, 401 and 607. Results for **every prime 29 ≤ ℓ ≤ 691** (all 116 primes):

| check | result |
|---|---|
| seed ū₀ ≠ 0 | all |
| Θ^s ū₀ ≠ 0 (survival) | all |
| Θ invertible | all (no singular Θ found) |
| unit-root rank of X̄ = R | all |
| s = ⌊(ℓ²−1)/(24ℓ)⌋ | all |
| Krylov rank of L̄(1) < R (precision-one rank deficit) | only ℓ = 607 (24 vs 25) |

The scan was stopped at 691 for time; it is about 50 s per prime there and grows like ℓ³. It
extends the previous coverage (29–257 complete, plus 307, 401, 607) to a complete range up to
691. No counterexample was found. This is a finite-model computation: the arithmetic
identification of the Katz model with the actual operator is not proved here.

## 6. What it would take to finish
* **Uniform G5.** One of the following, all open:
  * a mod-ℓ² theta-cycle or filtration theory for the specific form E^{−(ℓ+1)/2}T_ℓ(Δ^δ) under X;
  * an explicit formula for ū₀, for example a single coefficient, that is provably a unit;
  * a uniform non-vanishing theorem for the twisted L-values that ū₀ is expected to encode.

  None of these is in sight.
* **Weaker uniform targets reachable with the present tools.**
  * A quantitative version of `tendsto_bEll`.
  * Formalizing the seed formula of §1: part 1 is elementary from `L_eq_partition`; part 2 needs
    the filtration step.
  * Wiring §4.11 (Claim K) into Lean, which would make G4 conditional only on ℓ ∤ a_ℓ(h₈).
* **Per-prime extension.** The determinant criterion and the survival variant lower the
  certificate requirements. The bottleneck remains producing actual partition residues mod ℓ²
  at large ℓ in the kernel.

**Literature checked.**
* Boylan–Webb (Trans. AMS 365, 2013), through the repository's notes and a search: they
  conjecture and numerically observe b = 2m−1 generically but prove no lower bound.
* Folsom–Kent–Ono.
* Bruinier–Folsom–Kent–Ono exposition: says "one can generically take b_ℓ(m) = 2m−1", with no
  lower bound.
* Ahlgren–Boylan (mod-ℓ analogue).

No uniform lower bound for b_ℓ(m) was found in the literature.
