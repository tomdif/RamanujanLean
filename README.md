# RamanujanLean

A Lean 4 + Mathlib formalization of parts of **Ramanujan's mathematics**, in two arcs:

1. **Ramanujan's τ function** — the coefficient sequence of the modular discriminant
   `Δ(q) = q·∏(1−qⁿ)²⁴ = Σ τ(n) qⁿ`, extracted as a computable `τ : ℕ → ℤ` with its Hecke theory.
2. **q-series & partition theory** — a from-scratch formal-power-series framework (Bailey chains,
   Jacobi triple products, Durfee rectangles, the `d/dz` differentiation trick) culminating in several
   classical theorems proved **kernel-clean** (no `sorry`, no new axioms, no `native_decide`):
   Euler's pentagonal number theorem, Jacobi's cube identity, and **Ramanujan's partition congruences
   `p(5n+4) ≡ 0 (mod 5)` and `p(7n+5) ≡ 0 (mod 7)`** — bridged to Mathlib's combinatorial partition count,
   so `p(n)` really is `#{partitions of n}`.

> The Lean **package** is still named `RamanujanTau` (every module lives under `import RamanujanTau.…`);
> the repository is `RamanujanLean`.

### Results at a glance (all kernel-clean — `[propext, Classical.choice, Quot.sound]`, no `sorry`)

| Theorem | Statement |
|---|---|
| **Euler's pentagonal number theorem** | `(q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}` |
| **Jacobi's cube identity** | `(q;q)_∞³ = Σ_{m≥0} (−1)ᵐ(2m+1) q^{m(m+1)/2}` |
| **Ramanujan's congruence (mod 5)** | `5 ∣ p(5n+4)` |
| **Ramanujan's congruence (mod 7)** | `7 ∣ p(7n+5)` |
| **Partition-count bridge** | `[qⁿ] 1/(q;q)_∞ = #(Nat.Partition n)` — `p(n)` is the honest count |
| **Euler's recurrence** | `p(n) = p(n−1)+p(n−2)−p(n−5)−p(n−7)+⋯` |
| **Ramanujan's theta functions** | `φ(q)=Σq^{n²}`, `ψ(q)=Σq^{n(n+1)/2}`, `f(−q)=(q;q)_∞`, with product forms |
| **Canonical quintuple family** | For every odd `p ≥ 5`, `∏_{i=1}^{(p-1)/2}Q(qⁱ,qᵖ)` vanishes in every nonsquare class mod `p` |
| **Three quintuple products (`p=7`)** | `[q^{7n+r}] Q(q,q⁷)Q(q²,q⁷)Q(q³,q⁷) = 0` for `r=3,5,6` |
| **Root--Vanishing boundary** | Uniform short roots force vanishings; eight-coset theta/Walsh encoding isolates the exact spectral-coherence converse |

| | |
|---|---|
| Modules | 143 |
| Build | `lake build` → **3848 jobs, 0 errors** |
| `sorry` count | **0** · new `axiom` declarations | **0** |
| Headline theorems | depend only on `[propext, Classical.choice, Quot.sound]` (audited) |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` + Mathlib |

---

## Part II — q-series & partition theory (headline results)

Everything here is built from a single from-scratch engine: formal power series over `ℤ`, `ℤ[z;z⁻¹]⟦q⟧`
(the "z-outer" ring), a z-degree projection `zProj`, coefficient stabilization for infinite products, and
a `d/dz|_{z=−1}` differentiation functional. Nothing below is imported from Mathlib — the Jacobi triple
product, the pentagonal/cube identities, and the congruence are not in Mathlib.

### `MockTheta5EulerPentagonal.lean` — Euler's pentagonal number theorem
```lean
theorem euler_pentagonal : qfacInf = pentSeries
--  (q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}
```
Proved by building a **shifted base-`q³` bilateral Jacobi triple product**
`(q³;q³)_∞ · ∏(1+z q^{3i+1}) · ∏(1+z⁻¹ q^{3i−1}) = Σ_{n} zⁿ q^{(3n²−n)/2}` (`bilateral_pent_JTP`,
proved `zProj`-by-`zProj` against a Durfee-rectangle collapse), evaluating at `z = −1` (a *unit* — this is
how the `ℤ((q))` non-unit obstruction at `z = −q` is sidestepped), and reassembling the three residue-class
products mod 3 back into `(q;q)_∞`.

### `MockTheta5JacobiCubeProof.lean` — Jacobi's cube identity
```lean
theorem jacobi_cube_identity : qfacInf ^ 3 = jacobiCubeSum
--  (q;q)_∞³ = Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}
```
Proved from a **bilateral triangular Jacobi triple product** (`MockTheta5TriangularBilateral.lean`)
differentiated by the `d/dz|_{z=−1}` functional `L` (Leibniz via `Finsupp.addHom_ext`, the vanishing rule
`L((1+z)·f) = …`).

### `MockTheta5PartitionCongruence.lean` — Ramanujan's partition congruence
```lean
theorem five_dvd_coeff_partitionGF (n : ℕ) : (5 : ℤ) ∣ coeff (5*n+4) partitionGF
--  5 ∣ p(5n+4),   where p(n) = [qⁿ] 1/(q;q)_∞
```
The classical proof, fully formalized:
- **`MockTheta5Frobenius.lean`** — the char-5 Frobenius `(q;q)_∞⁵ ≡ (q⁵;q⁵)_∞ (mod 5)`, from per-factor
  freshman's dream `(1−x)⁵ = 1−x⁵` (`sub_pow_char`) lifted to the infinite product.
- **`MockTheta5Qfac4.lean`** — `(q;q)_∞⁴ = pentSeries · jacobiCubeSum`, whose coefficient at any exponent
  `≡ 4 (mod 5)` is `≡ 0 (mod 5)`: the Cauchy product feeds every `(pentagonal k, triangular m)` pair into the
  **arithmetic heart** `jacobi_weight_dvd_of_exponent` (`PartitionCongruenceMod5.lean`), which forces
  `2m+1 ≡ 0`.
- **`MockTheta5PartitionCongruence.lean`** — the capstone, via
  `Ψ₅ partitionGF = Ψ₅((q;q)_∞⁴) · expand₅(Ψ₅ partitionGF)`; the second factor is supported on multiples of
  5, so every `q^{5n+4}` term lands on a vanishing `(q;q)_∞⁴` coefficient. **No induction.**

### `MockTheta5PartitionCongruence7.lean` — Ramanujan's companion congruence
```lean
theorem seven_dvd_coeff_partitionGF (n : ℕ) : (7 : ℤ) ∣ coeff (7*n+5) partitionGF
--  7 ∣ p(7n+5)
```
The same pipeline mod 7, using `(q;q)_∞⁶ = ((q;q)_∞³)² = jacobiCubeSum²`: the Cauchy product of Jacobi's
cube series with itself feeds every triangular pair into a `ZMod 7` heart (`PartitionCongruenceMod7.lean`),
which forces `(2j+1)(2k+1) ≡ 0` at exponents `≡ 5 (mod 7)`.

### `MockTheta5PartitionCount.lean` — the partition-count bridge
```lean
theorem coeff_partitionGF_eq_card (n : ℕ) : coeff n partitionGF = (Fintype.card (Nat.Partition n) : ℤ)
theorem five_dvd_partition_card  (n : ℕ) : 5 ∣ Fintype.card (Nat.Partition (5*n+4))
theorem seven_dvd_partition_card (n : ℕ) : 7 ∣ Fintype.card (Nat.Partition (7*n+5))
```
Mathlib defines the partition generating function `Nat.Partition.genFun` combinatorially but leaves connecting
it to `1/(q;q)_∞` as a stated TODO. We close it: `HasProd (fun n ↦ 1 − X^{n+1}) (q;q)_∞` (the partial
products converge in the `X`-adic topology) meets `hasProd_genFun` factor-by-factor through the geometric
series, giving `genFun 1 · (q;q)_∞ = 1`, hence `partitionGF = genFun 1`. So `p(n) = coeff n partitionGF` **is**
the honest count of partitions of `n`, and both congruences are restated about it.

### `MockTheta5PentagonalRecurrence.lean` — Euler's recurrence for `p(n)`
```lean
theorem partition_pentagonal_recurrence (n : ℕ) (hn : 0 < n) :
    coeff n partitionGF = ∑ m ∈ Finset.range (n+1), (-1)^m *
      (p(n − (m+1)(3m+2)/2) + p(n − (m+1)(3m+4)/2))    -- terms with negative argument omitted
--  p(n) = p(n−1) + p(n−2) − p(n−5) − p(n−7) + p(n−12) + …
```
From `pentSeries · partitionGF = 1` (Euler pentagonal ⟹ the pentagonal series is the reciprocal of the
partition generating function), reading off the coefficient of `q^n`. The generalized pentagonal numbers
`(m+1)(3m+2)/2`, `(m+1)(3m+4)/2` are `k(3k−1)/2` for `k = m+1` and `k = −(m+1)`.

### `MockTheta5RamanujanTheta.lean` — Ramanujan's theta functions
Ramanujan's general theta `f(a,b) = Σ a^{n(n+1)/2}b^{n(n-1)/2} = (−a;ab)_∞(−b;ab)_∞(ab;ab)_∞` specializes
to the classical one-variable theta functions, recorded here from the square Jacobi triple product
`bilateralTheta = Σ zⁿ q^{n²}` and Euler pentagonal:
```lean
theorem ramanujan_f_neg  : pentSeries = qfacInf          --  f(−q) = (q;q)_∞
theorem phi_product      : phi    = qfac2Inf * negOddPochInf ^ 2  --  φ(q)  = Σ q^{n²} = (q²;q²)_∞(−q;q²)_∞²
theorem phiNeg_product   : phiNeg = qfac2Inf * oddPochInf ^ 2     --  φ(−q) = Σ(−1)ⁿq^{n²} = (q²;q²)_∞(q;q²)_∞²
def     psi := qfac2Inf * Ring.inverse oddPochInf        --  ψ(q) = (q²;q²)_∞/(q;q²)_∞  (Ramanujan's ψ)
theorem psi_eq_series    : psi = psiSum                  --  ψ(q) = Σ_{n≥0} q^{n(n+1)/2}   (Gauss)
```
`φ(q)` is `map ev1 bilateralTheta` (`z=1`), `φ(−q)` is `map evm1 bilateralTheta` (`z=−1`). Gauss's series form
`ψ(q) = Σ_{n≥0} q^{n(n+1)/2}` (`MockTheta5PsiSeries.lean`) comes from the `z=1` value of the triangular JTP:
`triTheta` double-covers the triangular numbers, so `map ev1 triTheta = 2·ψ` matches the product side
`2·((q;q)_∞·∏(1+qⁿ)²)`; cancelling the `2` (`PowerSeries ℤ` is a domain) and applying the distinct = odd
algebra gives `ψ = (q²;q²)_∞/(q;q²)_∞`. `MockTheta5ThetaIdentities.lean` records the theta relation
`phi_mul_phiNeg : φ(q)·φ(−q) = φ(−q²)²`.

### Multi-quintuple-product vanishing research

[`RESEARCH_MULTI_QUINTUPLE.md`](RESEARCH_MULTI_QUINTUPLE.md) records a reproducible investigation of the
2026 triple- and quadruple-quintuple-product coefficient-vanishing examples.  The exact integer scanner
`scripts/quintuple_vanishing_scan.py` reproduces all five published examples and finds the first obstruction
to the tempting condition `Σ iₛ² ≡ 0 (mod p)`: `(p;i,j,k)=(71;1,4,14)` is isotropic, but every residue class
has a nonzero coefficient already by `q⁴⁶³`.  `MultiQuintupleVanishing.lean` proves the branch-uniform
completed-square identity for arbitrary finite products, isolating the quadratic lattice that a future
sign-reversing affine involution must preserve.  `MultiQuintupleP7.lean` proves the first exact
triple theorem: the new `(p;i,j,k)=(7;1,2,3)` case vanishes in the quadratic nonresidues `3,5,6 (mod 7)`.
`MultiQuintuplePochhammer.lean` supplies the reusable formal `(qᵃ;qᵈ)∞` and the paper's five-factor
`Q(qⁱ,qᵖ)` specialization.  `MultiQuintupleCanonical.lean` proves the symbolic factorization
`∏_{i=1}^{(p-1)/2} Q(qⁱ,qᵖ) = φ(−q)(qᵖ;qᵖ)∞^((p-5)/2)(q²ᵖ;q²ᵖ)∞` for every odd `p ≥ 5`, and hence
all nonsquare residue-class vanishings (all quadratic nonresidues when `p` is prime).
This is a theorem about the actual product rather than a surrogate target.  No unproved general sparse
vanishing statement is asserted as a theorem.

The sparse-triple investigation has also produced a sharper, explicitly conjectural classification.
An isotropic triple is reflective exactly when its projective normal `(i,j,k)` appears to have an
integral lift `w` of norm `p` or `2p`.  `scripts/paley_spinor_scan.py` finds zero mismatches across 596
projective classes through `p=401`; 328 classes have such roots and are reflective/hits, while 268 have
neither.  `MultiQuintupleRootReflection.lean` proves the general forward theorem: every short projective
root produces an integral Householder reflection.  For `(p;i,j,k)=(71;1,11,34)`, the opaque matrix is
simply reflection in `w=(6,-5,-9)`, with `||w||²=2p` and `w≡6(i,j,k) (mod p)`.
`MultiQuintuplePaleySpinor.lean` also proves that the projective invariant is a Legendre elliptic
`j`-invariant and kernel-checks the residue-`61` affine branch certificate.
`MultiQuintupleRootConverse.lean` proves the converse for primitive rational Householder
reflections: the normal has norm `p` or `2p` and is a projective lift.  The coherent-cancellation
setting needed here is now handled completely downstream: rational involution classification
produces a Householder or negative Householder map, and the theta arithmetic forces its primitive
normal and branch target.  This does not classify arbitrary lattice automorphisms; the stronger
claim that every noncentral automorphism is itself a reflection is false in the order-12 `J=0`
classes, which also contain rotations.
`MultiQuintupleRootBranch.lean` proves the
universal positive and negative eight-branch matchings for every direct short root.
`MockTheta5QuintIdentity.lean` proves the full formal quintuple product identity, and
`MultiQuintupleBilateralBridge.lean` proves the exact coefficient interface
`[q^k] Q(q^i,q^p) = quintBilateralCoeff p i k` for `0<i` and `2i<p`.
`MultiQuintupleCancellation.lean` now flattens the actual three-factor coefficient into one finite
bilateral branch box and proves both positive and sign-corrected negative short-root progressions
vanish by a fixed-point-free sign-reversing involution.  It also gives a reflection-theoretic proof
of the `7n+3` triple progression.  `MultiQuintupleProjectiveCancellation.lean` then supplies a
reusable exponent-involution assembly, transports the non-direct projective root
`(6,-5,-9) ≡ 6(1,11,34) (mod 71)` through all eight affine residue cosets, and proves the actual
`71n+61` coefficient family zero.  It also instantiates the direct norm-`2p` root `(1,6,11)` to
prove the actual `79n+9` family.  `MultiQuintupleRootVanishingEquivalence.lean` now proves uniform
transport for every projective short root: the exact quotient and target-residue laws, positive
and sign-corrected negative eight-branch closure, two abstract pairing-to-coefficient bridges,
and a unified theorem making the entire predicted progression of the actual triple product zero.
It also proves that the positive and negative target congruences are necessary for projective
coordinate closure under explicit Bezout invertibility hypotheses.  The new
`MultiQuintupleRootVanishingClassification.lean` proves that a coefficient vanishes exactly when
its positive and negative finite branch supports have equal size, equivalently when an abstract
sign-reversing support bijection exists.  Persistent progression vanishing is exactly shellwise
sign balance, and the full bare Root--Vanishing biconditional is reduced to one explicitly named
rigidity proposition: every such abstract shellwise balance must arise from one coherent short-root
involution.  The unrestricted proposition is now formally disproved: `Q(q^3,q^9)^3` is supported
only on exponents divisible by three, hence vanishes throughout `9N+1`, but no projective-root
target can exist at `p=9`.  More generally, a new theorem proves this imprimitive-scale vanishing
mechanism whenever the modulus and all three indices have a common divisor not dividing the target
residue.  It now proves the stronger exact identity
`Q(q^(g*i),q^(g*p)) = Q(q^i,q^p)|_(q→q^g)`, coefficient-by-coefficient descent, and the complete
dichotomy: every scaled persistent zero is either automatically off support or descends to a
primitive persistent zero.  Conditional on the explicitly named primitive rigidity conjecture,
this becomes an end-to-end classification by automatic support or a projective root.
`MultiQuintupleLocalSupport.lean` goes beyond common scaling: for every odd divisor `d` of `p`
that divides `3i`, `3j`, and `3k`, the support lies in the eight subset-sum classes
`b1*i+b2*j+b3*k (mod d)`.  Missing any of those classes proves an entire progression zero; in
particular it formally proves the mixed family `Q(q,q^15) Q(q^3,q^15)^2` vanishes in `15N+2`.
For prime `p ≥ 5` and nonzero canonical indices this local obstruction is impossible, cleanly
isolating the corrected prime, pairwise-distinct, isotropic rigidity statement—and the corresponding
general arbitrary-automorphism classification—as the remaining open problem rather than an assumption.
`MultiQuintupleThetaCosets.lean` now gives that frontier an exact spectral form.  The eight Watson
branch choices are shifted cosets of `(6pℤ)^3`; square completion identifies coefficient degree
`K` with the common norm shell `24pK+Σ(6i_s-p)^2`, and the triple product is exactly the top-parity
Walsh projection of their eight theta components.  Full Walsh inversion recovers every component
from all eight character projections, while a separate theorem proves that the single parity
projection is not injective.  This rules out the tempting but invalid shortcut from one scalar
theta identity directly to componentwise equality.
`MultiQuintupleThetaRigidity.lean` proves that the progression shells fill the complete affine
residue fiber and formalizes the right global object: one rational orthogonal involution acting
coherently on every shell.  It proves that such an involution forces persistent cancellation and
completely classifies its rational linear part as a Householder reflection or its negative.  The
new `MultiQuintupleThetaArithmetic.lean` proves that every vector of the homogeneous index-`p`
congruence lattice is a difference of two Watson points in the same affine fiber.  Consequently
every coherent involution preserves that full lattice integrally, including the three `p e_s`
test vectors.  Its rational Householder line can always be primitively normalized over the
integers, with an explicit square-Bézout certificate, and the primitive squared norm is forced to
be one of `1`, `2`, `p`, or `2p`.  It then excludes the norm-`1` and norm-`2`
signed-coordinate/permutation stabilizers, sharpens the list to `p` or `2p`, proves that the
primitive normal is a projective lift of `(i,j,k)`, and uses one coherently transported Watson
point plus an exhaustive `ZMod 3` theorem to force the correct positive/negative branch and its
exact target congruence.  Consequently every coherent admissible theta involution now yields a
complete `ProjectiveRootTargetCertificate`; arithmetic classification is closed.  Conversely, an
explicit rational Householder or negative-Householder map, together with the universal eight-branch
matching, constructs one coherent theta involution from every such certificate.  Thus projective-root
targets and coherent involutions are exactly equivalent on admissible data.  At the proposition
level, spectral coherence is now proved logically equivalent to both theta-coset rigidity and the
corrected Root--Vanishing rigidity conjecture.  The sole remaining reverse-direction frontier is
therefore exact: obtain one fixed rational orthogonal involution from equality of the positive- and
negative-parity four-coset representation counts along the progression.
`MultiQuintupleThetaWitness.lean` gives an equivalent but operationally different route: every
admissible residue must have either a finite projective-root certificate or one finite nonzero
coefficient witnessing failure of persistent vanishing.  This root-or-witness dichotomy is proved
equivalent to spectral coherence and corrected Root--Vanishing rigidity, so a universal effective
witness bound would close the conjecture without reconstructing an isometry from an infinite theta
identity.  The reproducible `witness-scan` checks this dichotomy through `p<=1000`: across 3,172
projective classes and 2,055,986 residue problems it finds 1,356 root certificates and 2,054,630
coefficient witnesses, with no unresolved residue or root/nonzero conflict; the latest first witness
occurs at progression index 203.
The exact `root-scan` command independently reconstructs the selected sign, predicted residue,
root reflection, and affine certificate.  The stronger census through `p<=1000` covers 3,172
projective classes with no automorphism/root or root/certificate mismatches; all 88 extra residues
that were merely silent through depth 160 acquire a nonzero witness by depth 256.

### Supporting q-series infrastructure
Bailey pairs & the Bailey chain / transform (`MockTheta5Bailey*`), the classical and bilateral Jacobi
triple products (`MockTheta5JacobiTriple` / `…Bilateral` / `…ClassicalJTP`), Durfee-rectangle identities
(`MockTheta5Durfee*`), Cauchy/Euler sum=product identities, even/odd and distinct=odd partition theorems,
Gauss/alternating theta evaluations, and fifth-order mock-theta scoping (`MockTheta5R1`).

---

## Part I — Ramanujan's τ function

A computable `τ : ℕ → ℤ` (Mathlib has `ModularForm.discriminant : ℍ → ℂ` but does not extract the integer
coefficient function) via a small computable `List ℤ` polynomial representation:

```lean
def tau (n : ℕ) : ℤ :=
  let p   := eulerProductTrunc n n   -- ∏_{k=1}^{n} (1 − X^k), truncated to deg n
  let p24 := truncPowList n p 24      -- (·)^24, truncated
  coeffList (shiftList 1 p24) n       -- [X · (·)^24].coeff n
```

- **`Basic` / `SmallValues`** — the `τ` function, `τ(0)=0`, `τ(1)=1`, and exact values `τ(2..12)` by
  `native_decide`.
- **`HeckeTheory`** — a single master hypothesis class `TauHeckeMaster` (the `T_p`-action on the weight-12
  eigenform) from which both multiplicativity `TauMultiplicative` and the recurrence `TauHeckeRecurrence`
  are *derived as instances*.
- **`EulerFactor`** — under `TauHeckeRecurrence`, the local Euler factor
  `(1 − τ(p)X + p¹¹X²)·Σ τ(pʳ)Xʳ = 1`, `τ(p²)=τ(p)²−p¹¹`, and `τ(n)=∏ τ(p^k)`.
- **`Gegenbauer`** — the general closed form `τ(pʳ) = G_r(τ(p), p¹¹)` (Chebyshev-U family) plus the explicit
  binomial sum, subsuming `HeckePowers` (`τ(p⁴)…τ(p⁷)`).
- **`Deligne` / `Lehmer` / `Congruences`** — Deligne's bound `|τ(p)| ≤ 2p^{11/2}`, Lehmer's non-vanishing,
  and the mod-691 congruence, each certified on a finite range and exposed as a named hypothesis class for
  the universal statement.

Deep theorems are exposed as named typeclasses (`TauHeckeMaster`, `DeligneBound`, `LehmerConjecture`,
`TauMod691`), never asserted as `axiom`s — the same discipline as
[PlonkLean](https://github.com/tomdif/PlonkLean). The honest status of each:
`TauHeckeMaster` reduces (`HeckeOperator.HeckeData`) to constructing Hecke operators `T_p` on `CuspForm₁₂`
— the one piece genuinely absent from Mathlib; `DeligneBound` *is* Deligne's proof of the Weil conjectures
(out of reach); `LehmerConjecture` is open.

- **`DiscriminantBridge`** — connects Mathlib's analytic discriminant `Δ = η²⁴` to its q-expansion:
  `coeff 0 = 0` (`Δ` is a cusp form) and `coeff 1 = 1` (`τ(1) = 1`), the latter by identifying `Δ`'s cusp
  function `q ↦ q·∏'(1−qⁿ⁺¹)²⁴` on the unit disc and differentiating at `0`.

- **`Mod691`** — the modular-forms proof of Ramanujan's `τ(n) ≡ σ₁₁(n) (mod 691)`, carried to its arithmetic
  heart. `B₁₂ = −691/2730`; the `E₁₂` q-expansion `(65520/691)·σ₁₁` (the 691-carrier); the `E₄³` coefficients;
  and now **the full weight-12 relation** `E₄³ = E₁₂ + (432000/691)·Δ` (via `exists_smul_discriminant`, with
  the scalar pinned by `coeff 1 = 1`), giving `691·[qⁿ]E₄³ = 65520·σ₁₁(n) + 432000·τ(n)` for `n ≥ 1`
  (`tau_mod_relation`). The same machinery proves the **discriminant identity** `E₄³ − E₆² = 1728·Δ`
  (`qExpansion_E4cube_sub_E6sq`), i.e. `1728·τ(n) = [qⁿ]E₄³ − [qⁿ]E₆²` for every `n` (`tau_smul_eq_coeff`),
  and — **unconditionally** — the congruence `τ(n) ≡ σ₁₁(n) (mod 691)` in `ZMod 691`
  (`tau_congruence_mod691_unconditional`). Integrality `τ(n) ∈ ℤ` (`tau_int`) is *proved*: `E₄`, `E₆` are images
  of explicit integer series, so `1728·τ(n) = [qⁿ](p₄³−p₆²)`, and `key_dvd` proves `1728 ∣ [qⁿ](p₄³−p₆²)` via
  `12 ∣ 5σ₃(n)+7σ₅(n)` — the classical integrality of `Δ = (E₄³−E₆²)/1728`. No hypotheses, no axioms.
  In Ramanujan's iconic form: `τ(p) ≡ 1 + p¹¹ (mod 691)` for primes (`tau_prime_congruence_mod691`).
  See `OPEN_QUESTIONS.md`.

---

## Build

```sh
lake build
```

A Mathlib cache hit brings this down to seconds of project code on top of Mathlib.

## License

MIT.

## References

- Ramanujan, S. (1916). "On certain arithmetical functions." *Trans. Cambridge Philos. Soc.* **22**.
- Ramanujan, S. (1919). "Some properties of p(n), the number of partitions of n." *Proc. Cambridge Philos. Soc.* **19** — the congruence `p(5n+4)≡0 (mod 5)`.
- Euler, L. — the pentagonal number theorem. · Jacobi, C. G. J. (1829). *Fundamenta Nova* — the triple product and cube identity.
- Andrews, G. E. *The Theory of Partitions* — Bailey chains, Durfee squares, the Jacobi triple product.
- Deligne, P. (1974). `|τ(p)| ≤ 2p^{11/2}` (Weil conjectures). · Lehmer, D. H. (1947), *Duke Math. J.* **14**.
- Apostol, T. M. *Modular Functions and Dirichlet Series in Number Theory*.
- OEIS [A000594](https://oeis.org/A000594) (τ), [A000041](https://oeis.org/A000041) (p(n)).
