# Multi-quintuple-product coefficient vanishings

## Status

This track contains a formally proved infinite family and the complete Lean
classification of admissible sparse triple vanishings.
[`admissible_root_vanishing_equivalence`](RamanujanTau/MultiQuintupleFullConverse.lean)
proves the equivalence between persistent vanishing of the actual product
coefficients and an exact projective root certificate, under
`AdmissibleSparseTriple p i j k` and `R < p`.
See the [verification record](docs/verification/full_converse_lean.json).
Earlier frontier notes below are retained as historical research steps.
The exact coefficient scanner in `scripts/quintuple_vanishing_scan.py` reproduces all five
examples reported in the March and June 2026 papers and tests proposed extensions.

## Current theorem

For natural numbers p,i,j,k,R satisfying

```text
p prime, p ≠ 3, 0 < i < j < k, 2k < p,
p divides i²+j²+k², and R < p,
```

[`admissible_root_vanishing_equivalence`](RamanujanTau/MultiQuintupleFullConverse.lean)
proves

```text
HasProjectiveRootTarget p i j k R ↔ PersistentTripleVanishing p i j k R.
```

In plain language: every coefficient in the progression pN+R vanishes exactly
when a short integer vector satisfies the root and residue equations. The
criterion predicts an entire infinite progression from a finite arithmetic
certificate. The theorem concerns the actual infinite products
`Q(qⁱ,qᵖ) Q(qʲ,qᵖ) Q(qᵏ,qᵖ)`, and its only assumptions are the displayed
admissibility and residue conditions.

Writing v=(i,j,k), the certificate consists of integers e,c,λ,u and w∈ℤ³
with e∈{1,2}, ce=2, w≡λv modulo p, w·w=ep, v·w=pu, and

```text
2λR ≡ sum(w) − 6u                         (mod p), if ep ≡ 1 (mod 3),
cλ(2λR − sum(w) + 6u) ≡ 12                (mod p), if ep ≡ 2 (mod 3).
```

The target condition is essential: a short root alone does not specify the
vanishing residue. The three public interfaces are
`admissible_root_vanishing_converse`, `admissible_root_vanishing_equivalence`,
and `admissibleRootVanishingRigidity_proved`.

The published proof snapshot passed a **9,336-job full build** and a
**251-declaration multi-quintuple axiom audit**. All audited dependencies are
among `propext`, `Classical.choice`, and `Quot.sound`. The
[verification record](docs/verification/full_converse_lean.json) distinguishes
this published snapshot from the larger development worktree.

* [Result catalog and Lean example](docs/RESULTS.md#multi-quintuple-products-complete-admissible-triple-classification)
* [Completed proof outline](#complete-lean-converse-2026-11-01)
* [Certificate reproduction and audit commands](docs/FINITE_ARITHMETIC.md#multi-quintuple-classification-certificates)
* [Scope and follow-up questions](#scope-and-follow-up-questions)

## Canonical infinite family

For every odd integer `p = 2m+1 >= 5`, collecting the five Pochhammer factors proves

```text
prod_{i=1}^m Q(q^i,q^p)
  = phi(-q) (q^p;q^p)_inf^(m-2) (q^(2p);q^(2p))_inf.
```

The tail is supported on multiples of `p`, while `phi(-q)` is supported on square exponents.
It follows that every coefficient in every nonsquare residue class modulo `p` vanishes.  For
prime `p`, these are exactly all quadratic nonresidues, so this gives `(p-1)/2` infinite zero
progressions at once.  `RamanujanTau.MultiQuintupleCanonical` proves the factorization and the
coefficient theorem for symbolic `p`; this is not a finite computation or a list of fixed cases.

Check sample expansions against the theorem with, for example:

```bash
python3 scripts/quintuple_vanishing_scan.py canonical --prime 31 --depth 80
```

The investigation below concerns *sparse* products with only three or four
factors. The admissible three-factor case is now classified by the theorem
above. Four-factor products remain outside that classification.

## Historical development: reflective lattices and the converse

The sections below preserve the route from experiments to the completed
converse. Conditional reductions describe intermediate results; later sections
supply their missing inputs. The first-witness and particular shell-cutoff
conjectures remain separate questions. The arbitrary-automorphism equivalence
is still a paper argument, whereas the root–coefficient equivalence is proved
in Lean.

For a distinct isotropic triple `(i,j,k)`, define the index-`p` ternary lattice

```text
L_(p;i,j,k) = {(x,y,c1*x+c2*y+p*z) : x,y,z in Z},
c1 = -i/k (mod p),  c2 = -j/k (mod p),
```

with the ordinary sum-of-three-squares norm.  Solving a target residue condition in the
three bilateral quintuple sums produces this homogeneous lattice, together with eight
inhomogeneous cosets indexed by the bilateral branch choices.

The investigation began with the following conjecture:

> **Reflective-lattice conjecture.** A distinct isotropic triple product has an identically
> vanishing residue class if and only if `Aut(L_(p;i,j,k))` is larger than its unavoidable
> central subgroup `{+I,-I}`.  In the reflective case, every zero progression is explained by
> affine integral isometries that perfectly match the four even-parity branches with the four
> odd-parity branches.

This separates the old counterexamples for the right structural reason:

```text
p=71, (1,11,34): |Aut(L)|=4, zero residue 61, exact affine certificate
p=71, (1, 4,14): |Aut(L)|=2, no zero residue (every residue has a finite witness)
p=79, (1, 6,11): |Aut(L)|=4, zero residue 9,  exact affine certificate
p=79, (1, 9,32): |Aut(L)|=2, no zero residue
```

The exact scanner `scripts/paley_spinor_scan.py` exhausts the lattice automorphism group by
enumerating every lattice vector having the three required column norms and checking all Gram
pairings.  It uses rational/integer arithmetic to solve and verify every affine branch map.
The strengthened scan separates theorem-predicted residues from finite-depth
silence and rechecks every extra silent residue at a larger depth.  Through
every prime `p <= 1000`:

```text
projective J-classes checked                            3172
automorphism / short-root mismatches                       0
reflective / root-predicted-hit mismatches                  0
predicted residues missing by depth 160                    0
predicted residues lacking affine certificates             0
extra finite-silent residues at depth 160                  88
extras with a nonzero witness by depth 256                 88
unresolved finite-depth extras                              0
```

The coefficient comparison is finite evidence for the universal biconditional; finite silence is
never labeled a vanishing.  The affine certificates on the hit side are exact polynomial
identities, not numerical evidence.  A separate all-triples scan through `p <= 127`
(2,587 distinct canonical isotropic triples) also found that the hit/miss label is constant on
every projective class.

### Sharpening: reflectivity is a short-lift problem

The automorphism data has an unexpectedly elementary description.  Write
`v=(i,j,k)` for the projective normal defining the congruence lattice.  Every reflective
class in the census, and no nonreflective class, has a centered integral lift

```text
w congruent lambda*v (mod p),       ||w||^2 = p or 2p.
```

For a lattice point `x`, projective congruence gives `p | x dot w`.  If
`||w||^2=e*p`, with `(e,c)=(1,2)` or `(2,1)`, then

```text
R_w(x) = x - c*(x dot w/p)*w
```

is integral, preserves the norm, preserves the congruence lattice, and squares to the identity.
`RamanujanTau.MultiQuintupleRootReflection` proves this construction for arbitrary integral
parameters, without division and without assuming that `p` is prime.  Thus the implication

```text
short projective root  ==>  noncentral integral reflection
```

is now a formal theorem.  `RamanujanTau.MultiQuintupleRootConverse` proves the arithmetic
converse for a primitive rational Householder reflection: integrality on the three vectors
`p*e_i` forces the primitive normal norm to divide `2p`, hence (outside the coordinate cases)
to equal `p` or `2p`, and preservation of the congruence kernel forces the normal to be a
projective lift.  The extra classification step was previously conjectural: every noncentral
automorphism group should contain such a primitive rational reflection. The 2026-11-01 paper
argument below addresses this step; it has not been formalized or independently reviewed.
The exact `converse-scan` command checks the stronger set-level statement through `p <= 401`: all
328 noncentral classes contain a plane reflection, and the distinct plane-reflection matrices
agree exactly with the Householder matrices obtained from the short roots.  The superficially
stronger statement that every noncentral automorphism is a reflection is false for the order-twelve
`J=0` groups, which also contain rotations; the Root--Vanishing argument needs existence, not that
incorrect elementwise classification.

The exact `p <= 401` census splits as follows:

```text
reflective classes with a short root                     328
nonreflective classes without a short root                268
automorphism / short-root mismatches                        0
reflective / observed-vanishing mismatches                  0
```

Ordinary reflective classes have exactly two roots, `w` and `-w`, and automorphism group
of order four.  The special `J=0` classes have six roots and automorphism group of order twelve.
This is much more concrete than classifying determinant-`p^2` forms from `J`: it turns the
problem into representation of `p` or `2p` by a prescribed projective residue class.

For the new `p=71` hit, the whole matrix is explained by

```text
v = (1,11,34),       w = (6,-5,-9),
w congruent 6*v (mod 71),       ||w||^2 = 142 = 2*71.
```

The reflection is `x -> x-(x dot w/71)w`.  Written in the scanner's lattice basis, it is
exactly the previously discovered matrix.  `RamanujanTau.MultiQuintuplePaleySpinor` now
kernel-checks this root description and its equality with all three rows of that matrix.

Run the census or print the new `p=71` certificate with:

```bash
python3 scripts/paley_spinor_scan.py scan --max-prime 1000 --depth 160 --confirmation-depth 256
python3 scripts/paley_spinor_scan.py root-scan --max-prime 127 --depth 120
python3 scripts/paley_spinor_scan.py converse-scan --max-prime 401
python3 scripts/paley_spinor_scan.py candidate \
  --prime 71 --indices 1,11,34 --depth 500 --all-residues
```

### A prime-index symmetry theorem [paper argument, 2026-11-01]

**Theorem proposed for formalization.** Let `p >= 5` be prime, let
`v in F_p^3` be isotropic, with every coordinate nonzero and no two coordinates
equal up to sign, and put `L = {x in Z^3 : v dot x = 0 mod p}`. Then the
following are equivalent:

1. `Aut(L)` contains an element other than `I` and `-I`.
2. `Aut(L)` contains a plane reflection.
3. There is an integral vector `w`, projectively congruent to `v mod p`, with
   `w dot w = p` or `2p`.

Here `Aut` means isometries for the usual Euclidean norm. The hypotheses hold
for the prime, distinct, canonical isotropic triples in this research track.
The new part of the argument is `1 => 2`, including the order-three case.
The full statement below is a paper proof, not a new Lean theorem or a claim
of mathematical novelty.

**Lemma 1: the skew part is integral.** If `Q in Aut(L)`, then `pQ` and
`Q-Q^t` have integer entries. Indeed, `pZ^3` is contained in L, so `pQ` is
integral. Modulo p, every row of `pQ` annihilates the plane `v^perp`, hence
`pQ = u v^t mod p`. The same holds for `Q^t=Q^(-1)`, because it too preserves
L. Thus every column is also proportional to v, forcing
`pQ = c v v^t mod p`. This matrix is symmetric, so `Q-Q^t` is integral.
This lemma needs only the index-p congruence description, not isotropy.

**Lemma 2: only the threefold case needs a new reflection.** Given a
noncentral Q, replace it by `R=(det Q)Q`. This is a nonidentity proper
rotation preserving L. Its trace is an integer, since it is similar to an
integer matrix in a lattice basis. A proper three-dimensional rotation has
trace `1+2 cos(theta)`, so its nonidentity possibilities have orders
`2,3,4,6`. For an even order n, `-R^(n/2)` is already a plane reflection
preserving L.

**Lemma 3: an order-three rotation must be a signed coordinate cycle.**
Suppose R has order three. Write `C=R-R^t=[a]_cross`, where `[a]_cross`
is the skew matrix for cross product with a. Lemma 1 gives `a in Z^3`.
Since `R^2=R^t` and `trace R=0`, `trace(C^t C)=6`; hence `a dot a=3`.
All three entries of a are therefore `+1` or `-1`. Moreover,

`R = (a a^t - I + [a]_cross)/2`.

This has integer entries and is orthogonal, so it is a signed permutation
matrix. Conjugating by `diag(a)` turns it into an ordinary three-cycle.
The transformed normal `v'=diag(a)v` spans an eigenline of that cycle
over F_p. Its eigenvalue cannot be 1: that would make v' proportional to
`(1,1,1)`, contradicting isotropy for `p != 3`. Thus `p = 1 mod 3` and
`v'_1+v'_2+v'_3=0`.

**Lemma 4: the threefold case has an Eisenstein mirror.** For any prime
`p = 1 mod 3`, there are integers a,b with `a^2-ab+b^2=p`. For completeness,
`Z[omega]`, with `omega^2+omega+1=0`, is norm-Euclidean: rounding both
coefficients leaves a remainder of norm at most `3/4` times the divisor's
norm. Evaluation at a primitive cube root in F_p has a kernel ideal of
index p. That ideal is principal, and a generator has norm p. This uses
the standard Euclidean-domain-to-PID argument; see
[Conrad's notes, §4](https://kconrad.math.uconn.edu/blurbs/ringtheory/euclideanrk.pdf).

Then `w0=(a,b-a,-b)` has coordinate sum zero and squared norm `2p`.
Its reduction is nonzero. In the plane `x+y+z=0`, the isotropic cone over
F_p consists of two distinct lines, interchanged by swapping the first two
coordinates. Therefore w0 or that swap is projectively congruent to v'.
Undoing the sign change gives w projectively congruent to v, with norm 2p.
The map `x -> x-(x dot w/p)w` is an integral reflection of L: `x dot w`
is divisible by p, and `v dot w=0 mod p` ensures it preserves L.
This finishes `1 => 2`.

**The remaining equivalences.** For `2 => 3`, choose a primitive integral
normal w of the rational reflection and write `n=w dot w`. Integrality on
the three `p e_i` gives `n | 2p w_i w_j` for every i,j. Primitivity gives
`n | 2p`, so `n` is `1,2,p,2p`. Norms 1 and 2 give a coordinate sign flip
or a signed coordinate swap; preservation of L would force a zero
coordinate of v or two coordinates equal up to sign. They are excluded.
For `n=p` or `2p`, integrality on all x in L gives `p | w dot x`.
Thus w modulo p annihilates `v^perp` and is proportional to v. It is nonzero
modulo p because `0<n<p^2`. The construction already proved in
`MultiQuintupleRootReflection` gives `3 => 2`, and `2 => 1` is immediate. ∎

**What this argument establishes on paper.** It addresses the
automorphism/short-root equivalence seen in the census. Combined with the
projective-root-to-vanishing theorem, an extra lattice symmetry forces a zero
progression. The converse from identically zero coefficients to a root is
proved separately by the completed Lean theorem above. The arbitrary-
automorphism argument itself remains outside the formalization.

`scripts/check_lattice_symmetry.py` checks the proof's intermediate claims
against the existing exhaustive rational automorphism enumerator. It checks
the skew integrality, possible orders, order-three signed permutations,
extracted roots, and equality of all reflection and short-root matrices.
It separately constructs an Eisenstein mirror for all 611 primes
`p <= 10000` with `p = 1 mod 3`. A nonintegral rational order-three rotation
serves as a control: rationality alone does not justify Lemma 3.
The full run through prime 1000 checks 3,172 projective classes and 9,376
automorphisms; all 1,196 noncentral classes have an extracted reflection,
with no disagreement between the complete reflection and short-root sets.
The saved [bounded verification record](docs/verification/lattice_symmetry.json)
states the actual census bound and counts; these checks do not establish the
universal theorem in Lean.

```sh
python3 scripts/check_lattice_symmetry.py --max-prime 1000 \
  --eisenstein-bound 10000 --output /tmp/lattice-symmetry.json
```

### An explicit infinite sparse family [Lean theorem, 2026-11-01]

The norm construction also gives a direct specialization that needs no
primality assumption. For every `t >= 0`, put

`p = 9t^2 + 15t + 7`, `j = 3t+2`, `k = 3t+3`.

Then every coefficient of `q^(pN+k)`, for every `N >= 0`, vanishes in

`Q(q,q^p) Q(q^j,q^p) Q(q^k,q^p)`.

The index triple `(1,j,k)` has squared norm `2p`; p is odd and is 1 modulo
3. The negative short-root reflection has target `2k=1+j+k` and cancels
the full progression. The bounds `0<1,j,k<p/2` hold for every t. The moduli
strictly increase, so this gives infinitely many distinct sparse products.

| t | p | Three indices | Identically zero progression |
|---|---|---|---|
| 0 | 7 | 1, 2, 3 | `7N+3` |
| 1 | 31 | 1, 5, 6 | `31N+6` |
| 2 | 73 | 1, 8, 9 | `73N+9` |
| 3 | 133 | 1, 11, 12 | `133N+12` |
| 4 | 211 | 1, 14, 15 | `211N+15` |

`Ramanujan.MultiQuintuple.coeff_eisensteinFamily_zero` in
[MultiQuintupleEisensteinFamily](RamanujanTau/MultiQuintupleEisensteinFamily.lean)
proves this for the actual stabilized five-Pochhammer products. In
particular the composite modulus 133 is included. This is an explicit
corollary of the existing general short-root theorem; the p=31 instance
was already among the known examples. No claim that this family is new
to the literature is made. It does not depend on the unformalized
automorphism classification above.

The [verification record](docs/verification/eisenstein_family.json) records
the full build, axiom audit, and independent arithmetic. The latter compares
direct multiplication of the five Pochhammer factors with the bilateral
Watson sums, coefficient by coefficient, for the first six parameters.
Run it with `python3 scripts/check_eisenstein_family.py`.

### The uniform projective target law

Write a short root as `w=lambda*v+p*a` and put `u=(v dot w)/p`.  For a branch
point in coefficient residue `r+p*q`, the exact completed-square pairing is

```text
Y dot w = p * (2*lambda*r - sum(w) + 6*u
               + p*(2*lambda*q + 2*A)),
A = sum a_s*(3*n_s+b_s).
```

`RamanujanTau.MultiQuintupleRootVanishingEquivalence` proves this identity for arbitrary
integral parameters.  Consequently the positive target is the single congruence

```text
2*lambda*r = sum(w)-6*u  (mod p),
```

while the sign-corrected negative target is

```text
c*lambda*(2*lambda*r-sum(w)+6*u) = 12  (mod p),   c*e=2.
```

The same module proves that both target laws close all eight bilateral branches for every short
root: the output signs exist, their product reverses, the exponent is preserved, and the positive
or sign-corrected negative coordinate map is involutive.  Two general pairing-to-vanishing bridges
then turn those local branch maps into fixed-point-free involutions of the complete coefficient
support.  The resulting unified projective-root theorem proves every coefficient in the predicted
progression of the actual stabilized three-factor Pochhammer product is zero.
The target laws are now necessary inside this mechanism as well as sufficient.  If one positive
reflected coordinate closes on a quintuple branch, its affine base is divisible by `p` whenever
`c*lambda*i` is invertible modulo `p`; if one sign-corrected negative coordinate closes, it forces
`c*lambda*base = 12 (mod p)` whenever `i` is invertible.  The Lean theorems use explicit Bezout
identities, so neither result hides a primality or division assumption.

`RamanujanTau.MultiQuintupleRootVanishingClassification` isolates the exact global boundary.  For
each actual coefficient it proves

```text
coefficient = 0
  <==> #positive branch points = #negative branch points
  <==> a sign-reversing bijection of the two finite supports exists.
```

Progression-wise, persistent vanishing is therefore exactly shellwise sign balance.  A projective
root supplies one coherent affine involution on every shell.  The desired bare
Root--Vanishing biconditional is proved equivalent to a single named rigidity proposition:
every abstract shellwise balance is induced by a short projective-root target.  That rigidity
proposition is not smuggled in as an axiom—and the unrestricted version is now formally
**disproved**.  The counterexample is

```text
p=9, (i,j,k)=(3,3,3), R=1:
Q(q^3,q^9)^3 is supported on multiples of 3, so every coefficient q^(9N+1) is zero;
no projective-root target exists because e*p is 0, never 1 or 2, modulo 3.
```

This is an exact power-series proof, not a scan.  The same module now proves the exact scaling law

```text
Q(q^(g*i),q^(g*p)) = expand_g(Q(q^i,q^p)),
[q^n] expand_g(F) = if g divides n then [q^(n/g)]F else 0.
```

Consequently every persistent vanishing in a common-scale lift satisfies the exhaustive dichotomy

```text
scaled vanishing at R
  <==> g does not divide R
        or (g divides R and the primitive product vanishes at R/g).
```

There is no third common-scale mechanism. If the descended triple satisfies
`AdmissibleSparseTriple` and R/g is a canonical residue, the completed converse
identifies the second clause with a primitive projective-root target. Descended
products outside those hypotheses require a broader classification.

`RamanujanTau.MultiQuintupleLocalSupport` proves a second, strictly more general support theorem.
For every odd `d` satisfying

```text
d | p,  d | 3i,  d | 3j,  d | 3k,
```

every coefficient degree lies in one of only eight classes modulo `d`:

```text
b1*i + b2*j + b3*k,  where each bs is 0 or 1.
```

Any residue outside those classes gives an identically zero progression.  This formally proves the
mixed example `Q(q,q^15) Q(q^3,q^15)^2`, whose entire `15N+2` progression vanishes even though the
three indices have no common scale.  For prime `p >= 5` and nonzero canonical indices, any such
nontrivial `d` would force `p | i,j,k`, so the local sieve disappears.  This separates elementary
local support gaps from the primitive cancellation problem. The corrected
classification is therefore explicitly restricted to prime, pairwise-distinct,
isotropic triples and canonical residues. Its original interface,
`AdmissibleRootVanishingRigidity`, is now discharged by
`admissibleRootVanishingRigidity_proved`.
The scanner now derives the signed lattice reflection and residue from these formulas rather than
searching over all automorphisms.  An exact sweep through `p<=251` checked 162 reflective classes:
every predicted residue had the root-specific affine certificate and was an observed zero, with
zero mismatches. This sweep supplied finite evidence before the general converse
was proved. The forward coefficient progression is a formal theorem for arbitrary
parameters satisfying the root and target hypotheses.

### Exact eight-coset theta reduction and the rigidity bottleneck

`RamanujanTau.MultiQuintupleThetaCosets` packages the three bilateral branch bits as eight
shifted cosets of `(6p Z)^3`.  For branch `b=(b1,b2,b3)`, the base coordinates are

```text
(6i + sign(b1)p, 6j + sign(b2)p, 6k + sign(b3)p),
```

and square completion identifies exponent `K` exactly with the common ternary norm shell

```text
24pK + (6i-p)^2 + (6j-p)^2 + (6k-p)^2.
```

If `Theta_b` denotes the representation series of branch coset `b`, the actual triple
quintuple product is proved equal, as a formal power series, to its top-parity Walsh component

```text
sum_b (-1)^(b1+b2+b3) Theta_b.
```

The module proves character orthogonality and the integral inversion formula

```text
8 Theta_b = sum_a chi_a(b) ThetaHat_a.
```

It also proves that the lone parity projection is not injective.  This is a structural warning:
one scalar vanishing identity cannot be promoted to equality of the eight component theta series
without additional modular, Hecke, or twisting information.  All eight Walsh projections would
be sufficient. At this stage the problem was to recover enough spectral
information from the persistent progression identity; the completed proof
instead uses the dual-shell phase partners described below.
More precisely, the signed series is now proved to be the difference of the two nonnegative
representation series formed by the four positive- and four negative-parity cosets.  Persistent
vanishing is exactly equality of those two representation counts along the progression.  Thus the
spectral question is an isospectral-unions problem, not equality of two individual ternary forms;
Schiemann's individual-form rigidity cannot be applied without an additional argument.

`RamanujanTau.MultiQuintupleThetaRigidity` then proves two geometric facts needed after that
spectral step.  First, under the canonical odd-modulus hypotheses, the nonnegative progression
shells exhaust the full affine integral residue fiber; coherence is not being inferred from a
sparse subset of its points.  Second, every noncentral rational orthogonal involution of ternary
space has eigenspace dimensions `(2,1)` or `(1,2)` and is exactly a Householder reflection or the
negative of one.  A coherent involution is proved to pair the complete coefficient support and
force persistent vanishing.

`RamanujanTau.MultiQuintupleThetaArithmetic` proves the next arithmetic bridge.  In affine indices
`m_s=3n_s+b_s`, every completed coordinate is `(6i_s-p)+2p*m_s`, and the progression fiber is
`i*m_1+j*m_2+k*m_3=R (mod p)`.  Despite each `m_s` using only residues zero and one modulo three,
every vector of the homogeneous index-`p` congruence lattice is constructively a difference of two
Watson points in the same fiber.  Therefore a coherent rational involution maps the entire
congruence lattice integrally and maps all three `p*e_s` test vectors to integral vectors.  The
rational Householder classification is also strengthened by clearing denominators: its normal may
always be chosen as a nonzero integral vector.  It is now primitively normalized with an explicit
square-Bézout certificate, and integrality on the three `p*e_s` vectors forces its squared norm into
the exact list `1`, `2`, `p`, or `2p`.  It now excludes the norm-`1` and norm-`2`
signed-coordinate/permutation stabilizers by six explicit canonical support cases, sharpens the
list to `p` or `2p`, and proves that the primitive normal is a projective lift of `(i,j,k)` modulo
`p`.  Finally, closure and weight reversal on one Watson point feed an exhaustive `ZMod 3`
converse: the positive Householder case forces norm class `1`, the negative case forces norm class
`2`, and the already-proved coordinate-closure necessities give the exact projective target
congruence.  Thus every coherent admissible theta involution supplies a complete
`ProjectiveRootTargetCertificate`.  The converse is now constructive as well.  A positive target
builds the rational Householder involution and a negative target its negative; the corresponding
uniform eight-branch theorem selects a weight-reversing partner at every point of the affine fiber.
These partners satisfy the required coordinate transport globally, so every target certificate
supplies a coherent theta involution.

The formal theorem is an exact equivalence between projective-root targets and nonempty coherent
theta involutions on admissible data.  It upgrades the former sufficient reduction: spectral
coherence, theta-coset rigidity, and corrected Root--Vanishing rigidity are now proved logically
equivalent propositions.  The rational geometry and the entire arithmetic extraction are therefore
checked using only Lean's standard axioms. At this stage, the reverse
Root--Vanishing direction was reduced to one remaining claim:

1. **Spectral coherence:** persistent vanishing of the top Walsh component forces one coherent
   rational orthogonal involution of the eight cosets.

Parity noninjectivity explains why this requires extra content: a single scalar
Walsh identity does not formally determine all eight theta components. The
completed proof resolves the problem using Poisson summation, actual phase
partners, and integral short generation, as described below.

There is now a sharper scalar formulation.  `RamanujanTau.MultiQuintupleThetaCharacter` proves
that for the affine Watson index `m=3n+b`, the branch sign is

```text
chi_3^+(m) =  1  if m = 0 (mod 3),
             -1  if m = 1 (mod 3),
              0  if m = 2 (mod 3),
```

which is the nontrivial quadratic character modulo three evaluated at `m+1`.  Consequently the
eight-coset Walsh projection is exactly one theta series weighted by
`chi_3^+(m_1)chi_3^+(m_2)chi_3^+(m_3)`, and this character theta series is proved equal to the actual
triple quintuple product. This supplied an alternative way to formulate the
converse as nonvanishing of one explicit character theta component.  This makes finite Weil transforms at `3` and `p`, Hecke
propagation, and cusp-order separation concrete alternatives to reconstructing an isometry from
four-versus-four representation counts.

There is now a second, exactly equivalent route that avoids recovering the isometry directly.
`RamanujanTau.MultiQuintupleThetaWitness` proves the classical contrapositive normal form

```text
projective root targeting R
    or
one N with [q^(p*N+R)] Q(q^i,q^p)Q(q^j,q^p)Q(q^k,q^p) != 0.
```

For admissible data this root-or-finite-witness dichotomy is proved logically equivalent to
theta-coset rigidity, spectral geometric coherence, and corrected Root--Vanishing rigidity.  Both
alternatives carry finite certificates. An effective geometry-of-numbers or
modular bound for the first nonzero witness was therefore another possible route
to the converse. The completed proof does not require the quantitative bound
proposed below.

The new exact command

```bash
python3 scripts/paley_spinor_scan.py witness-scan --max-prime 2600 --depth 700
```

checks the certificate dichotomy residue by residue.  Its current census is

```text
projective classes                                     18,704
residue problems                                   31,479,496
projective-root certificates                            4,910
finite nonzero coefficient witnesses               31,474,586
latest first witness progression index                    541
violations of N <= p/4                                      0
unresolved residues / root-nonzero conflicts             0 / 0
```

This remains bounded evidence, not a universal cutoff theorem. The converse
now guarantees a finite witness whenever there is no root target, but it does
not give the following proposed bound on the first witness:

```text
if no projective root targets R, then some nonzero coefficient occurs with N <= floor(p/4).
```

`AdmissibleQuarterCutoffRootOrProductWitness` formalizes exactly this finite target, and
`admissibleRootVanishingRigidity_of_quarterCutoff` proves that it closes corrected rigidity for
each datum.  The scan reports reflective and nonreflective witness profiles separately, exact
relative maxima, and any quarter-bound violations; none occur through `p<=2600`.  This empirical
linear bound is substantially sharper than the generic modular-form bounds one would get without
using the special threefold product character and index-`p` lattice geometry, but it is not promoted to a
theorem by the computation.

### Poisson-dual shell separation

There is a complementary finite-looking attack on the same converse.  Write
`a=(i,j,k)` and let the integral numerators of the dual congruence lattice be

```text
w congruent lambda*a (mod p).
```

After square completion, the eight branches have a common quadratic part and a common constant.
For a target residue `R`, the Fourier amplitude attached to one dual vector is therefore an exact
signed sum `A_R(w)` of `6p`-th roots of unity.  Direct cancellation of the lattice basis gives the
phase formula used by `paley_spinor_scan.py`; its dependence on the branch bits is affine.  Hence

```text
A_R(w) = zeta^C * product_(s=1)^3 (1-zeta^delta_s),
delta_s = 2*w_s - 6*w_3*(3*k)^(-1)*a_s  (mod 6p).
```

This proves two useful algebraic facts in the scanner: whether `w` carries the Watson character is
independent of `R`, and increasing `R` multiplies its amplitude by the common phase

```text
zeta^(6*w_3*(3*k)^(-1)).
```

The remaining root-of-unity sums are tested without floating point.  Since
`Q(zeta_(6p))=Q(zeta_3)(zeta_p)` for prime `p>=5`, a sum vanishes exactly when its `p`
coefficients in the basis `(1,zeta_3)` are all equal.  The command

```bash
python3 scripts/paley_spinor_scan.py dual-shell-scan \
  --max-prime 1000 --shells 4 --shift-radius 1
```

enumerates the first four supported norm shells.  Its shift box comes with a geometric lower bound
for every omitted vector, so each selected shell is certified complete.  The exact result is

```text
projective classes                                  3,172
residue problems                                2,055,986
incomplete selected shells                              0
four-shell/root-target mismatches                       0
```

That bounded agreement does **not** extend to a universal four-shell theorem.  The exact hierarchy
of first failures begins as follows:

```text
one shell    p=71,   (i,j,k)=(1,4,14),    R=36
two shells   p=191,  (i,j,k)=(1,17,61),   R=22
three shells p=709,  (i,j,k)=(1,34,286),  R=675
four shells  p=1439, (i,j,k)=(1,63,391),  R=229
five shells  p=1523, (i,j,k)=(1,147,468), R=572
```

The four-shell counterexample is especially transparent.  There is no short projective root, and
the first five complete supported shells are

```text
norm 3p:  +/-(-22,  53,  32)                         zero at R=229
norm 12p: +/-(-44, 106,  64)                         zero at R=229
norm 48p: +/-(-88, 212, 128)                         zero at R=229
norm 66p: +/-(-298,-67,41), +/-(-254,-173,-23)       zero at R=229
norm 69p: +/-(-89,149,-263)                          nonzero at R=229
```

For each of the first four shells the signed phase counter is literally empty before any
cyclotomic relation is used.  The fifth counter is
`{2221:-3, 3535:3, 5099:3, 6413:-3}` modulo `6p=8634`, hence is nonzero by the exact
`Q(zeta_3)(zeta_p)` test.  Every omitted shift has norm at least `4,659,122`, while the fifth norm is
only `99,291`, certifying that all five displayed shells are complete.  The same residue has the
actual nonzero product witness `[q^37643]=1`, with progression index `N=26`; it is a counterexample
to the fixed four-shell diagnostic, not to Root--Vanishing rigidity.  Reproduce the certificate with

```bash
python3 scripts/paley_spinor_scan.py dual-candidate \
  --prime 1439 --indices 1,63,391 --residue 229 --shells 4
```

`RamanujanTau.MultiQuintupleDualShellCounterexample` independently kernel-checks that `1439` is
prime, that `(1,63,391)` is isotropic, and that no projective lift can have norm `p` or `2p`.
The proof bounds all root coordinates by `53` and exhausts the resulting congruence box, leaving
only `0` and `+/-(-22,53,32)`, whose nonzero norm is `3p`.

Analytically, persistent primal vanishing implies that **every** complete dual norm shell has zero
amplitude: apply Poisson summation to the Gaussian specialization and separate successive dual
norms as the Gaussian parameter tends to zero.  A valid finite version must therefore use a
datum-dependent bound:

```text
Effective dual-shell rigidity:
produce B(p,i,j,k) such that cancellation through all complete supported shells of norm <= B
forces a short-projective-root target.
```

The amplitude factorization, affine residue law, exact cyclotomic decision, shell completeness
certificate, bounded four-shell agreement through `p<=1000`, and the fixed-cutoff counterexamples
above are established exactly.  Four-shell rigidity is false, and merely replacing four by five is
also false.

#### The adaptive correction: stop at the first spanning shell

The failures reveal a sharper invariant than shell count.  Accumulate the complete supported dual
norm shells in increasing order, and let `rho_span` be the norm of the first shell for which their
vectors span `Q^3`.  In the hard examples the entire falsely cancelling prefix has rank at most two:

```text
p=709:   the first rank-three shell detects the three-shell false zero
p=1439:  the first four cancelling shells span only a plane; shell five spans and detects
p=1523:  the first five cancelling shells span only a plane; shell six spans and detects
```

This leads to the precise replacement for every fixed-shell conjecture:

```text
Spanning-Shell Rigidity (conjecture).
For prime, pairwise-distinct, isotropic (p;i,j,k), if every complete supported
dual shell of norm at most rho_span cancels at R, then R is a short-projective-root target.
```

It is finite for a theorem-level reason.  For any nonzero `p`, any indices, and any choice of the
inverse parameter in the phase formula, the scalar-zero dual vectors

```text
v1=(p,p,p),  v2=(p,p,-p),  v3=(p,-p,p)
```

are supported: each phase difference is `p*(+/-2 mod 6)`, so it is not divisible by `6p`.
Furthermore

```text
||v1||^2=||v2||^2=||v3||^2=3p^2,    det(v1,v2,v3)=-4p^3.
```

Consequently `rho_span <= 3p^2`.  This universal supported-spanning certificate is kernel-checked
in `RamanujanTau.MultiQuintupleDualSpanning`; unlike spanning-shell rigidity itself, it is a proved
theorem and needs no primality or isotropy hypothesis.

The reproducible adaptive scan is

```bash
python3 scripts/paley_spinor_scan.py dual-span-scan \
  --max-prime 3000 --max-shells 64 --shift-radius 1
```

It compares the exact common cyclotomic zero set through `rho_span` with the exact short-root target
set.  The census gives

```text
projective classes                                 24,741
residue problems                               48,334,107
incomplete selected shells                              0
missing spanning shells                                 0
spanning-shell/root-target mismatches                    0
```

The same command restricted to `p=1439` and `p=1523` checks all 60 and 63 projective classes,
respectively, with no mismatch.  These computations are exact bounded evidence, not a proof of the
spanning-shell conjecture. This suggested proving spanning-shell rigidity and
formalizing the analytic bridge from persistent primal vanishing to cancellation
on every complete dual shell. The analytic bridge is now proved. The final
converse uses integral short generation rather than assuming the first-spanning
cutoff criterion, which remains a separate stronger question.

#### Phase hyperplanes and the perfect-shell refinement

The exact factorization gives more structure than a zero test.  Put

```text
u = ((i,j,k) dot w)/p,
C = 6*w3*q*R + 6*u - (w1+w2+w3).
```

For the antipodal pair `+/-w`, the exponent comparing its two factored amplitudes is

```text
2*C + delta_1 + delta_2 + delta_3
  = 6 * (2*u + q*w3*(2*R-i-j-k)).
```

Consequently its phase matches modulo `6p` exactly when

```text
2*u + q*w3*(2*R-i-j-k) = 0  (mod p).
```

`RamanujanTau.MultiQuintupleDualPhase` proves this identity and divisibility equivalence over the
integers.  It explains the false fixed-cutoff prefixes: collinear vectors repeat one phase
hyperplane, while coplanar shells can cross-pair within the same partial geometry.  The first new
direction tests whether that partial matching extends.

For an actual reconstruction proof, rational vector span is not quite the strongest invariant.
A set is *perfect* when the tensors `w*w^T` span the six-dimensional space of ternary quadratic
forms.  Consider

```text
(p,p,p), (-p,p,p), (p,-p,p), (p,p,-p), (2p,p,p), (p,2p,p).
```

Every coordinate is a nonmultiple of three after removing `p`, so every vector is universally
Watson-supported.  The first four norms are `3p^2`, the last two are `6p^2`, and their six quadratic
tensors have determinant `144` after removing the common scale.  The Lean theorem
`ternaryMatrix_norm_preserving_of_six_vectors` proves the key consequence directly: a rational
three-by-three linear map preserving these six norms preserves every ternary norm and is therefore
orthogonal.

There is also an integral-generation certificate.  The three vectors

```text
(p,p,p), (2p,p,p), (p,2p,p)
```

have determinant `p^3` and reduced determinant `1`, hence generate `p*Z^3`.  For canonical
`0 <= i,j,k <= p/2`, one can independently choose centered shifts `z_s in {0,-1}` so that

```text
w=(i+p*z1,j+p*z2,k+p*z3)
```

is supported; two adjacent choices cannot both kill a support factor because their phases differ
by `2p` modulo `6p`.  Lean proves both existence and the bound

```text
||w||^2 <= 3*p^2.
```

Adding this scalar-one lift to the three scalar-zero generators produces the entire projective
dual lattice.  Therefore the first cutoff that is both perfect and lattice-generating exists by
norm `6p^2`.  This yields a proof-oriented strengthening of spanning-shell rigidity:

```text
Perfect-Generating Phase Rigidity (separate finite-cutoff conjecture).
Aggregate cancellation through the first perfect, lattice-generating supported cutoff
is induced by one phase-reversing linear pairing of its vectors.
```

Once that pairing is obtained, the proved perfect-set theorem forces it to be orthogonal and the
proved generators force it to preserve the full projective dual lattice.  Involutive phase reversal
then lands exactly in the Householder/projective-root classification. This
formulates a stronger finite-cutoff question: promote an exact cyclotomic
multiset equality to one coherent linear pairing at that particular cutoff.
`dual-perfect-scan` tests this strengthened criterion exactly.

The exact reconstruction census through `p<=3000` reports

```text
projective classes                                 24,741
residue problems                               48,334,107
missing or incomplete perfect cutoffs                    0
perfect-shell/root-target mismatches                    0
coherent phase-reversing maps                         6,039
nonunique vector phase pairings                           0
nonlinear/incoherent pairings                             0
nonorthogonal recovered maps                             0
noninvolutive recovered maps                             0
dual-lattice preservation failures                       0
signed-Householder/root-map mismatches                    0
maximum compressed shell weight                         24
shells at/above non-pairing threshold `2p`               0
expanded/compressed amplitude disagreements              0
non-pairing cyclotomic cancellations                     0
```

The largest perfect prefix uses 61 shells, at `p=2963`, and the largest observed perfect-shell
norm is `993p`, at `p=2971`.  These are bounded exact results, not the universal phase-pairing
lemma.  They do show that the proposed finite promotion is not merely compatible with the zero
sets: it reconstructs the already formalized root involution exactly in every tested case.

### Cubic compression: eight phase terms collapse to one

There is a further projective constraint hidden in the factored amplitude.  Write

```text
w_s = lambda*a_s + p*z_s,       3*q*k = 1 + p*t.
```

Then direct substitution gives

```text
delta_s = 2*w_s - 6*w_3*q*a_s
        = 2*p*(z_s - 3*z_3*q*a_s - lambda*a_s*t).
```

`RamanujanTau.MultiQuintupleDualCompression` proves this identity and the exact support
equivalence in Lean.  Once support excludes divisibility by `6p`, the reduced parenthesis is
`+1` or `-1` modulo three.  Thus each of the three factors is evaluated only at a nontrivial cube
root.  Since

```text
1-zeta^(4p) = zeta^p * (1-zeta^(2p)),
```

the original signed eight-term affine cube is exactly

```text
zeta^E(w) * (1-zeta^(2p))^3
```

for a single computable `6p`-phase `E(w)`.  The common cubic factor is nonzero.  Hence a complete
shell amplitude is zero exactly when the positive sum `sum_w zeta^E(w)` is zero: its cyclotomic
weight is the number of supported vectors, not eight times that number.

There is one more forced cancellation in the exponent.  Modulo three,
`w_s = p*t_s`, while the number of conjugate factors is exactly the number of
`t_s = -1`.  Substitution shows

```text
3 | E(w).
```

`MultiQuintupleDualCompression` proves this order reduction in Lean, including the zero-one sign
encoding and the antipodal law `E(-w)=3p-E(w)`.  Hence the remaining shell sum is a sum of
`2p`-th roots, not arbitrary `6p`-th roots.  Cubic three-cycles cannot occur at all.  Complete norm
shells are antipodally closed and therefore have even weight.  Lam--Leung's weight semigroup for
order `2p` now gives a sharp conclusion: a non-pairing `p`-gon must occur an even number of times,
so below weight `2p` every vanishing shell is a disjoint union of opposite pairs.  The parity and
weight argument is also proved directly in Lean as
`constant_bucket_difference_eq_zero_of_even_weight_lt_two_mul`.

The exact scanner computes this compressed phase directly, verifies it against the original
expanded amplitude on every common zero, tests whether every zero is completely opposite-phase
balanced, and then performs the existing linear/orthogonal/lattice/root reconstruction.  The
earlier finite proof program proposed a universal sub-`2p` perfect-prefix
shell-weight bound before promoting the matching to one linear map. The
2026-11-01 theorem below removes that weight-bound obligation for complete
Watson shells. The recomputed exact census through `p<=3000` records maximum compressed weight `24`;
no perfect-prefix shell reaches weight `2p`.  Across all 6,039 common-zero residues it finds no
expanded/compressed disagreement, no non-pairing shell, no ambiguous opposite-phase partner, and
no failure in the subsequent linear, orthogonal, involutive, lattice-preserving, or
signed-Householder checks.

### Converse attack: pairing without a weight bound [Lean algebra, 2026-11-01]

The twisted antipodal law contains more information than even shell size.
It rules out non-pairing cyclotomic cancellation at **every** weight.

**Theorem.** Let p be an odd prime, let rho be a primitive `2p`-th root of
unity in a characteristic-zero field, and let a finite phase multiset have
multiplicities n(a), indexed modulo `2p`. Assume

`n(a) = n(p-a)` for every phase a.

Then `sum_a n(a) rho^a = 0` if and only if
`n(a)=n(a+p)` for every a. In particular the multiset can be paired into
opposite phases, without any upper bound on its cardinality or multiplicities.

*Proof.* Set `eta=rho^2`, a primitive p-th root. Every phase is uniquely
`2j` or `2j+p`, with `0<=j<p`. Regroup the sum as

`sum_(j=0)^(p-1) d_j eta^j`, where `d_j=n(2j)-n(2j+p)`.

The minimal polynomial of eta over Q is `1+X+...+X^(p-1)`, so this sum
vanishes exactly when all integer coefficients d_j are equal. The twisted
antipodal law gives `n(0)=n(p)`, hence `d_0=0`. All d_j are therefore zero.
The converse is immediate by pairing opposite phases. ∎

For Watson shells, take `a(w)=E(w)/3 mod 2p`. The already proved facts
`3 | E(w)` and `E(-w)=3p-E(w)` supply precisely this twisted antipodal law.
The new module
[MultiQuintuplePhasePairing](RamanujanTau/MultiQuintuplePhasePairing.lean)
proves the prime coefficient criterion, the multiplicity balance induced by
an antipodal equivalence, and the factorization of the actual root powers
into the prime-order sum. Its final theorem is
`antipodal_shell_amplitude_zero_iff_pair_balance`. It uses Mathlib's
`IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int`; no new cyclotomic
irreducibility assumption is introduced.

**Why phase pairing alone is insufficient.** Equal phase counts give shellwise pairings, but
neither unique partners nor a common linear isometry. That distinction is
essential. Here is a finite counterexample to a purely geometric shortcut,
using artificial phases rather than the Watson formula. Take the 18 vectors
`+/-e_i` and `+/-e_i+/-e_j` in Z^3, with shells of norms 1 and 2. They
generate Z^3, and their quadratic tensors span all six ternary quadratic
forms. At p=11 assign opposite phases so that the unique partners include

`e1 <-> e2`, `e3 <-> -e3`, but `(e1+e2) <-> (e1-e2)`.

Complete the phase assignment antipodally. The checker below gives every
phase explicitly and verifies cancellation and unique partners on both
shells. No linear map realizes the pairing: the first two basis images force
`T(e1+e2)=e1+e2`, contrary to the prescribed partner. Thus a coherence
proof must use the actual arithmetic Watson phases; perfectness,
generation, and unique shell partners alone are insufficient. This example
does **not** disprove the corrected Root--Vanishing conjecture.

The route isolated at this stage was:

1. Formalize the analytic implication from persistent primal vanishing to
   cancellation on every complete Poisson-dual shell.
2. Use the actual Watson phase formula to prove that the forced pairings
   through a sufficient finite cutoff are induced by one linear map.
3. Apply the existing norm, lattice, involution, and short-root reductions.

All three obligations are now discharged in the completed converse. The
first-spanning and first-perfect cutoff claims remain stronger finite conjectures,
not consequences of the universal converse alone. No equivalence with those
particular cutoffs is asserted here.

**A faster exact attack.** `scripts/attack_phase_rigidity.py` uses an LLL
basis of `{w : w = lambda*(1,j,k) mod p}` to enumerate complete short shells.
It verifies the basis congruences and determinant `p^2`. If C is its inverse
coordinate matrix and `||w||^2<=B`, then
`|coordinate_i(w)|^2 <= B*sum_j C_ij^2`; rational Cauchy bounds therefore
certify the enumeration box. Support is just nondivisibility of each
coordinate by 3. Candidate residues come from the linear congruences that
could give one vector an opposite-phase partner. Every candidate is then
checked by the existing exact cyclotomic algorithm.

The deterministic sample attempts 350 cases: random large primes, triples
perpendicular to short fixed normals, known difficult cases, and reflective
classes. It completes 292, up to prime 196,821,127, with no spanning- or
perfect-cutoff mismatch. All 149 common-zero residue checks have unique
partners forming an orthogonal, involutive, lattice-preserving linear map.
The other 58 cases exceed the explicit 500,000-point box cap and are
**skipped**, not verified. This is a selected sample, not a census of all
primes or triples up to that bound.

`scripts/check_phase_pairing.py` independently compares the new enumeration
and candidate pruning with the old exhaustive scanner on seven small/hard
cases, including 1439 and 1523. It also checks 240 synthetic antipodal phase
multisets, some with weight over 7,000 times `2p`, and six double-p-gon
negative controls that violate the antipodal hypothesis.
The [proof verification record](docs/verification/phase_pairing.json),
[arithmetic controls](docs/verification/phase_pairing_arithmetic.json), and
[sampled search](docs/verification/phase_rigidity_search.json) keep the
formal and computational claims separate.

```sh
lake env lean scripts/audit/multi_quintuple.lean
python3 scripts/check_phase_pairing.py --output /tmp/phase-pairing-arithmetic.json
python3 scripts/attack_phase_rigidity.py --output /tmp/phase-rigidity-search.json
```

### Full converse: a complete paper argument with finite certificates [2026-11-01]

**Verification status.** The argument below is now formalized end to end in
[MultiQuintupleFullConverse](RamanujanTau/MultiQuintupleFullConverse.lean).
The analytic Poisson bridge, universal lattice generation, and exact root-target
assembly are all proved. The
[full Lean record](docs/verification/full_converse_lean.json) reports the
published 9,336-job build and 251-declaration axiom audit. The earlier
[paper verification record](docs/verification/full_converse_paper.json) preserves
its historical 9,295-job build, 12-declaration audit, and independent Python
checks; it predates the complete formalization.

**Claim.** Let p be prime and let
`0<i<j<k<p/2`, with `i^2+j^2+k^2=0 mod p`. Put v=(i,j,k). For `0<=R<p`,
the coefficients of `Q(q^i,q^p) Q(q^j,q^p) Q(q^k,q^p)` in the progression
`p*N+R` vanish for every nonnegative N if and only if there are integers
`w, lambda, e`, with `e=1 or 2`, such that

```
w = lambda*v mod p,       w.w = e*p,       lambda != 0 mod p,
u = (v.w)/p,              c = 2/e,
```

and the target equation is

```
2*lambda*R = sum(w)-6*u mod p                  if e*p = 1 mod 3,
c*lambda*(2*lambda*R-sum(w)+6*u) = 12 mod p    if e*p = 2 mod 3.
```

The reverse implication here is the existing formal projective-root theorem.
The proof of the converse follows.

#### 1. Persistent zero coefficients force opposite phases on every dual shell

Let

```
L = {x in Z^3 : v.x = 0 mod p},
N = p*L* = {w in Z^3 : w = lambda*v mod p}.
```

Their Euclidean covolumes are p and p^2. Choose `q=(3k)^(-1) mod p`.
For a branch `b in {0,1}^3`, the original summation index n satisfies
`3*v.n+v.b=R mod p`. Put `c_b=q*(R-v.b) mod p` and

`x_b = v/p + (2b-1)/6 + c_b*(0,0,1)`.

Completing the squares identifies the progression with the Gaussian sum

`F(t) = sum_b (-1)^sum(b) sum_(x in L+x_b) exp(-pi*t*||x||^2)`.

More explicitly, the squared norm of the completed coordinate divided by
`6p` is `2K/(3p) + ||6v-p*(1,1,1)||^2/(36p^2)`, where K is the original
exponent. Canonical indices make every such exponent nonnegative. Thus
persistent vanishing implies `F(t)=0` for every `t>0`.

Poisson summation, applied to these eight absolutely convergent Gaussian
sums, gives

`F(t) = 1/(p*t^(3/2)) sum_(w in N) A_R(w) exp(-pi*||w||^2/(p^2*t))`.

For `zeta=exp(2*pi*i/(6p))`, direct substitution of x_b gives

```
A_R(w) = zeta^C product_s (1-zeta^delta_s),
C = 6*w3*q*R + 6*u - sum(w),       u=(v.w)/p,
delta_s = 2*w_s-6*w3*q*v_s.
```

Projectivity makes each `delta_s=2p*t_s`, with
`t_s=p^(-1)*w_s mod 3`. The amplitude is nonzero exactly when none of the
coordinates of w is divisible by 3. Call these vectors **supported**.
If n(w) counts the t_s equal to 2 modulo 3, then

```
A_R(w) = (1-zeta^(2p))^3 * rho^a(w),
rho = zeta^3,       a(w) = (C+p*n(w))/3 mod 2p.
```

The numerator is divisible by 3. Moreover
`a(-w)=p-a(w) mod 2p`. Separating successive Gaussian exponents as `t -> 0`
shows that each complete dual norm shell has amplitude zero. The antipodal
phase theorem proved above then gives equal multiplicities at a and a+p.
Consequently **every supported vector has an equal-norm opposite-phase
partner**. This step has no shell-weight bound.

#### 2. Short partners preserve all mutual dot products

All calculations in this paragraph, except explicitly displayed integer
norms, are in F_p. Put

```
h = (v.v)/p,       c0 = (2R-sum(v))/3,       D = h+c0,
lambda(w)*v = w mod p,
ell(w) = 2*(v.w/p)+c0*lambda(w).
```

Here `lambda` and `ell` are additive functions on N. The actual compressed
phase satisfies `a(w)=ell(w) mod p`. Write `w=lambda*v+p*z`. Expanding the
norm and polarizing gives

```
||w||^2/p = lambda(w)*ell(w)-D*lambda(w)^2 mod p,
2*(w.z)/p = lambda(w)*ell(z)+lambda(z)*ell(w)
             -2D*lambda(w)*lambda(z) mod p.                 (1)
```

The quotients are integers: all pairings of vectors in N are divisible by p.

**Short-vector uniqueness.** If distinct integral vectors w,w' have equal
norm and are congruent modulo an odd p, then `||w||^2 >= p^2/2`.
Indeed, write `w'-w=p*z`. Equality of norms implies
`2*w.z+p*||z||^2=0`, so `||z||^2` is even. Since z is nonzero it is at least
2. The parallelogram identity gives
`p^2*||z||^2 <= 4*||w||^2`. This lemma is now checked in Lean.

Consider all supported vectors with `||w||^2<p^2/2`. An opposite-phase
partner w' is distinct, has the same ell, and by uniqueness has a different
lambda. Subtracting the two norm equations in (1) therefore forces

`D*(lambda(w)+lambda(w')) = ell(w).`                         (2)

If D=0 this forces ell(w)=0 and hence `||w||^2/p=0 mod p`, impossible for
`0<||w||^2<p^2/2`. Thus D is nonzero whenever this supported set is nonempty.
Equation (2) is one fixed reflection on the pair of arithmetic coordinates
`(lambda,ell)`: `(lambda,ell) -> (ell/D-lambda,ell)`.
Substitution in the second equation of (1) shows that, for any two pairs
`w->w'` and `z->z'`,

`w'.z' = w.z mod p^2`.

Cauchy--Schwarz gives

`|w'.z'-w.z| <= 2*sqrt(||w||^2*||z||^2) < p^2`.

The integer difference must therefore be zero. Partners are also unique:
two partners have the same lambda by (2), so short-vector uniqueness applies
to them. We have proved, without assuming a linear map, that the short
partner permutation is involutive and preserves **all** dot products.

#### 3. Enough supported short vectors exist for every p >= 1250

The integral positive-definite lattice `(N, < , >/p)` has Gram determinant p.
Its dual, multiplied by p in the original Euclidean coordinates, is L.
Every nonzero vector of L has squared norm at least 3: norm 1 would force
one v-coordinate to be zero, and norm 2 would force two coordinates equal
up to sign.

Choose a basis b1,b2,b3 of N as follows. Choose b1 shortest; choose the
projection of b2 shortest in the rank-two projected lattice; extend to a
basis; size-reduce b3 along b2 in that projection and reduce b2,b3 along b1.
For the inner product divided by p, write the Gram--Schmidt squared lengths
as A,B,C and its three coefficients as mu,nu,xi. Then

```
|mu|,|nu|,|xi| <= 1/2,
A*B*C=p,       B>=3A/4,       C>=3B/4,
A is a positive integer,    M=A*B is an integer >=3.         (3)
```

The two inequalities follow because the reduced second vector cannot be
shorter than the chosen first vector, in N or in its projection. For the
last assertion, M is the last diagonal entry of the adjugate Gram matrix.
This adjugate is a Gram matrix of L, whose minimum is at least 3.

Use all coefficient vectors `(x,y,z)` with

`x,y in {-2,-1,0,1,2}, z in {0,1}`

that are nonzero isotropic vectors modulo 3 for the Gram form. Their images
in N are supported. Indeed, reduction `N/3N -> (Z/3Z)^3` is an isomorphism,
and a nonzero vector of sum-of-three-squares norm zero modulo 3 has all
three coordinates nonzero.

These vectors generate N over Z. To see this, a nonsingular ternary form
over F_3 has isotropic vectors spanning F_3^3: diagonalize it and check
`x^2+y^2+z^2` and `x^2+y^2-z^2`, up to an overall sign. Every isotropic
projective point has a representative with z=0 or z=1 in the displayed
box. Some such point has x nonzero, and replacing x=1 by -2, or x=-1 by 2,
gives the vector 3e1 as a difference of two included vectors. Likewise the
span contains 3e2. An included vector with z=1 then supplies 3e3. The
integer span contains 3Z^3 and is surjective modulo 3, so it is Z^3.

For every vector in this box, Gram--Schmidt gives the uniform bound

```
||x*b1+y*b2+z*b3||^2/p
 = A*(x+mu*y+nu*z)^2+B*(y+xi*z)^2+C*z^2
 <= p/M + (49A+25B)/4.                                    (4)
```

If M<12, then (3) gives A<=3 and B<=11, so (4) is at most
`p/3+211/2 < p/2` when p>=1250.
If M>=12, (3) gives `A^3<=64p/27` and `B^2<=4p/3`. For p>=1250 these imply
`A<=p/80` and `B<=p/30`. Thus (4) is at most

`p/12 + 49p/320 + 25p/120 = 427p/960 < p/2`.

Multiplying by p proves that supported vectors of squared norm strictly
below `p^2/2` generate N for every p>=1250. This is a universal geometric
bound, not an extrapolation from the scan.

#### 4. The finite range, including the one short-generator exception

For the 202 primes `5<=p<1250`, there are 14,370 triples of the form
`(1,j,k)` with `1<j<k<p/2` and `1+j^2+k^2=0 mod p`. The
[certificate file](docs/verification/short_watson_generators.json) gives
14,369 short generating sets, with at most five vectors per set. Each
vector is supported, lies in N, and has `2*||w||^2<p^2`. The gcd of the
three-by-three minors is exactly p^2, proving that their integer span is N.
The checker enumerates every normalized triple independently; it does not
identify cases using the elliptic J-invariant or trust the LLL generator.
Projective rescaling does not change N, and signed coordinate permutations
preserve all these properties, so this covers every original triple in
that prime range, except p=13.

At p=13 the two canonical admissible triples are `(1,3,4)` and `(2,5,6)`.
Their root-predicted residues are respectively `{2,4,10}` and `{3,9,11}`.
Every other residue has the following nonzero coefficient, written `(R,N,a)`
for `[q^(13N+R)]F(q)=a`:

```
(1,3,4): (0,0,1), (1,0,-1), (3,0,-1), (5,2,2), (6,0,1),
         (7,1,-1), (8,0,1), (9,0,-1), (11,1,1), (12,2,-1).
(2,5,6): (0,0,1), (1,0,-1), (2,0,-1), (4,0,1), (5,1,-1),
         (6,0,-1), (7,0,1), (8,0,1), (10,2,1), (12,1,-1).
```

The certificate contains an explicit norm-26 projective root for each of
the six predicted residues. The independent checker verifies their target
equations and computes the 20 witnesses directly from the five Pochhammer
factors, discarding only factors whose first exponent exceeds 40. Thus
this exception is fully settled; finite silence is not used as a proof.

```sh
python3 scripts/certify_short_watson_generators.py \
  --output /tmp/short-watson-generators.json
python3 scripts/check_short_watson_generators.py \
  docs/verification/short_watson_generators.json \
  --output /tmp/short-watson-generators-check.json
```

The [independent check record](docs/verification/short_watson_generators_check.json)
also exhausts the 468 nonsingular ternary Gram forms modulo 3 in the
box-generation lemma and all 48 orthogonal matrices modulo 3 used below.
These Python checks independently support the elementary arguments. The
completed Lean development checks the mod-three generating box, all p=13 root
and coefficient certificates, and all 14,369 short-generator certificates in
the kernel. It also proves normalized-line coverage and identifies the checked
generators with the required projective dual lattices.

#### 5. The one symmetry and the exact target equation

For p!=13, let S be all supported vectors of norm below `p^2/2`. Steps 3--4
show that S generates N. Step 2 supplies an involutive dot-product-preserving
permutation of S. Choose three independent elements of S and send them to
their partners. Equality of all pairwise dot products extends this map
uniquely to a rational orthogonal map T on Q^3; taking inner products with
the three basis images shows that it sends every element of S to its
partner. Therefore `T(N)=N` and `T^2=I`. Duality gives `T(L)=L`.

T is not I, since partners have opposite phases. Nor is it -I: phase
preservation modulo p would then give `ell(w)=0` for every w in S, hence
for every w in N. But `ell(p*e_s)=2*v_s` is nonzero modulo p. The same
generation argument shows that ell is preserved by T on all of N.

A noncentral rational orthogonal involution in dimension three is a
Householder reflection H_w or its negative. Choose its normal w primitive
integral and write n=w.w. Since pZ^3 is contained in L, integrality on p*e_s
gives `n | 2p*w_s*w_t` for all s,t. Primitivity gives `n | 2p`.
The possibilities n=1,2 would force a zero coordinate of v or two equal
up to sign, so `n=e*p`, e=1 or 2. Integrality on all of L then gives
`p | w.x` for every x in L. Thus `w=lambda*v mod p`, with lambda nonzero.
This is the arithmetic extraction already formalized upstream.

It remains to choose H_w versus -H_w and recover R. For supported x,
the parity of its actual phase is

`(-1)^a(x) = (-1)^sum(x) * chi_3(p) * chi_3(x1*x2*x3)`.

An integral norm-preserving map preserves sum(x) modulo 2. The reduction
of T modulo 3 is defined, because its denominator divides p, and is
orthogonal. Every orthogonal matrix for x^2+y^2+z^2 over F_3 is a signed
permutation: a norm-one column has exactly one nonzero coordinate. It
multiplies `chi_3(x1*x2*x3)` by a constant sign. Opposite phases on S force
that sign to be -1. If n=1 mod 3, the reflection H_w changes one coordinate
sign; if n=2 mod 3, it performs a signed transposition with sign product
+1. Hence T=H_w when e*p=1 mod 3, and T=-H_w when e*p=2 mod 3.

Write `u=(v.w)/p`, `c=2/e`, and `t_x=(x.w)/p`. Then

`H_w(x)=x-c*t_x*w`.

If T=H_w, preservation of ell and evaluation at `x=p*e_s` give `ell(w)=0`.
Since `3*ell(w)=6u+lambda*(2R-sum(v))`, this is exactly
`2*lambda*R=sum(w)-6u mod p`.

If T=-H_w, preservation gives `2*ell(x)=c*t_x*ell(w)`. Evaluate at
`x=p*e_s`, where `ell(x)=2v_s` and `t_x=w_s=lambda*v_s mod p`, to obtain
`c*lambda*ell(w)=4`. Multiplying by 3 gives precisely
`c*lambda*(2*lambda*R-sum(w)+6u)=12 mod p`.

Both branches give the required root target. Together with the explicit
p=13 check and the already formal forward implication, this completes the
paper argument for the full admissible converse. The proof does not rely
on uniqueness of arbitrary phase pairings, the first-spanning-cutoff
conjecture, or injectivity of an individual ternary theta series. Its key
input is the p-squared congruence in Step 2 and the *integral* generating
set below the same strict length bound.

### Initial Lean formalization progress [2026-11-01; superseded below]

At this stage the full admissible converse was not yet a Lean theorem.
The historical [verification record](docs/verification/short_converse_lean.json)
separates the then-checked results from the remaining obligations.

1. [Dual short geometry](RamanujanTau/MultiQuintupleDualShortGeometry.lean)
   identifies the compressed phase modulo p on actual projective lifts,
   proves their dot products divisible by p, upgrades the p² congruence to
   exact equality under the strict length bound, and proves partner uniqueness.
2. [Spanning isometries](RamanujanTau/MultiQuintupleSpanningIsometry.lean)
   extend a Gram-preserving pairing on a spanning family to one rational
   orthogonal map, including families with duplicate vectors.
   [Dual pairing isometry](RamanujanTau/MultiQuintupleDualPairingIsometry.lean)
   combines this with the arithmetic: existence of short phase partners,
   rational spanning, and one nonzero phase imply a noncentral orthogonal
   involution. Neither a coherent linear map nor involutivity is assumed.
3. [Integral span](RamanujanTau/MultiQuintupleIntegralSpan.lean) proves that
   determinant gcd one certifies generation over Z.
   [Small isotropic box](RamanujanTau/MultiQuintupleSmallIsotropicBox.lean)
   uses kernel-checked certificates for all 468 nonsingular symmetric Gram
   forms over F₃ to prove that the displayed coefficient box generates Z³.
   Its reproducible generator is
   [generate_small_isotropic_box.py](scripts/generate_small_isotropic_box.py).
4. [Generator estimates](RamanujanTau/MultiQuintupleShortGeneratorEstimate.lean)
   prove the size-reduced box estimate and the strict p/2 bound for p>=1250
   from hypotheses (3). Existence of a basis satisfying those hypotheses
   was not yet proved in Lean at this stage.
5. [The modulus-13 converse](RamanujanTau/MultiQuintupleConverseThirteen.lean)
   proves the complete Root--Vanishing equivalence for every admissible
   triple and residue at 13. The kernel checks the six roots, the 20 exact
   nonzero coefficients, and the completeness of the two canonical triples.
   The coefficient theorem uses the actual infinite products; no unproved
   truncation or Python correctness hypothesis is involved.

At that stage, closing the universal statement still required: the analytic Poisson
and shell-separation bridge in Step 1; existence of the reduced basis and
its identification with the actual dual lattice in Step 3; the 14,369
small-prime certificates and normalization in Step 4; and the integral
lattice preservation, phase-parity, and exact target assembly for the dual
involution in Step 5. The existing primal coherent-involution classification
does not by itself discharge this last dual assembly. No universal converse
was asserted by those initial files.

### Complete Lean converse [2026-11-01]

The obligations above are now discharged. The public theorem in
[MultiQuintupleFullConverse.lean](RamanujanTau/MultiQuintupleFullConverse.lean)
proves the full admissible Root–Vanishing equivalence and the original
`AdmissibleRootVanishingRigidity` interface.

The analytic bridge starts from the actual coefficient identity and applies
congruence-projected Poisson summation to all eight Watson branches. Absolute
convergence permits regrouping, and analytic power-series uniqueness separates
every norm shell. The exact Fourier amplitude compresses to a common nonzero
factor times one canonical phase per supported vector. The antipodal phase law
then forces opposite partners. Integral short generation is proved using a
reduced basis for p≥1250 and kernel-checked normalized tables below that bound;
the exceptional modulus 13 is settled separately. Finally, the short-partner
isometry and lattice-preservation arguments produce the precise projective root
certificate and residue condition.

The [full Lean verification record](docs/verification/full_converse_lean.json)
records the commands and axiom report. The earlier JSON and axiom snapshots
remain unchanged. The classification has the stated admissibility hypotheses;
it does not assert the false unrestricted converse or classify four-factor
products.

### The projective invariant is an elliptic `j`-invariant

The correct symmetric invariant is

```text
J = (i^2*j^2+j^2*k^2+k^2*i^2)^3 / (i^2*j^2*k^2)^2  (mod p).
```

It labels the signed-permutation/projective classes in the scan.  More importantly, if
`u=(j/i)^2` and `i^2+j^2+k^2=0`, then

```text
-256*J = 256*(1+u+u^2)^3 / (u^2*(1+u)^2),
```

which is exactly the Legendre elliptic-curve `j`-invariant at `lambda=-u`.  Thus the sparse
quintuple problem naturally meets the octahedral quotient of the isotropic conic and elliptic
moduli; `sigma2`'s quadratic character was only a coarse shadow of this invariant.

`RamanujanTau.MultiQuintuplePaleySpinor` formally proves this elliptic `j` bridge over an arbitrary
field.  It also kernel-checks the `p=71`, `(1,11,34)`, residue-`61` reflection, its short-root origin,
its involutivity, the eight residue constants, and the four exponent-preserving parity-reversing
affine branch pairings.  `RamanujanTau.MultiQuintupleRootBranch` now proves the corresponding
positive and sign-corrected negative eight-branch matching for every direct short root, including
branch-parity reversal, residue transport, exponent preservation, and involutivity.

On the q-series side, `RamanujanTau.MockTheta5QuintIdentity` proves the full formal bivariate
quintuple product identity.  `RamanujanTau.MultiQuintupleBilateralBridge` then proves, for every
`0 < i` and `2i < p`, that each coefficient of the actual stabilized five-Pochhammer series
`quintupleSpecialized p i` equals its finite signed Watson bilateral coefficient.
`RamanujanTau.MultiQuintupleCancellation` completes the direct-short-root end-to-end step: it
flattens the actual three-factor coefficient into one finite branch box, proves the reflected
partner stays inside that box, and applies the positive or sign-corrected negative matching as a
fixed-point-free sign-reversing involution.  Thus the resulting entire coefficient progression,
not merely a surrogate bilateral sum, is formally zero.

`RamanujanTau.MultiQuintupleProjectiveCancellation` now closes the two leading sparse examples.
It proves a reusable theorem that any exponent-preserving, sign-reversing involution of the
contributing branch points cancels the coefficient of the actual product.  For
`(p;i,j,k)=(71;1,11,34)`, it derives the eight residue-coset parameterizations from the target
coefficient, transports the non-direct short projective root `(6,-5,-9)` through the four affine
branch pairings and their exact inverses, and proves every `71n+61` coefficient zero.  For
`(79;1,6,11)`, the index triple itself is the norm-`2p` root, so the direct assembly proves every
`79n+9` coefficient zero.  Both statements concern the stabilized Pochhammer products, not a
surrogate bilateral model.

The first attractive conjecture was:

> For distinct canonical indices `0 < i_s < p/2`, the product
> `prod_s Q(q^{i_s}, q^p)` has an identically vanishing residue class modulo `p`
> whenever `sum_s i_s^2 = 0 (mod p)`.

The congruence is a strong signal, but it is **not sufficient**.  The exact scan finds

```text
p = 71, (i,j,k) = (1,4,14),  1^2 + 4^2 + 14^2 = 3*71,
```

while every residue modulo 71 has a nonzero coefficient within the checked range.  This is
a finite certificate against the proposed conclusion: once one nonzero coefficient has been
found in every residue class, no residue class can vanish identically.  The tuple `(1,4,33)`
at `p=79` is a second counterexample.

Thus the current evidence supports two narrower questions:

1. Is `sum i_s^2 = 0 (mod p)` necessary for a vanishing progression when the indices are
   pairwise distinct and no factors are equivalent under the elementary symmetries of `Q`?
2. What additional invariant separates the isotropic tuples that vanish from those that do
   not?

For `p=71`, the second elementary invariant

```text
sigma2 = i^2*j^2 + j^2*k^2 + k^2*i^2
```

separates the data perfectly: all 35 isotropic tuples with quadratic-residue `sigma2` have a
candidate vanishing class, while all 70 with non-residue `sigma2` have none.  It is not the
whole answer: at `p=79`, only 39 of the 78 nonzero quadratic-residue `sigma2` tuples vanish
(all 13 tuples with `sigma2=0` also vanish).  The projective `J`-invariant and reflective-lattice
criterion above now explain this split throughout the much larger census; the old `sigma2`
observation remains useful as the first coarse signal.

## First exact target: the p=7 triple

The scan also finds the previously unstated small triple

```text
Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7),
```

with candidate zero progressions `7n+3`, `7n+5`, and `7n+6`.  In this case there is a direct
explanation.  Sorting the product factors by residue class gives

```text
Q(q,q^7) Q(q^2,q^7) Q(q^3,q^7)
  = phi(-q) (q^7;q^7)_inf (q^14;q^14)_inf.
```

The last two factors are supported on multiples of seven, while
`phi(-q)=sum_n (-1)^n q^(n^2)` is supported modulo seven only at the quadratic residues
`0,1,2,4`.  Therefore the three quadratic nonresidues `3,5,6` vanish.

`RamanujanTau.MultiQuintuplePochhammer` defines the paper's one-variable specialization
`quintupleSpecialized p i = Q(q^i,q^p)` from five stabilized residue-class q-Pochhammer factors.
`RamanujanTau.MultiQuintupleP7` then proves the complete product collection

```text
quintupleSpecialized 7 1 * quintupleSpecialized 7 2 * quintupleSpecialized 7 3
  = phi(-q) (q^7;q^7)_inf (q^14;q^14)_inf
```

and transports the support argument to the actual product.  Thus all three infinite families
`7n+3`, `7n+5`, and `7n+6` are kernel-checked theorems, with no remaining specialization
interface and no appeal to numerical experimentation.

## Exact coefficient model

The papers use

```text
Q(z,q) = (z,q/z,q;q)_inf (q*z^2,q/z^2;q^2)_inf
       = sum_{n in Z} q^(n(3n-1)/2) z^(3n) (1-z*q^n).
```

For a canonical specialization `0 < i < p/2`, this becomes a genuine power series

```text
Q(q^i,q^p) = sum_{n in Z} (q^A(n) - q^B(n)),
A(n) = p*n*(3n-1)/2 + 3*i*n,
B(n) = A(n) + i + p*n.
```

The scanner enumerates precisely the finitely many bilateral terms that can contribute below
the requested bound and performs sparse convolution over the integers.  It does not use
floating point arithmetic.

The square completion behind the lattice approach is

```text
24*p*A(n) + (6*i-p)^2 = (6*p*n + 6*i-p)^2,
24*p*B(n) + (6*i-p)^2 = (6*p*n + 6*i+p)^2.
```

`RamanujanTau.MultiQuintupleVanishing` formalizes the denominator-free versions of these two
identities.  They turn equality of product exponents into preservation of a sum of squares,
which is the natural starting point for an affine sign-reversing involution.

`RamanujanTau.MultiQuintupleBilateralBridge` closes the coefficient interface exactly:

```text
coeff k (quintupleSpecialized p i) = quintBilateralCoeff p i k
```

for `0 < i` and `2*i < p`.  Its proof transports the completed formal quintuple product identity
through a finite positive-cone diagonal and identifies a common truncation with the five stabilized
Pochhammer factors.  No analytic convergence or unrestricted substitution of a negative Laurent
power into a formal power series is used.

## Reproducing the experiments

Published examples, checked through 160 complete progressions:

```bash
python3 scripts/quintuple_vanishing_scan.py known
```

Inspect the first counterexample and print its finite coverage certificate:

```bash
python3 scripts/quintuple_vanishing_scan.py candidate \
  --prime 71 --indices 1,4,14 --depth 120
```

Scan all pairwise-distinct isotropic triples for primes through 97:

```bash
python3 scripts/quintuple_vanishing_scan.py scan --max-prime 97 --depth 80
```

The reported zeros are finite experimental evidence unless separately proved.  A reported
non-hit with all residues covered is, by contrast, a valid finite disproof of the claim that
the product has some identically zero residue class.

## Scope and follow-up questions

The admissible Root–Vanishing classification is complete, including the
analytic bridge, coherent short-partner involution, integral lattice generation,
and exact root-target extraction. Its contrapositive guarantees that any
admissible residue without a root target has a finite nonzero coefficient
witness. The unrestricted converse remains false by the p=9 common-scale
counterexample.

The following questions go beyond the proved theorem:

1. **Quantitative first witnesses.** Does every admissible non-root residue
   have a nonzero coefficient by N≤⌊p/4⌋? The exact census through p≤2600
   finds no exception, but the universal bound is not proved.
2. **Earlier shell cutoffs.** Do the first-spanning or first-perfect,
   lattice-generating cutoffs already force a root target? Their existence
   bounds and finite scans are proved or checked separately; the completed
   converse does not establish rigidity at those particular cutoffs. Fixed
   four- and five-shell criteria are false at p=1439 and p=1523.
3. **Arbitrary lattice automorphisms.** Formalize the separate paper argument
   that every noncentral automorphism group in this prime-index setting
   contains a plane reflection. The completed converse constructs a suitable
   involution directly from vanishing and does not formalize that broader
   automorphism statement.
4. **Broader products.** Classify four-factor products and determine suitable
   criteria beyond distinct isotropic triples at prime modulus. Composite
   moduli and repeated indices have additional support mechanisms, so the
   admissible theorem cannot simply be extended by dropping its hypotheses.

These directions retain the useful experimental questions while separating
them from the now-proved universal admissible converse.

## Sources

- T. Y. Lam, K. H. Leung,
  [On vanishing sums for roots of unity](https://arxiv.org/abs/math/9511209),
  for the prime-weight semigroup; for an even antipodally closed sum at root
  order `2p`, weight `2p` is the first possible non-pairing threshold.
- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [The p-Dissection of a Product of Quintuple Products](https://arxiv.org/abs/2603.04666),
  especially the concluding triple-product examples.
- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [Vanishing Coefficients in Products of Quintuple Products](https://arxiv.org/abs/2606.06701),
  especially the affine lattice-involution method and the concluding triple/quadruple examples.
- B. Kane, D. Kim,
  [Theta series of ternary quadratic lattice cosets](https://doi.org/10.1007/s00029-025-01110-0),
  for the genus/spinor-genus/class decomposition of ternary coset theta series and the
  `p`-neighbor algorithm; it supplies the correct ambient theory but not the signed
  multiplicity-one statement required here.

## 2026-10-04: structure of the first witnesses, and why the Eisenstein route is closed

This historical experiment log predates the completed converse. Its scans
remain relevant to quantitative first-witness questions.

Four reproducible scans (`scripts/mq_*.py`; each takes `max_prime depth`) probe *how* non-root
residues fail to vanish.

**1. Parity alone does not certify nonvanishing.** (`mq_parity_scan.py 200 60`) Of 23,536 non-root
residues for `p ≤ 200`, the first nonzero coefficient is odd in 22,023 cases and `±2` in 1,513.
Some residues have *no* odd coefficient at all (e.g. `p=7,(1,2,3)`, residues `1,2,4`). There the
triple product vanishes identically mod 2 because of a sign-*preserving* fixed-point-free
involution, while the integer coefficients are `±2`. A pure mod-2 argument therefore cannot
prove the conjecture.

**2. The first occupied shell is almost always the witness.** (`mq_first_shell_scan.py 300 100`)
For 62,089 of 66,302 non-root residues (`p ≤ 300`), the smallest shell containing any Watson point
already has a nonzero signed coefficient. When it cancels, it contains exactly **two points of
opposite sign** in 4,197 of 4,213 cases (four points in the other 16).

**3. Cancelling pairs are short congruence vectors, and the witness is usually where their reflection
breaks.** Watson points are `m ∈ ℤ³` with `m_s ≢ 2 (mod 3)`, exponent `Σ(i_s m_s + p m_s(m_s−1)/6)`, sign
`+` for `m_s ≡ 0` and `−` for `m_s ≡ 1`, and `Y = 2pm + 6i − p` (`mq_convention_check.py` verifies this
against the series). Two facts are elementary:
* membership in a progression is linear, `K ≡ (i,j,k)·m (mod p)`, because `m(m−1)/6 ∈ ℤ`;
* if two Watson points lie on the same shell, `(Y−Y')·(Y+Y') = 0` gives `Δm·(i,j,k) ≡ 0 (mod p)`.
So cancelling pairs are short vectors of the index-`p` congruence lattice. For a reflection in `Δ` to be
integral on a whole progression, `|Δ|²` must divide 6, or divide `6p` when `Δ` is a projective lift. Short
roots are exactly the norm `p`, `2p` lifts.
(`mq_pair_reflection_scan.py 150 60`, `mq_pair_classify.py 200 60`) Every first-shell cancelling `Δ` in
the data is a non-lift (never a root). In 1,637 of 1,739 two-point cancellations (`p ≤ 200`) the first
nonzero coefficient is exactly at the first shell where the reflection in `Δ` stops matching points to
opposite-sign points. In the remaining 102 the failing shell is cancelled again by a different
coincidence. These are small-number events (2–4 points per shell); `mq_show_shells.py 13 1,3,4 5 4`
displays one. The tiny `Δ` (`|Δ|² | 6`) never re-cancel. **There is no hidden second mechanism:**
re-cancellations look exactly like random `±1` coincidences on sparse early shells, which is what a
random-sign model predicts.

**4. Every residue projection is a cusp form, so Siegel–Weil cannot help.** The Watson points form a
union of cosets of `(6pℤ)³`, determined by the local conditions `Y odd` (at 2),
`Y_s ≡ 6i_s (mod p)` (at p) and `Y_s ≡ ±p (mod 3)` (at 3). The sign depends only on the
3-adic data. At 3, negating one coordinate preserves the norm and the admissible 3-adic set but
flips the sign, so every signed local density at 3 vanishes. Hence the genus (Eisenstein) part of
every progression projection `F_r = Σ_{K≡r} c(K) q^K` is zero: each `F_r` is a weight-3/2 cusp form.
(`mq_cusp_check.py`) Numerically, along each progression `|Σ c(K)|` is 0.0004–0.01 of the point
count, while `Σ c(K)²` ≈ point count. This is the signature of a cusp form with pseudo-random signs.

**Consequences.**

* Nonvanishing for non-root residues cannot come from a local or Eisenstein obstruction. The
  then-conjectural equivalence concerns a family of weight-3/2 cusp forms (on a level divisible by
  `p²`) is nonzero exactly when no projective root exists. The natural tools are the Shimura
  correspondence and Waldspurger-type formulas, or the root-or-witness reduction already formalized.
* The data explain the small witness cutoff heuristically, and point 3 shows the algebraic
  "first-reflection-failure" route cannot by itself give a proof: early-shell coincidences are
  genuinely unstructured. Signs on a shell behave like independent
  `±1`, so a shell with an odd number of points can never cancel. Persistent cancellation beyond the
  first few occupied shells therefore needs a global symmetry, which the formal converse identifies
  with a short projective root.
* The census through `p ≤ 2600` (exact witnesses for every non-root residue, formal vanishing for every
  root residue) is already an exact verification of the root–vanishing equivalence for all those `p`.
  It relies on the exact Python scanner, not on Lean.
