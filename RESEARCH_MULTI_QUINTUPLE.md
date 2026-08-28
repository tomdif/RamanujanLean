# Multi-quintuple-product coefficient vanishings

## Status

This track now contains a proved infinite family as well as an open classification problem.
The exact coefficient scanner in `scripts/quintuple_vanishing_scan.py` reproduces all five
examples reported in the March and June 2026 papers and tests proposed extensions.

## Main theorem: the all-canonical infinite family

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

The remaining experimental problem below concerns *sparse* products with only three or four
factors.  The all-canonical theorem does not classify those sparse vanishings.

## Breakthrough candidate: the reflective-lattice criterion

For a distinct isotropic triple `(i,j,k)`, define the index-`p` ternary lattice

```text
L_(p;i,j,k) = {(x,y,c1*x+c2*y+p*z) : x,y,z in Z},
c1 = -i/k (mod p),  c2 = -j/k (mod p),
```

with the ordinary sum-of-three-squares norm.  Solving a target residue condition in the
three bilateral quintuple sums produces this homogeneous lattice, together with eight
inhomogeneous cosets indexed by the bilateral branch choices.

The data now supports the precise conjecture:

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
projective lift.  What remains conjectural as a general theorem is the extra classification step
saying that every noncentral automorphism group contains such a primitive rational reflection.
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

This is an exact power-series proof, not a scan.  More generally, the same module proves an
imprimitive-scale family: if a common factor `g` divides the modulus and all three indices but
does not divide `R`, the entire `pN+R` progression vanishes by support.  The corrected frontier is
therefore explicitly restricted to prime, pairwise-distinct, isotropic triples and canonical
residues; `AdmissibleRootVanishingRigidity` records that statement.
The scanner now derives the signed lattice reflection and residue from these formulas rather than
searching over all automorphisms.  An exact sweep through `p<=251` checked 162 reflective classes:
every predicted residue had the root-specific affine certificate and was an observed zero, with
zero mismatches.  The sweep remains finite evidence for the proposed converse classification; the
forward coefficient progression is now a formal theorem for arbitrary parameters satisfying the
root and target hypotheses.

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

## Next sparse-product proof target

The projective classification, primitive-reflection converse, universal positive and negative
projective branch matching, coefficient bridge, finite cancellation assembly, explicit `p=71`
and `p=79` certificate transports, projective target formulas, and uniform projective-root-to-
vanishing theorem, exact shell-balance converse, and imprimitive counterexample are now
implemented.  For the corrected prime/distinct/isotropic problem, the proof frontier is:

1. show that every noncentral automorphism group of the index-`p` congruence lattice contains a
   primitive rational Householder reflection, so that `MultiQuintupleRootConverse` applies;
2. prove a rigidity theorem on the cancellation side showing that every persistent admissible
   sparse-triple vanishing supplies a noncentral lattice automorphism, or identify another
   non-reflective mechanism.

The first item is a sharply isolated existential arithmetic root-system problem.  The forward
Root--Vanishing direction is closed.  The original unrestricted biconditional is false by the
`p=9` theorem above.  In the corrected prime/distinct/isotropic regime, the missing reverse
implication must recover a structural, progression-wide cancellation symmetry; current ternary
lattice-coset theta theory decomposes such series but does not turn an equality of shell counts
into a termwise affine isometry.

## Sources

- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [The p-Dissection of a Product of Quintuple Products](https://arxiv.org/abs/2603.04666),
  especially the concluding triple-product examples.
- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [Vanishing Coefficients in Products of Quintuple Products](https://arxiv.org/abs/2606.06701),
  especially the affine lattice-involution method and the concluding triple/quadruple examples.
