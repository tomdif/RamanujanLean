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

There is no third common-scale mechanism.  Conditional on the remaining admissible primitive
rigidity statement, the second clause is equivalent to a primitive projective-root target, giving
a formal end-to-end scaled classification.

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
local support gaps from the genuine primitive cancellation problem.  The corrected frontier is
therefore explicitly restricted to prime, pairwise-distinct, isotropic triples and canonical
residues; `AdmissibleRootVanishingRigidity` records the only remaining converse statement.
The scanner now derives the signed lattice reflection and residue from these formulas rather than
searching over all automorphisms.  An exact sweep through `p<=251` checked 162 reflective classes:
every predicted residue had the root-specific affine certificate and was an observed zero, with
zero mismatches.  The sweep remains finite evidence for the proposed converse classification; the
forward coefficient progression is now a formal theorem for arbitrary parameters satisfying the
root and target hypotheses.

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
be sufficient, and the missing problem is now to manufacture enough of them—or prove an equivalent
spectral multiplicity-one statement—from the persistent progression identity.
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
closed, without axioms.  The reverse Root--Vanishing direction now has exactly one remaining claim:

1. **Spectral coherence:** persistent vanishing of the top Walsh component forces one coherent
   rational orthogonal involution of the eight cosets.

Parity noninjectivity explains why this is genuine extra content: a single scalar Walsh identity
does not formally determine all eight theta components.  The remaining breakthrough target is a
rigidity or multiplicity-one theorem for the two parity unions along the selected progression.

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
triple quintuple product.  The remaining claim can therefore be attacked as nonvanishing of one
explicit character theta component.  This makes finite Weil transforms at `3` and `p`, Hecke
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
alternatives carry finite certificates.  Consequently an effective geometry-of-numbers or modular
bound for the first nonzero witness would prove the full conjecture without promoting one Walsh
projection to eight component identities.

The new exact command

```bash
python3 scripts/paley_spinor_scan.py witness-scan --max-prime 2000 --depth 512
```

checks the certificate dichotomy residue by residue.  Its current census is

```text
projective classes                                     11,546
residue problems                                   14,991,476
projective-root certificates                            3,498
finite nonzero coefficient witnesses               14,987,978
latest first witness progression index                    389
violations of N <= p/4                                      0
unresolved residues / root-nonzero conflicts             0 / 0
```

This remains bounded evidence, not a universal cutoff theorem.  Its significance is that the
remaining theorem now has a falsifiable, certificate-complete computational form rather than only
an infinite spectral formulation.  The cleanest surviving conjectural bound is now explicit:

```text
if no projective root targets R, then some nonzero coefficient occurs with N <= floor(p/4).
```

`AdmissibleQuarterCutoffRootOrProductWitness` formalizes exactly this finite target, and
`admissibleRootVanishingRigidity_of_quarterCutoff` proves that it closes corrected rigidity for
each datum.  The scan reports reflective and nonreflective witness profiles separately, exact
relative maxima, and any quarter-bound violations; none occur through `p<=2000`.  This empirical
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
rigidity conjecture.  The corrected Poisson route is now sharply separated into two remaining
steps: prove spanning-shell rigidity, and formalize the analytic bridge from persistent primal
vanishing to cancellation on every complete dual shell.  Together with `rho_span <= 3p^2`, those
steps would yield a universal finite Root--Vanishing decision theorem.

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
Perfect-Generating Phase Rigidity (remaining finite lemma).
Aggregate cancellation through the first perfect, lattice-generating supported cutoff
is induced by one phase-reversing linear pairing of its vectors.
```

Once that pairing is obtained, the proved perfect-set theorem forces it to be orthogonal and the
proved generators force it to preserve the full projective dual lattice.  Involutive phase reversal
then lands exactly in the already completed Householder/projective-root classification.  Thus the
dual frontier is no longer an unspecified infinite rigidity problem: it is the finite promotion
from an exact cyclotomic multiset equality to one coherent linear pairing.  The new
`dual-perfect-scan` tests the strengthened cutoff exactly.

The exact reconstruction census through `p<=1500` reports

```text
projective classes                                  6,877
residue problems                                6,763,985
missing or incomplete perfect cutoffs                    0
perfect-shell/root-target mismatches                    0
coherent phase-reversing maps                         2,361
nonunique vector phase pairings                           0
nonlinear/incoherent pairings                             0
nonorthogonal recovered maps                             0
noninvolutive recovered maps                             0
dual-lattice preservation failures                       0
signed-Householder/root-map mismatches                    0
```

The largest perfect prefix uses 35 shells, at `p=1483`, and the largest observed perfect-shell
norm is `501p`, at `p=1489`.  These are bounded exact results, not the universal phase-pairing
lemma.  They do show that the proposed finite promotion is not merely compatible with the zero
sets: it reconstructs the already formalized root involution exactly in every tested case.

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
vanishing theorem, exact shell-balance converse, imprimitive counterexample, ternary-character theta
normal form, and the converse
construction from a projective-root certificate to a coherent involution are now implemented.
For the corrected prime/distinct/isotropic problem, the proof frontier is:

1. prove either of the following equivalent statements:
   - spectral coherence: persistent vanishing of the parity Walsh component supplies one
     noncentral rational orthogonal involution acting on the full affine residue fiber; or
   - effective separation: every residue without a projective-root target has a finite nonzero
     coefficient witness, ideally below an explicit geometry-of-numbers or modular bound; or
   - spanning-shell rigidity: prove that common Poisson-dual cancellation through the first shell
     whose supported vectors span `Q^3` forces a projective-root target.  The stopping norm exists
     and is at most `3p^2` by the proved scalar-zero spanning certificate; or, for the structurally
     stronger route, prove coherent phase matching through the first perfect and lattice-generating
     cutoff, whose existence is proved by norm `6p^2`.

The rational three-dimensional classification is now proved: every such noncentral orthogonal
involution is a Householder reflection or its negative.  The arithmetic sequel now excludes the
two integral signed-permutation norms, extracts the short projective lift, selects its mod-three
branch, and proves the exact target law; the converse builds the coherent involution back from that
data.  Hence the one remaining item is a sharply isolated ternary theta-coset spectral problem,
proved equivalent—not merely sufficient—to corrected rigidity.  The forward Root--Vanishing
direction is closed.  The finite-witness normal form shows that it is enough to prove an effective
separation bound for non-root residue classes; the exact census through `p<=2000` gives no exception
through progression index 512 and in fact finds every first witness by index 389.  The
original unrestricted biconditional is false by the `p=9` theorem above.  In the corrected
prime/distinct/isotropic regime, the missing reverse implication must recover a structural,
progression-wide cancellation symmetry.  The ternary-character normal form now identifies the
precise scalar theta lift whose kernel must be classified; current ternary lattice-coset theta
theory decomposes such series but does not automatically turn one signed character projection into
a termwise affine isometry.  The exact dual-shell census supplies a third finite normal form, but
the counterexamples at `p=1439` and `p=1523` prove that four- and five-shell cutoffs are not
universal.  Their low shells remain rank-deficient, while the first spanning shell detects the
false zero.  The supported-spanning theorem bounds that adaptive shell by `3p^2`; the remaining
dual problem is the colored ternary rigidity implication at this first full-rank threshold.  The
perfect-set refinement already proves that six norm tests force orthogonality and that a bounded
supported set generates the full dual lattice, leaving coherent phase matching as the precise
finite combinatorial obstruction.

## Sources

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
