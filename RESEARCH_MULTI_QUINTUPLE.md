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
(all 13 tuples with `sigma2=0` also vanish).  This points toward a finer projective invariant
on the conic `i^2+j^2+k^2=0`, together with the mod-6 coset data in Watson's bilateral sum.

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

The most useful next step is to classify the isotropic triples projectively.  For each orbit:

1. retain the mod-6 branch/sign data of the bilateral expansion;
2. search for an integral affine isometry of the completed-square lattice;
3. require it to preserve the target exponent and reverse the branch sign;
4. emit the matrix and translation as a certificate suitable for Lean.

This should reveal the missing invariant before attempting a universal theorem.

## Sources

- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [The p-Dissection of a Product of Quintuple Products](https://arxiv.org/abs/2603.04666),
  especially the concluding triple-product examples.
- T. Daniels, T. Huber, J. McLaughlin, D. Ye,
  [Vanishing Coefficients in Products of Quintuple Products](https://arxiv.org/abs/2606.06701),
  especially the affine lattice-involution method and the concluding triple/quadruple examples.
