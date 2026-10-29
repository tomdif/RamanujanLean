# Theorem A: formalization boundary

Updated 2026-10-29. [Current status](STATUS.md) · [Research argument](BL_SHARPNESS_PROOF.md)

**The universal theorem is not yet formalized. The classical weight-six
obstruction is now proved unconditionally.** Lean constructs three actual
eta quotient cusp forms at level six, proves their Fourier coefficients,
proves dimension three, and establishes (U₃+9)(U₂²+6U₂+32)=0 on the entire
classical cusp space. The identity also holds on its coefficient reductions.
The remaining ordinarity inputs are characteristic-ℓ filtration and lifting,
the newform eigenvalue formulas, and the Shimura/Boylan–Webb comparisons.
The independent prime-29 all-power theorem remains complete.

The next stage now has an actual integral weight-two basis, the relation
AC=B², descent to embedded coefficient rings, and a coefficient bound for
all nonnegative weights at level six. Extending these results to the graded
ring and proving the characteristic-ℓ filtration laws remain open.

## Targets

The paper argument has two linked targets for every prime ℓ ≥ 13:

1. Every normalized newform in weight ℓ−3 and level six with Atkin–Lehner signs
   (−(2/ℓ), −(3/ℓ)) has an ℓ-adic unit as its ℓ-th coefficient, at every prime
   above ℓ.
2. U_{ℓ²} is invertible modulo ℓ on
   S_{(ℓ−2)/2}(SL₂ℤ, ν_η^{−ℓ}).

Yang's Hecke-module correspondence and the integral q-expansion dictionary are
needed to pass from the first statement to the second. The subsequent
identification with Boylan–Webb's operators is needed for d_ℓ = 0.
None of those identifications is supplied by an abstract matrix calculation.

## What Lean now proves

All declarations below are in `RamanujanTau.TheoremA`.

| Source | Checked result | Boundary |
|---|---|---|
| [ThetaCycle](../RamanujanTau/TheoremA/ThetaCycle.lean) | `theta_cycle_weight_six`: a closed, nonnegative weight cycle starting at ℓ−3, with the stated step and drop laws, has weight six after four steps | Numerical bookkeeping; proving those laws for modular filtrations is separate |
| [Series](../RamanujanTau/TheoremA/Series.lean) | `U_eq_zero_iff_theta_cycle`: U_ℓ f = 0 iff θ^{ℓ−1}f = f; `U_theta_pow`: U_d θ^r = d^r θ^r U_d | Identities on actual infinite formal power series, over every field of characteristic ℓ |
| [Signs](../RamanujanTau/TheoremA/Signs.lean) | `theta_four_eigenvalue`: q⁴(q/ℓ)q^{(ℓ−5)/2} = q² in characteristic ℓ | Euler's criterion is proved through Mathlib; the original newform eigenvalue formula remains a modular input |
| [WeightSix](../RamanujanTau/TheoremA/WeightSix.lean) | An exact integer matrix identity and the exclusion of a nonzero joint (4,9) eigenvector | The actual-space identity is now proved in `WeightSixIdentity` |
| [Reduction](../RamanujanTau/TheoremA/Reduction.lean) | `U_ne_zero_of_filtration_data` combines these results to conclude U_ℓ f ≠ 0 | Explicit hypotheses retain the filtration laws, the weight-six annihilator, and the U₂/U₃ eigenvalue formulas |
| [BadPrimeCosets](../RamanujanTau/TheoremA/BadPrimeCosets.lean) and [BadPrimeForms](../RamanujanTau/TheoremA/BadPrimeForms.lean) | `cuspU` constructs U_p on Mathlib's actual `CuspForm (Γ₀(N)) k` for every prime p dividing nonzero N | Modularity, holomorphy, and vanishing at every cusp are proved, not assumed |
| [BadPrimeQExpansion](../RamanujanTau/TheoremA/BadPrimeQExpansion.lean) | `qExpansion_cuspU` and `cuspU_intertwines` identify the analytic operator with coefficient extraction; q-expansion is injective and the operators commute | Applies to every integral weight and every prime dividing the level, including 2 and 3 at level six |
| [IntegralCusp](../RamanujanTau/TheoremA/IntegralCusp.lean) | U_p preserves actual classical cusp expansions and their coefficient reductions | Does not assert that every Katz form lifts to a classical form |
| [ClassicalWeightSix](../RamanujanTau/TheoremA/ClassicalWeightSix.lean) | The polynomial on actual analytic operators intertwines with the series polynomial; a classical identity descends to arbitrary residue rings | The transfer is applied to the proved identity in `WeightSixIdentity` |
| [LevelSixCosets](../RamanujanTau/TheoremA/LevelSixCosets.lean) and [LevelSixNorm](../RamanujanTau/TheoremA/LevelSixNorm.lean) | Twelve explicit translates give an actual level-one form of twelve times the weight; this product detects zero | No assumed index or dimension formula |
| [CoefficientDecay](../RamanujanTau/TheoremA/CoefficientDecay.lean) and [LevelSixDecay](../RamanujanTau/TheoremA/LevelSixDecay.lean) | Vanishing below q^m gives norm decay of order m+3, using cusp periods 1, 6, 3, 2 | Analytic estimates for actual forms at every relevant cusp |
| [LevelSixSturm](../RamanujanTau/TheoremA/LevelSixSturm.lean) | A level-six cusp form of weight k vanishes if its coefficients below m vanish and k < m+3; `firstThree_injective` and `weightSix_finrank_le_three` follow | Unconditional analytic theorems; `WeightSixIdentity` subsequently proves dimension exactly three |
| [WeightSixCertificate](../RamanujanTau/TheoremA/WeightSixCertificate.lean) | Three actual weight-six cusp forms matching 27 coefficients through q^9 imply the full classical polynomial identity and its residue-ring versions | That input is discharged by `EtaQExpansion` and `WeightSixIdentity` |
| [LevelSixGenerators](../RamanujanTau/TheoremA/LevelSixGenerators.lean), [EtaSquared](../RamanujanTau/TheoremA/EtaSquared.lean), and [EtaQuotientModularity](../RamanujanTau/TheoremA/EtaQuotientModularity.lean) | Twenty-four explicit matrices generate Γ₀(6); exact η² word multipliers prove invariance and holomorphy of the three quotients | Matrix words and phase divisibility are kernel checked |
| [EtaCuspTransform](../RamanujanTau/TheoremA/EtaCuspTransform.lean), [EtaCuspDecay](../RamanujanTau/TheoremA/EtaCuspDecay.lean), and [EtaCuspForms](../RamanujanTau/TheoremA/EtaCuspForms.lean) | Exact cusp factorizations and positive rates prove vanishing at every cusp, giving actual Mathlib cusp forms | No cusp condition is assumed |
| [EtaFormalProducts](../RamanujanTau/TheoremA/EtaFormalProducts.lean) and [EtaQExpansion](../RamanujanTau/TheoremA/EtaQExpansion.lean) | Full analytic/formal q-expansion identities and kernel-checked integer coefficient tables through q⁹ | Uses the repo's existing analytic realization and truncated-series arithmetic |
| [WeightSixIdentity](../RamanujanTau/TheoremA/WeightSixIdentity.lean) | `classicalWeightSixAnnihilator_eq_zero`, `weightSixCoefficientEquiv`, `weightSix_finrank_eq_three`, and unconditional transfer to reduced cusp expansions | The actual classical obstruction is complete |
| [LiftedOrdinarity](../RamanujanTau/TheoremA/LiftedOrdinarity.lean) | Excludes (4,9) in reduced weight-six cusp expansions; `U_ne_zero_of_lifted_filtration_data` uses this proved obstruction | Filtration, lifting, and initial eigenvalues remain explicit inputs |
| [LevelSixModularSturm](../RamanujanTau/TheoremA/LevelSixModularSturm.lean) | The first k+1 coefficients determine every actual modular form of nonnegative integral weight k; dimension is at most k+1 | Includes noncuspidal forms; no ring presentation assumed |
| [EtaQuotientForms](../RamanujanTau/TheoremA/EtaQuotientForms.lean) and [WeightTwoForms](../RamanujanTau/TheoremA/WeightTwoForms.lean) | Finite phase and nonnegative cusp-rate certificates construct actual modular forms; three weight-two forms satisfy AC=B² | Zero cusp rates are allowed; holomorphy and boundedness at every cusp are proved |
| [WeightTwoQExpansion](../RamanujanTau/TheoremA/WeightTwoQExpansion.lean) | Integral Fourier expansions, coefficients through q⁹, and AC=B² over ℤ | The list certificate is kernel checked |
| [WeightTwoCoordinates](../RamanujanTau/TheoremA/WeightTwoCoordinates.lean) | Exact dimension three in weight two, reconstruction from three coefficients, and descent to any embedded coefficient ring | Generation in all even weights and modular filtration are separate obligations |

The conditional reduction is useful because its conclusion concerns the existing
Boylan–Webb coefficient-extraction operator on an actual power series. The
unproved modular inputs appear in its theorem statement; an axiom audit does
not discharge them.

## A simpler weight-six argument

In the classical basis (g(z), g(2z), h(z)), with g and h the normalized weight-six
newforms of levels three and six, the coefficient-certified matrices are

```text
U₂ = [-6   1   0]       U₃ = [9  0   0]
     [-32  0   0]            [0  9   0]
     [  0  0   4]            [0  0  -9].
```

They satisfy

\[
(U_3+9I)(U_2^2+6U_2+32I)=0.
\]

The polynomial takes the value 18·72 = 1296 at (4,9), a nonzero scalar in
every characteristic ℓ ≥ 5. Thus it excludes that eigenpair without an
eigenvector-lifting theorem or semisimplicity in characteristic ℓ.
The matrix certificate, actual classical operator identity, and exclusion on
coefficient reductions are all checked in Lean.

The descent step is now formalized by
`IsReducedCuspExpansion.weightSix_annihilator_unconditional`: the proved identity on the
actual complex cusp space holds on every cusp expansion over a coefficient
ring embedded in ℂ, and then after any coefficient-ring reduction. No integral
old/new direct-sum decomposition is required. Applying this to θ⁴F still
requires the weight-six lifting/comparison theorem. The classical polynomial
identity is no longer an input.

The independent [PARI script](../scripts/frontier/pattern/weight_six.gp) recomputes
the classical rational matrices and the relation. It also checks the optional
full-space relation on M₆(Γ₀(6)) obtained by adding the factor
(U₂−I)(U₂−32I). That larger relation evaluates to −108864 at (4,9), whose
prime divisors are 2, 3, and 7. The full-space relation is a PARI check, not a
Lean theorem about modular forms.

The Lean construction uses an even-exponent eta quotient basis:

\[
g(z)=\eta(z)^6\eta(3z)^6,\qquad v(z)=g(2z),\qquad
w(z)=\frac{\eta(z)^4\eta(6z)^{14}}{\eta(2z)^2\eta(3z)^4}.
\]

Its first three coefficient columns are (1,−6,9), (0,1,0), and (0,0,1),
so the determinant is one. The form used in the old/new coefficient table is
h = g + 10v − 18w. The name h specifies this linear combination; the proof
needs no separate newform-classification theorem. Its complete analytic
construction and first nine coefficients are checked in Lean.

The eta transformation proof uses 96 exact matrix-word certificates and 72
phase divisibility checks. Forty-eight cusp factorizations and 36 positive-rate
checks reduce cusp vanishing to the discriminant's analytic decay. The
[generator](../scripts/frontier/pattern/gen_eta_generator_data.py) supplies
untrusted integer data; Lean checks every required identity. The quotient's
Fourier series is obtained by multiplying by a formal unit, so no numerical
division or branch choice enters the coefficient certificate.

`classicalWeightSixAnnihilator_eq_zero_iff` proves the analytic identity is
equivalent to the full six-term coefficient relation, for all coefficients
of every form.

## The finite analytic certificate

`weightSix_eq_zero_of_first_three` proves that a weight-six cusp form is zero
if its q, q², and q³ coefficients vanish. The proof takes the product of
twelve translates. The cusp blocks of widths 6, 3, and 2 each contribute one
power of q; fourfold vanishing at infinity therefore gives decay of order
seven. Dividing the resulting weight-72 form by Δ⁷ produces a holomorphic
level-one form of weight −12, which vanishes by Mathlib's existing theorem.
The nonzero-product theorem then forces the original form to vanish.

The finite input to `weightSix_identity_of_coefficient_certificate` is:

| Form | q | q² | q³ | q⁴ | q⁵ | q⁶ | q⁷ | q⁸ | q⁹ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| g | 1 | −6 | 9 | 4 | 6 | −54 | −40 | 168 | 81 |
| v | 0 | 1 | 0 | −6 | 0 | 9 | 0 | 4 | 0 |
| h | 1 | 4 | −9 | 16 | −66 | −36 | 176 | 64 | 81 |

The three actual forms now have this table in Lean. The three-coefficient
bound proves they span and identifies the U₂/U₃ actions, giving the polynomial
identity on every form and then through integral reduction. PARI independently
checks the table; it is not part of the Lean proof.

## Integral weight-two coordinates

The three actual forms are

\[
A=\frac{\eta(2z)^{12}\eta(3z)^2}{\eta(z)^6\eta(6z)^4},\qquad
B=\frac{\eta(2z)^4\eta(6z)^4}{\eta(z)^2\eta(3z)^2},\qquad
C=\frac{\eta(z)^2\eta(6z)^{12}}{\eta(2z)^4\eta(3z)^6}.
\]

Their first coefficient columns, including the constant term, are
(1,6,15), (0,1,2), and (0,0,1). Thus a weight-two form with initial
coefficients c₀,c₁,c₂ equals

\[
c_0 A+(c_1-6c_0)B+(c_2-2c_1-3c_0)C.
\]

Lean proves this for the entire actual space M₂(Γ₀(6)), whose dimension
is exactly three. The reconstruction commutes with arbitrary ring maps.
`weightTwo_expansion_descent` proves the same expression over any ring
embedded in ℂ when the original expansion lies in that ring. The exponent
identity proves AC=B² analytically, and q-expansion injectivity transfers
it to the integer formal series.

These are ingredients for a proposed presentation of the even-weight ring
by A, B, C with relation AC=B². That full presentation is not yet proved.
The new coefficient bound and the leading terms 1, q, q² suggest proving
spanning by monomials in every even weight, then extending the repo's
level-one Hasse and Serre-derivative tools to these coordinates. Neither
the Hasse divisibility criterion nor the θ-filtration laws are assumed
by the weight-two theorems.

## Source checks and remaining work

Katz's 1977 paper, §II, theorem (1)–(2), gives θ's action at every cusp and
the filtration increase when the weight is prime to ℓ. Corollary (1) explicitly
sends holomorphic forms to cusp forms. The Hasse invariant has q-expansion one
at every cusp (§I), so removing Hasse factors preserves cusp vanishing.
This supplies the cited paper argument for cuspidality; it is not yet a Lean
construction. [Katz, author PDF](https://web.math.princeton.edu/~nmk/old/modformcharp.pdf).

The published Yang paper, Theorem 1 (p. 5), has the signs and quadratic twist
used in the research draft. Its correspondence is over characteristic zero;
the determinant argument needs integral Hecke lattices, not an assumed
integral isomorphism of the two spaces.
[Yang, published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A54F3A98B24022EB47D0FBBA2FAB37B4/S0027763000010916a.pdf/modular_forms_of_halfintegral_weights_on_sl2.pdf).

The next formal obligations are substantive:

1. Construct level-six modular forms in characteristic ℓ with q-expansions,
   Hasse invariant, filtration, and θ, and prove the laws used by the reduction.
   The explicit ring route now has integral weight-two coordinates and a
   coefficient bound in every weight. Proving generation in all even weights,
   the Hasse divisibility criterion, and the θ laws is the next step.
2. Prove the lifting/comparison needed for θ⁴F and the eigenvalue formulas
   for the stated Atkin–Lehner newform class. The actual classical weight-six
   forms, coefficient table, spanning argument, operator identity, and
   residue-ring transfer are complete.
3. Construct the half-integral-weight Hecke space and prove the required
   correspondence or an equivalent characteristic-polynomial identity.
4. Connect its reduction to X̄ on V and to the definition of d_ℓ. Prove the
   resulting decomposition and invoke a formal version of BW's bound.

This development does not prove universal sharpness, G4, or G6. In particular,
BW §6.1 reports an all-precision rank deficit at 607, but its listed computations
there reach 607 only at precision one. Repeated eigenvalues alone do not prove
non-cyclicity, and non-cyclicity modulo ℓ does not by itself settle every higher
precision. [Boylan–Webb, §§6.1–6.2](https://people.math.sc.edu/boylan/reprints/partition.pdf).

## Reproduce the checks

```sh
python3 scripts/frontier/pattern/gen_eta_generator_data.py
lake build RamanujanTau.TheoremA.LiftedOrdinarity RamanujanTau.TheoremA.WeightTwoCoordinates
lake env lean scripts/audit/theorem_a.lean
gp -q -f scripts/frontier/pattern/weight_six.gp
```

The [dedicated audit](verification/theorem_a.axioms.txt) checks 84 declarations,
including the actual eta cusp forms, coefficient identities, full weight-six
annihilator, exact dimension, integral reduction, and conditional ordinarity
reduction, plus the general coefficient bound and integral weight-two
construction and descent. Their dependencies are confined to `propext`, `Classical.choice`,
and `Quot.sound`. The integer certificates use `decide +kernel`; Python and
PARI are not part of Lean's trust boundary. See [status](STATUS.md#verification)
for the complete build record.
