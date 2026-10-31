# Theorem A: formalization boundary

Updated 2026-10-30. [Current status](STATUS.md) · [Research argument](BL_SHARPNESS_PROOF.md)

**Theorem A is proved unconditionally in Lean for every prime ℓ ≥ 13, including modularity of the
explicit Shimura lifts.** The dependencies are `propext`, `Classical.choice` and `Quot.sound`. The proof
is machine-checked and has not been reviewed by a human expert.

- *Integer weight.* `newform_coeff_ell_ne_zero`: a normalized T_ℓ-eigenform in
  S^{new}_{ℓ−3}(Γ₀(6)) with signs (−(2/ℓ), −(3/ℓ)) has ℓ-th coefficient nonzero under every
  ring map to a field of characteristic ℓ. `latticeT_det_not_dvd`: T_ℓ has determinant
  prime to ℓ on the integer U₂,U₃ sign lattice. The U₂/U₃ eigenvalues are derived from
  the Atkin–Lehner signs, and T_ℓ is built from Mathlib's actual trace.
- *Half-integral weight.* `ThetaLift.theoremA_unconditional`: U_{ℓ²} is injective modulo ℓ on
  S_{(ℓ−2)/2}(SL₂ℤ, ν_η^{−ℓ}). `ThetaLift.X_injective_unconditional`: the same for Boylan–Webb's
  X̄ = D̄Ū on V = Δ^t S_{k'}, by the proved dictionary `X_on_V`.
- *Modularity.* `ThetaLift.aadModularity`, for every prime ℓ ≥ 5: for each squarefree t ≡ −ℓ (mod 24),
  the explicit series Σ_n (Σ_{de=n} (d/t) d^{λ−1} (12/e) a(te²)) qⁿ is a modular form on Γ₀(6) of weight
  ℓ−3. This is Theorem 1.1 of [Ahlgren–Andersen–Dicks](https://arxiv.org/abs/2307.07438). The formal proof
  uses their theta kernel, with the changes recorded in the [blueprint](AAD_BLUEPRINT.md).

The proof does not use Yang's theorem. If U_{ℓ²}h ≡ 0, every lift is killed by U_ℓ modulo ℓ, so
ordinarity makes it vanish modulo ℓ. Triangularity gives a(te²) ≡ 0, and every index has the
form te². An earlier route through `YangCorrespondence` also remains in `HalfIntegral.lean`
(`theoremA`, `X_injective_on_V`), with the T_{ℓ²} formula checked exactly against PARI's newforms for
13 ≤ ℓ ≤ 41 ([script](../scripts/frontier/pattern/shimura_check.py),
[PARI](../scripts/frontier/pattern/sign_class_coeff.gp)).

The lift formula was tested with [lift_check.py](../scripts/frontier/pattern/lift_check.py) for
primes 13 ≤ ℓ ≤ 41 and up to five values of t. For ℓ ≤ 31 the first 30 coefficients lie in the
level-six cusp space, a proper subspace of ℂ³⁰. For ℓ = 37 and 41 that space already has rank 30,
so that run tests nothing. This is evidence, not a proof.

The corollaries are proved in [BLBound](../RamanujanTau/BLBound/Modules.lean), for every prime ℓ ≥ 13.
`D_image` is Lemma 2 of the research draft. `partition_bound` gives one monic χ ∈ ℤ[x] with χ(0) prime to ℓ
such that Σ_i [xⁱ]χ^m · p((ℓ^(b+2i) n + 1)/24) ≡ 0 (mod ℓ^m) for all b ≥ 2m−1. `chain_stable` writes each
term as a fixed combination of later terms, which is the partition form of b_ℓ(m) ≤ 2m−1. `d_ell_zero` gives a
space of reduced weight ℓ−1 cusp forms that contains D̄(M̄) and on which X̄ is bijective, which is the
condition d_ℓ = 0. The proof does not use Boylan–Webb's Theorem 1.2.

`Modules.lean` also states these in Boylan–Webb's own terms. `Lam` is Λ^odd(b,m), `bEll` is b_ℓ(m), defined as the
least odd b with X: Λ^odd(b,m) → Λ^odd(b+2,m) bijective, and `dEll` is d_ℓ of their (5.1). `bEll_le` proves
b_ℓ(m) ≤ 2m−1 and `dEll_eq_zero` proves d_ℓ = 0. `Vinv_eq` shows that the largest X̄-invertible subspace of S̄ is V̄,
and `Sbar_decomp` gives S̄ = V̄ ⊕ ker X̄. These definitions were written from our notes on the paper
([LIT_CHECK](LIT_CHECK.md)) and should be compared with the paper in review.
The independent prime-29 all-power theorem remains complete.

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
| [ThetaCycle](../RamanujanTau/TheoremA/ThetaCycle.lean) | `theta_cycle_weight_six`: a closed, nonnegative weight cycle starting at ℓ−3, with the stated step and drop laws, has weight six after four steps | Numerical bookkeeping; the required laws in the integral model are now proved in `BinaryFiltrationCycle` |
| [Series](../RamanujanTau/TheoremA/Series.lean) | `U_eq_zero_iff_theta_cycle`: U_ℓ f = 0 iff θ^{ℓ−1}f = f; `U_theta_pow`: U_d θ^r = d^r θ^r U_d | Identities on actual infinite formal power series, over every field of characteristic ℓ |
| [Signs](../RamanujanTau/TheoremA/Signs.lean) | `theta_four_eigenvalue`: q⁴(q/ℓ)q^{(ℓ−5)/2} = q² in characteristic ℓ | Euler's criterion is proved through Mathlib; the original newform eigenvalue formula remains a modular input |
| [WeightSix](../RamanujanTau/TheoremA/WeightSix.lean) | An exact integer matrix identity and the exclusion of a nonzero joint (4,9) eigenvector | The actual-space identity is now proved in `WeightSixIdentity` |
| [Reduction](../RamanujanTau/TheoremA/Reduction.lean) | `U_ne_zero_of_filtration_data` combines these results to conclude U_ℓ f ≠ 0 | Earlier conditional interface; `BinaryOrdinarity` now supplies the filtration and obstruction |
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
| [LiftedOrdinarity](../RamanujanTau/TheoremA/LiftedOrdinarity.lean) | Excludes (4,9) in reduced weight-six cusp expansions; `U_ne_zero_of_lifted_filtration_data` uses this proved obstruction | Earlier conditional interface; the full-space route below removes the filtration and lifting hypotheses |
| [LevelSixModularSturm](../RamanujanTau/TheoremA/LevelSixModularSturm.lean) | The first k+1 coefficients determine every actual modular form of nonnegative integral weight k; dimension is at most k+1 | Includes noncuspidal forms; no ring presentation assumed |
| [EtaQuotientForms](../RamanujanTau/TheoremA/EtaQuotientForms.lean) and [WeightTwoForms](../RamanujanTau/TheoremA/WeightTwoForms.lean) | Finite phase and nonnegative cusp-rate certificates construct actual modular forms; three weight-two forms satisfy AC=B² | Zero cusp rates are allowed; holomorphy and boundedness at every cusp are proved |
| [WeightTwoQExpansion](../RamanujanTau/TheoremA/WeightTwoQExpansion.lean) | Integral Fourier expansions, coefficients through q⁹, and AC=B² over ℤ | The list certificate is kernel checked |
| [WeightTwoCoordinates](../RamanujanTau/TheoremA/WeightTwoCoordinates.lean) | Exact dimension three in weight two, reconstruction from three coefficients, and descent to any embedded coefficient ring | Extended to every even weight below |
| [EtaQuotientQExpansion](../RamanujanTau/TheoremA/EtaQuotientQExpansion.lean) and [EvenWeightForms](../RamanujanTau/TheoremA/EvenWeightForms.lean) | A uniform actual eta family in weight 2n, with integral expansions of orders 0,…,2n and leading coefficient one | Exact transformation, cusp, and full q-expansion proofs |
| [EvenWeightCoordinates](../RamanujanTau/TheoremA/EvenWeightCoordinates.lean) | Dimension 2n+1, an integer inverse coefficient matrix, reconstruction and descent in every even weight | Reconstruction commutes with arbitrary ring maps |
| [EvenWeightProducts](../RamanujanTau/TheoremA/EvenWeightProducts.lean) | Basis products add indices; A,B,C generate, with unique monomials AᵃBᵇCᶜ, b < 2, in each weight | No assertion of independence across different weights after reduction |
| [LevelSixSerre](../RamanujanTau/TheoremA/LevelSixSerre.lean) and [EvenWeightSerre](../RamanujanTau/TheoremA/EvenWeightSerre.lean) | Actual Serre differentiation at all cusps; 12θ−kE₂ raises the integral model's weight by two over every commutative ring | Hasse divisibility and the θ-filtration laws are not inferred from closure alone |
| [BinarySeries](../RamanujanTau/TheoremA/BinarySeries.lean) and [BinaryModel](../RamanujanTau/TheoremA/BinaryModel.lean) | Homogeneous binary polynomials of degree 2n identify the actual weight-2n space and its integral model; evaluation is injective in each even degree, and a polynomial Serre operator matches the series operator | The two auxiliary integer series are not asserted to be odd-weight modular forms |
| [BinaryEisenstein](../RamanujanTau/TheoremA/BinaryEisenstein.lean) and [BinaryPullback](../RamanujanTau/TheoremA/BinaryPullback.lean) | Explicit E₄/E₆ polynomials, complete series identities over every ring, weight-preserving substitution, and no common projective zero in characteristic different from 2 and 3 | Finite integer certificates are promoted to full identities by the proved coefficient bound |
| [BinaryHasse](../RamanujanTau/TheoremA/BinaryHasse.lean) and [BinaryBaseChange](../RamanujanTau/TheoremA/BinaryBaseChange.lean) | Homogeneous Hasse and companion polynomials with expansions 1 and E₂; the companion is the Serre derivative; identical expansions in one weight class are Hasse-power multiples | Applies over every field of characteristic ℓ ≥ 5 |
| [HasseSeparation](../RamanujanTau/TheoremA/HasseSeparation.lean) | No common projective zero over an algebraic closure, and coprimality on both affine charts over the original field | Uses the repo's proved Igusa simple-root results and Ramanujan differential equations |
| [BinaryTheta](../RamanujanTau/TheoremA/BinaryTheta.lean) and [BinaryDivisibility](../RamanujanTau/TheoremA/BinaryDivisibility.lean) | The homogeneous theta numerator represents 12θ; Hasse divisibility is unchanged away from weights divisible by ℓ, and is forced at such weights; a Hasse factor is equivalent to lowering weight by ℓ−1 with unchanged series | Supplies the minimal-weight argument below |
| [BinaryFiltration](../RamanujanTau/TheoremA/BinaryFiltration.lean) and [BinaryFiltrationCycle](../RamanujanTau/TheoremA/BinaryFiltrationCycle.lean) | Least representing half-weight in one class, theta step/drop laws, and `theta_four_binaryRep` for a nonzero U_ℓ-kernel series in weight ℓ−3 | No cross-class Katz-filtration comparison is assumed |
| [BadPrimeModular](../RamanujanTau/TheoremA/BadPrimeModular.lean) | Actual U_p on the full modular-form space, coefficient extraction, and commutation | Includes noncuspidal forms at every integral weight and every prime dividing the level |
| [EtaTruncation](../RamanujanTau/TheoremA/EtaTruncation.lean) and [ModularWeightSixData](../RamanujanTau/TheoremA/ModularWeightSixData.lean) | General bounded eta products; coefficients through q¹⁸; kernel-checked 7×7 operator matrices and annihilator | Finite data is checked against the proved integral basis |
| [ModularWeightSixAction](../RamanujanTau/TheoremA/ModularWeightSixAction.lean) and [ModularWeightSixIdentity](../RamanujanTau/TheoremA/ModularWeightSixIdentity.lean) | Actual operator action, full-space annihilator over every coefficient ring, and exclusion of the (4,9) eigenpair in characteristic ℓ ≥ 13 | Avoids a cusp-lifting theorem for the fourth theta iterate |
| [BinaryOrdinarity](../RamanujanTau/TheoremA/BinaryOrdinarity.lean) | `U_ne_zero_of_binary_sign_eigenvalues` for every prime ℓ ≥ 13 | The U₂/U₃ eigenvalue formulas remain explicit inputs |
| [ReducedLevelSixOrdinarity](../RamanujanTau/TheoremA/ReducedLevelSixOrdinarity.lean) | `U_ne_zero_of_reduced_levelSix_sign_eigenvalues` for reductions of actual complex forms | Requires an embedded coefficient ring, a nonzero reduction, and the two prescribed eigenvalues |
| [TraceCosets](../RamanujanTau/TheoremA/TraceCosets.lean) | Explicit p+1 coset representatives compute Mathlib's trace from Γ₀(Mp) to Γ₀(M) | Any prime p not dividing M |
| [AtkinLehner](../RamanujanTau/TheoremA/AtkinLehner.lean) | `trace_formula`: Tr f = f + p^{2−k}U_p(f∣W); `IsNewSign.U_qExpansion`: U_p = −w p^{k/2−1} | Newness at p is the vanishing of Mathlib's trace, for a W-eigenform |
| [GoodHecke](../RamanujanTau/TheoremA/GoodHecke.lean) | T_ℓ on Γ₀(M) as the trace of f∣[ℓ 0;0 1]; `qExpansion_heckeT` is the classical formula | Modularity and all cusp conditions come from the trace |
| [SignLattice](../RamanujanTau/TheoremA/SignLattice.lean) | `latticeT_det_not_dvd`: T_ℓ is invertible modulo ℓ on the integer sign lattice | Unconditional, for every prime ℓ ≥ 13 |
| [NewClass](../RamanujanTau/TheoremA/NewClass.lean) | `newClass`, `newClass_U2/U3`, `newform_coeff_ell_ne_zero`, `newClass_mem_span`, `newClass_isRoot` | Unconditional; no multiplicity one or number-field integrality is used |
| [HalfIntegral](../RamanujanTau/TheoremA/HalfIntegral.lean) | `YangCorrespondence`, `latticeS_det_not_dvd`, `theoremA` | **Conditional on `YangCorrespondence`** |
| [BWDictionary](../RamanujanTau/TheoremA/BWDictionary.lean) | `X_on_V` (unconditional): X̄(Δ^t G) = Δ^t (q;q)^j Ξ(G); `X_injective_on_V` | The injectivity is **conditional on `YangCorrespondence`** |
| [LevelLowering](../RamanujanTau/TheoremA/LevelLowering.lean) | `exists_decomposition`, `exists_lowered`: a form on Γ₀(Mt) in powers of q^t comes from Γ₀(M) | Unconditional |
| [BLBound](../RamanujanTau/BLBound/Modules.lean) | `U_filtration`, `hasse_squarefree`, `D_image`, `exists_chi`, `partition_bound`, `chain_stable`, `bEll_le`, `dEll_eq_zero`, `Vinv_eq`, `Sbar_decomp` | Unconditional, ℓ ≥ 13 |
| [LiftReduction](../RamanujanTau/TheoremA/LiftReduction.lean) | `liftSeries`, `U_lift`, `lift_ell_dvd`, `theoremA_of_modularity`, `X_injective_of_modularity` | Reduction of Theorem A to `AADModularity`, which [Final](../RamanujanTau/ThetaLift/Final.lean) proves |

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
old/new direct-sum decomposition is required. The newer all-prime proof uses
the full modular-form space instead, so it does not need to show that θ⁴F
belongs to this reduced cusp space.

The independent [PARI script](../scripts/frontier/pattern/weight_six.gp) recomputes
the classical rational matrices and the relation. It also checks the optional
full-space relation on M₆(Γ₀(6)) obtained by adding the factor
(U₂−I)(U₂−32I). That larger relation evaluates to −108864 at (4,9), whose
prime divisors are 2, 3, and 7. This full-space relation is now also a Lean
theorem. Seven integral eta-basis elements, their coefficients through q¹⁸,
and the proved coefficient bound identify two kernel-checked 7×7 matrices
with the actual U₂ and U₃ actions. The relation descends to every coefficient
ring and excludes (4,9) in the complete weight-six model for ℓ ≥ 13.

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

## Every even weight and Serre differentiation

For 0 ≤ i ≤ 2n, the exponent vector of η² at dilations 1,2,3,6 is

\[
(-3n+2i,\;6n-4i,\;n-2i,\;-2n+4i).
\]

The resulting actual form Fₙ,ᵢ has expansion qⁱ times an integer unit with
constant coefficient one. The coefficient bound proves these forms span
M₂ₙ(Γ₀(6)); their triangular coefficient matrix has determinant one. Thus
the dimension is 2n+1, and the coordinates descend without division to
any embedded coefficient ring. Their series satisfy
Fₙ,ᵢ Fₘ,ⱼ = Fₙ₊ₘ,ᵢ₊ⱼ. Every basis element has the unique normal monomial
AᵃBᵇCᶜ with a+b+c=n, b < 2, and b+2c=i.

Two explicit integer series x,y satisfy x²=A, xy=B, y²=C. Lean identifies
x^(2n−i)y^i with Fₙ,ᵢ. Consequently the homogeneous binary polynomials
of degree 2n give the entire actual complex space and its integral model.
The single-weight q-expansion principle is valid over every commutative
ring, including all residue characteristics. This construction uses formal
Euler-product units; it makes no odd-weight modularity claim about x or y.

The Serre derivative is now an actual operator on level-six modular forms.
Cauchy's estimate proves boundedness of the derivative of any holomorphic
function bounded at infinity. Slash-equivariance applies this at every
cusp. After multiplication by 12, its expansion is 12θf−kE₂f.
Integral descent proves that this operator raises weight k to k+2 over
every coefficient ring. `binaryEv_binarySerre` identifies the corresponding
homogeneous polynomial operator with the series operator.

The level-one Eisenstein series now have proved binary expressions:

```text
E₄ = x⁴ + 228x³y + 270x²y² − 972xy³ + 729y⁴
E₆ = x⁶ − 522x⁵y − 9477x⁴y² + 18468x³y³ − 24057x²y⁴
     + 39366xy⁵ − 19683y⁶.
```

Kernel-checked integer coefficients and the coefficient bound establish these
identities for the complete series. Their discriminant factors as
E₄³−E₆² = 1728x³y(x−y)²(x−9y)⁶. Evaluating E₄ at the four possible factors
proves that E₄ and E₆ have no common nonzero point in characteristic ℓ ≥ 5.

Write H for the pulled-back Hasse invariant and J for its Serre companion,
to distinguish them from the weight-two generators A,B,C. Lean proves
that H and J have degrees ℓ−1 and ℓ+1 and complete expansions 1 and E₂.
Igusa's simple-root results imply that they have no common projective zero;
base change to an algebraic closure proves coprimality on both affine charts
over every field of characteristic ℓ ≥ 5.

For homogeneous P of degree k=2n, the polynomial
T(P)=H·δP+k·J·P has degree k+ℓ+1 and expansion 12θ(P). Lean proves:

- If k is nonzero in the coefficient field, H divides T(P) exactly when H divides P.
- If k is zero in the coefficient field, H divides T(P).
- For k ≥ ℓ−1, H divides P exactly when a homogeneous polynomial of degree
  k−(ℓ−1) has the same complete expansion.
- More generally, equal expansions in degrees k and k+m(ℓ−1) differ by multiplication by Hᵐ.

Homogenization proves the global divisibility statements from the chart
statements. The check H(1,0)=1 ensures that no factor at infinity is lost.
`binaryHalfFiltration` now defines the least representing half-weight in a
fixed class modulo (ℓ−1)/2. Hasse divisibility proves the theta step law
and that no weight drop occurs when the minimal full weight is nonzero
modulo ℓ. This construction makes no claim of independence between
different weight classes; the one-class result suffices for the cycle.

If U_ℓ f = 0, the series identity θ^{ℓ−1}f = f closes the cycle.
For a nonzero series initially represented in weight ℓ−3, the proved
bookkeeping forces the fourth iterate's minimal weight to be six.
Its U₂/U₃ eigenvalues become 4 and 9 by Euler's criterion. The full-space
weight-six annihilator then forces θ⁴f = 0, contradicting the closed cycle.
Integral descent transfers this argument to reductions of actual complex
modular forms. Every step of this argument is now checked in Lean.

## Source checks and remaining work

Katz's 1977 paper, §II, theorem (1)–(2), gives θ's action at every cusp and
the filtration increase when the weight is prime to ℓ. Corollary (1) explicitly
sends holomorphic forms to cusp forms. The Hasse invariant has q-expansion one
at every cusp (§I), so removing Hasse factors preserves cusp vanishing.
This supplies the cited paper argument for cuspidality. The current Lean proof
uses its explicit integral polynomial model and the full weight-six modular
space, so it does not require this general Katz construction.
[Katz, author PDF](https://web.math.princeton.edu/~nmk/old/modformcharp.pdf).

The published Yang paper, Theorem 1 (p. 5), has the signs and quadratic twist
used in the research draft. Its correspondence is over characteristic zero;
the determinant argument needs integral Hecke lattices, not an assumed
integral isomorphism of the two spaces.
[Yang, published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A54F3A98B24022EB47D0FBBA2FAB37B4/S0027763000010916a.pdf/modular_forms_of_halfintegral_weights_on_sl2.pdf).

The remaining formal obligations are:

1. The lower bound b_ℓ(m) ≥ 2m−1 for ℓ ≥ 29 remains open, apart from the proved threshold at ℓ = 29.

This development does not prove universal sharpness, G4, or G6. In particular,
BW §6.1 reports an all-precision rank deficit at 607, but its listed computations
there reach 607 only at precision one. Repeated eigenvalues alone do not prove
non-cyclicity, and non-cyclicity modulo ℓ does not by itself settle every higher
precision. [Boylan–Webb, §§6.1–6.2](https://people.math.sc.edu/boylan/reprints/partition.pdf).

## Reproduce the checks

```sh
python3 scripts/frontier/pattern/gen_eta_generator_data.py
lake build RamanujanTau.BLBound.Modules
lake env lean scripts/audit/theorem_a.lean
gp -q -f scripts/frontier/pattern/weight_six.gp
python3 scripts/frontier/pattern/shimura_check.py
python3 scripts/frontier/pattern/lift_check.py
python3 scripts/frontier/pattern/mu_sum.py
gp -q scripts/frontier/pattern/sign_class_coeff.gp
```

The [dedicated audit](verification/theorem_a.axioms.txt) checks 324 declarations,
including the actual eta cusp forms, coefficient identities, full weight-six
annihilator, exact dimension, integral reduction, and conditional ordinarity
reduction, plus the uniform eta basis, integral reconstruction, polynomial
model, actual and integral Serre operators, Eisenstein/Hasse comparison,
projective separation, global homogeneous divisibility, minimal-weight
theta-cycle laws, the full weight-six operator identity, all-prime
ordinarity on the prescribed eigenspace, the Atkin–Lehner and T_ℓ layers, the
sign-lattice determinant theorem, modularity of the lifts, and Theorem A. Their dependencies
are confined to `propext`, `Classical.choice`,
and `Quot.sound`. The integer certificates use `decide +kernel`; Python and
PARI are not part of Lean's trust boundary. See [status](STATUS.md#verification)
for the complete build record.
