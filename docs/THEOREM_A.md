# Theorem A: formalization boundary

Updated 2026-10-29. [Current status](STATUS.md) · [Research argument](BL_SHARPNESS_PROOF.md)

**The universal theorem is not yet formalized.** The new Lean development proves
the arithmetic and linear algebra of the ordinarity argument, including a
conditional reduction on actual power series. It does not supply the required
level-six modular-form theory or the Shimura correspondence. The independent
prime-29 all-power theorem remains complete.

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
| [WeightSix](../RamanujanTau/TheoremA/WeightSix.lean) | An exact integer matrix identity and the exclusion of a nonzero joint (4,9) eigenvector | The matrices' identification with actual Hecke operators is not formalized |
| [Reduction](../RamanujanTau/TheoremA/Reduction.lean) | `U_ne_zero_of_filtration_data` combines these results to conclude U_ℓ f ≠ 0 | Explicit hypotheses retain the filtration laws, the weight-six annihilator, and the U₂/U₃ eigenvalue formulas |

The conditional reduction is useful because its conclusion concerns the existing
Boylan–Webb coefficient-extraction operator on an actual power series. The
unproved modular inputs appear in its theorem statement; an axiom audit does
not discharge them.

## A simpler weight-six argument

In the classical basis (g(z), g(2z), h(z)), with g and h the normalized weight-six
newforms of levels three and six, the expected matrices are

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
The integer matrix certificate and this implication are both checked in Lean.

An identity over the fraction field also holds on any stable integral lattice,
by injectivity into the fraction-field space, and then on its reduction.
Applying this observation requires a proved comparison with the actual
weight-six space in characteristic ℓ; an integral old/new direct-sum
decomposition is not required.

The independent [PARI script](../scripts/frontier/pattern/weight_six.gp) recomputes
the classical rational matrices and the relation. It also checks the optional
full-space relation on M₆(Γ₀(6)) obtained by adding the factor
(U₂−I)(U₂−32I). That larger relation evaluates to −108864 at (4,9), whose
prime divisors are 2, 3, and 7. The full-space relation is a PARI check, not a
Lean theorem about modular forms.

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
   A concrete presentation of the level-six ring could be an alternative to
   developing a general theory of modular curves; that route has not been proved.
2. Identify the weight-six operator relation on the actual space and justify
   integral reduction/base change. Prove the bad-prime eigenvalue formulas for
   the stated Atkin–Lehner class. These discharge the remaining ordinarity inputs.
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
lake build RamanujanTau.TheoremA.Reduction
lake env lean scripts/audit/theorem_a.lean
gp -q -f scripts/frontier/pattern/weight_six.gp
```

The full build passed 9,136 jobs. The [dedicated audit](verification/theorem_a.axioms.txt)
checked twelve declarations with dependencies confined to `propext`,
`Classical.choice`, and `Quot.sound`. The integer matrix identity
is checked with `decide +kernel`; PARI is not part of Lean's trust boundary.
