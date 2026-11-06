# RamanujanLean

[![Repository checks](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanLean/actions/workflows/repository-checks.yml)

Lean 4 + Mathlib proofs in Ramanujan's mathematics: modular forms, partitions,
q-series, mock theta identities, and finite certificates for infinite arithmetic laws.

[Theorem catalog](docs/RESULTS.md) · [Current status](docs/STATUS.md) ·
[Multi-quintuple classification](RESEARCH_MULTI_QUINTUPLE.md#current-theorem) ·
[Finite certificates](docs/FINITE_ARITHMETIC.md) · [Documentation guide](docs/README.md)

The Lean package is named `RamanujanTau`; modules use `import RamanujanTau.…`.
Partition theorems are connected to Mathlib's actual `Nat.Partition` cardinalities.
Proofs use kernel-checked finite computations, without `sorry`, added axioms, or
`native_decide`. Explicit hypotheses in conditional theorems remain visible in
those theorems' statements.

## Selected results

| Area | Formalized result | Entry point |
|---|---|---|
| Ramanujan's τ | Multiplicativity, the Hecke recurrence, and the mod-691 congruence for the computable Euler-product coefficients | [TauModular](RamanujanTau/TauModular.lean) |
| Hasse–Weil via Stepanov | Character sums of squarefree polynomials over F_p are O(m²√p); Hasse's bound for elliptic curves up to the constant; Salié's Kloosterman bound | [Main](RamanujanTau/Stepanov/Main.lean), [Salié](RamanujanTau/Stepanov/Salie.lean), [write-up](docs/STEPANOV.md) |
| Rankin–Selberg | Σ_{n≤N} τ(n)²/n¹¹ = (3/π)(4π)¹²‖Δ‖²/11!·N + O(N^{3/5}) (Rankin 1939, exact exponent), via horocycle equidistribution, Karamata, and the theta functional equation with Perron for the error term. The 3/5 comes from Landau's method; its Γ-integral kernel bound is proved by a bent contour through the saddle point, using only \|Γ\| bounds. The ε is removed by a sharp bound for the top kernel and exact partial summation. The same holds for every level-one cusp form. The Rankin–Selberg theorem proper: Σ τ(n)²n^{−11−s} continues meromorphically to ℂ, its completion R*(s) = 2π^{−s}Γ(s)Γ(s+11)(4π)^{−s−11}ζ(2s)R(s) satisfies R*(1−s) = R*(s) with simple poles at 0, 1 (residues ∓‖Δ‖²); likewise E*(z,1−s) = E*(z,s) | [HoroIdent](RamanujanTau/EisensteinReal/HoroIdent.lean), [PowerSaving84](RamanujanTau/RankinError/PowerSaving84.lean), [write-ups](docs/EISENSTEIN_REAL.md), [error](docs/RANKIN_ERROR.md), [FE](docs/RANKIN_SELBERG_FE.md) |
| Rankin–Selberg for all level-one cusp forms | Σ_{n≤N}\|a_f(n)\|²/n^{k−1} ~ (3/π)(4π)^k‖f‖²/(k−1)!·N for every f ∈ S_k(SL₂(ℤ)), with explicit integer instances in weights 16–26 | [Main](RamanujanTau/RankinSelbergGeneral/Main.lean), [write-up](docs/RANKIN_SELBERG_GENERAL.md) |
| L(Δ,s) in the critical strip | Hecke's functional equation for Λ(s) = (2π)^{−s}Γ(s)L(Δ,s); absolute convergence for Re s > 13/2 without Deligne (Rankin 1939); the convexity bound \|L(Δ,6+it)\| ≪ (1+\|t\|)^{1/2+ε} by Phragmén–Lindelöf; all three for every level-one cusp form, with Hecke's functional equation Λ(f,k−s) = i^kΛ(f,s); the Euler product and non-vanishing of L(Δ,s) past 13/2, non-vanishing on the edge Re s = 13/2 itself (without Sym² or Deligne), so every nontrivial zero lies in the open strip 11/2 < Re s < 13/2, indeed in the de la Vallée-Poussin region 11/2 + c/log(|t|+2) ≤ Re s ≤ 13/2 − c/log(|t|+2) with no exceptional zero, and −L'/L is regular on Re s ≥ 13/2 and the prime number theorem for τ with de la Vallée-Poussin error, Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N), unconditionally (no Deligne); τ(p) > 0 and τ(p) < 0 each for infinitely many primes, unconditionally, indeed Σ_{τ(p)>0} p^{−β} = ∞ for β < 9/20 and #{p < x : ±τ(p) > 0} ≥ x^θ for arbitrarily large x (θ < 9/20), with a positive proportion of each sign under Deligne; L(Δ×Δ,1+it) ≠ 0 and L(Sym²Δ,1+it) ≠ 0 on the edge, and the Rankin–Selberg PNT Σ_{p<N} τ(p)² log p/p¹¹ ~ N; the Wiener–Ikehara theorem and the classical PNT ψ(x) ~ x are proved via a port of PrimeNumberTheoremAnd; for every normalized level-one eigenform, L(f,(k+1)/2+it) ≠ 0 for t ≠ 0 unconditionally (the real point t = 0 is a named hypothesis except for Δ), and the PNT for a_f(p) under Deligne for f, and Hardy's theorem: infinitely many zeros lie on the critical line Re s = 6, and on Re s = k/2 for every nonzero level-one cusp form with real coefficients; quantitatively, gaps between critical zeros of L(Δ,s) are ≪ t^{1/2+ε}, and there are ≫ T of them up to height T (Hafner 1983; the analogue of Hardy–Littlewood 1921 for ζ), also for every level-one cusp form with real coefficients; the Riemann–von Mangoldt formula N(T) = (T/π) log(T/2πe) + O(log T) for all zeros with 0 < Im ≤ T (for every nonzero level-one cusp form: (T/π) log(T/2πe·n₀) + O(log T), n₀ the first nonzero coefficient; and the zero-free region for every eigenform); on the critical line ∫₀ᵀ\|L(Δ,6+it)\|² ~ 2c·T log T with c Rankin's constant (Good 1982), and likewise for every nonzero level-one cusp form; cancellation in partial sums, Σ_{n≤x} τ(n) ≪ x^{59/10+ε} by Landau's method without Deligne, and Σ_{n≤x} τ(n) = Ω(x^{23/4}) (exact Ω-exponent, Landau–Mellin–Plancherel), with sign changes at the exact exponent, Σ τ(n) > c x^{23/4} and < −c x^{23/4} in every [X, 2X] for c < 1/(2π√2) (Ingham kernel on the truncated Voronoi formula); Cramér–Tong mean square ∫₁^X S(x)²x^{−25/2}dx ~ (B/4π²) log X with B = Σ τ(n)²n^{−25/2} and the unweighted Cramér limit X^{−25/2}∫₁^X S² → B/50π²; the truncated Voronoi formula S(x) ≈ x^{23/4}/(π√2) Σ_{n≤X^θ} τ(n)n^{−25/4}cos(4π√(nx) − π/4) in L² over [X, 2X]; all three also for every level-one cusp form of weight k with real coefficients (Cramér constant Σa(n)²n^{−k−1/2}/((4k+2)π²), Ω±(x^{(k−1)/2+1/4}) when a(1) ≠ 0); Wilton's bound Σ_{n≤M} τ(n)e(nα) ≪ M⁶ log M uniformly in α, and the functional equation of additive twists by a/q; **unconditional t-aspect subconvexity** \|L(Δ,6+it)\| ≪ (1+\|t\|)^{1/2−1/832000}, via a proved shifted-convolution bound Σ_{n≤N} λ(n)λ(n+h) ≪ (N+h)^{1−1/8000}h⁸ (two-point Poincaré series on Γ\(ℍ×ℍ), Kloosterman/Weil; exponent far from Good's 1/3) (every level-one cusp form: x^{(k−1)/2+2/5+ε}; with Deligne the known exponent is 35/6, Hafner–Ivić); the mean square (1/T)∫₀ᵀ\|L(Δ,σ+it)\|² → Σ τ(n)²n^{−2σ} on the full classical range σ > 6 (Carlson–Potter), and ∫₀ᵀ\|L(Δ,σ+it)\|² ~ C(σ)T^{25−4σ} for every σ < 6 | [HeckeConvex](RamanujanTau/HeckeConvex/Main.lean), [write-up](docs/HECKE_CONVEXITY.md), [general](docs/HECKE_CONVEXITY_GENERAL.md), [zeros](docs/HECKE_ZEROS.md), [edge](docs/EDGE_NONVANISHING.md), [zero-free region](docs/ZERO_FREE_REGION.md), [PNT](docs/TAU_PNT.md), [Wiener–Ikehara](docs/WIENER_IKEHARA.md), [PNT error](docs/TAU_PNT_ERROR.md), [signs/Sym²](docs/TAU_PNT_UNCOND.md), [sign counts](docs/TAU_SIGNS_QUANT.md), [eigenforms](docs/EIGENFORM_EDGE.md), [mean square](docs/MEAN_SQUARE.md), [σ > 6](docs/MEAN_SQUARE_FULL.md), [σ < 6](docs/MEAN_SQUARE_LEFT.md), [Hardy](docs/HARDY_ZEROS.md) ([general](docs/HARDY_ZEROS_GENERAL.md), [count](docs/HARDY_COUNT.md), [T/log log T](docs/HARDY_COUNT_LINEAR.md), [≫ T](docs/HARDY_COUNT_HAFNER.md) ([general](docs/HAFNER_GENERAL.md)), [critical mean square](docs/CRITICAL_MEAN_SQUARE.md), [lower](docs/CRITICAL_MEAN_SQUARE_LOWER.md), [asymptotic](docs/CRITICAL_MEAN_SQUARE_ASYMP.md) ([general](docs/GENERAL_CUSP_MOMENTS.md)), [zero count](docs/ZERO_COUNT.md), [Riemann–von Mangoldt](docs/ZERO_COUNT_RVM.md), [general](docs/GENERAL_ZEROS.md)), [partial sums](docs/TAU_PARTIAL_SUMS.md) ([59/10](docs/TAU_PARTIAL_SUMS_SHARP.md), [Ω](docs/TAU_OMEGA_PARTIAL.md), [Ω±](docs/TAU_OMEGA_PM.md), [mean square](docs/VORONOI.md) ([Cramér](docs/CRAMER_MEAN_SQUARE.md)), [Wilton/twists](docs/SUBCONVEXITY.md), [conditional subconvexity](docs/SUBCONVEXITY_COND.md)) |
| Weil's bound for τ | Weil's Kloosterman bound \|S(1,b;p)\| ≤ 2√p (Stepanov for Artin–Schreier curves, rationality of the Kloosterman L-function, amplification), hence τ(n) = O(n^{23/4+ε}) | [StepanovAS](RamanujanTau/StepanovAS/Main.lean), [write-up](docs/STEPANOV_ARTIN_SCHREIER.md) |
| Optimality of 11/2 | \|τ(n)\| ≥ c·n^{11/2} for infinitely many n, so τ(n) ≠ O(n^{11/2−δ}) for any δ > 0 (from the Rankin–Selberg lower bound); likewise \|a_f(n)\| ≥ c·n^{(k−1)/2} infinitely often for every nonzero level-one cusp form; with Landau's theorem on nonnegative Dirichlet series, every nonzero real level-one cusp form has coefficients of both signs infinitely often | [TauOmega](RamanujanTau/TauOmega/Main.lean), [write-up](docs/TAU_OMEGA.md), [Landau](docs/LANDAU_SIGNS.md) |
| Earlier τ exponents | τ(n) = O(n^{47/8+ε}) (Kloosterman 1927), the first bound below Hecke's n⁶, with Kloosterman's sum bound, Poincaré-series unfolding, and the cusp-form property all proved; then O(n^{35/6+ε}) via Salié's bound. Both are superseded by Weil's 23/4 above (Rankin's 29/5 lies in between and is not formalized) | [Kloosterman](RamanujanTau/TauBound/Unconditional.lean), [Salié](RamanujanTau/Stepanov/Salie.lean), [write-up](docs/TAU_SUBHECKE_BOUND.md) |
| Lehmer's conjecture, small n | τ(n) ≠ 0 for every 1 ≤ n < 214,928,639,999 (Lehmer 1947), from congruences for τ at a hypothetical least (prime) zero | [Lehmer1947](RamanujanTau/LehmerSmall/Lehmer1947.lean), [write-up](docs/LEHMER_SMALL_N.md) |
| Jensen polynomials of Riemann Ξ | Griffin–Ono–Rolen–Zagier Theorem 1: for every d, the Jensen polynomials of the Taylor coefficients of Ξ (from Mathlib's completed zeta) are real-rooted for all large n and converge to Hermite polynomials | [XiUncond](RamanujanTau/GORZXi/XiUncond.lean), [write-up](docs/GORZ_XI.md) |
| Turán inequalities for Ξ | γ(n)γ(n+2) ≤ γ(n+1)² for every n ≥ 0 (Csordas–Norfolk–Varga), so the degree-2 Jensen polynomials of Ξ are real-rooted for every n; the Csordas–Varga monotonicity is proved with kernel-checked interval cells | [CVMain](RamanujanTau/GORZXiEff/CVMain.lean), [write-up](docs/GORZ_XI_EFFECTIVE.md) |
| Jensen polynomials, every degree | Griffin–Ono–Rolen–Zagier for p(n): for every d the degree-d Jensen polynomial is real-rooted for all large n, and the renormalized polynomials converge to Hermite polynomials | [GORZ](RamanujanTau/GORZ/Main.lean), [write-up](docs/GORZ_PARTITIONS.md) |
| Jensen thresholds d = 6, 7 | The degree-6 Jensen polynomial of p is real-rooted for every n ≥ 610 and not at 609; degree 7: every n ≥ 908, not at 907 | [Final](RamanujanTau/JensenThreshold/Final.lean), [write-up](docs/JENSEN_THRESHOLDS.md) |
| Andrews' 1966 asymptotic | α(n) equals Andrews' printed sum over k ≤ √n of A_{2k}·I_{1/2} terms up to O(√n log n) (Andrews' own error term), via uniform bounds on f ± b near every root of unity | [SharpHb](RamanujanTau/MockCusp/SharpHb.lean), [write-ups](docs/ANDREWS_1966_ASYMPTOTIC.md), [cusps](docs/MOCK_THETA_CUSPS.md) |
| Dragonette's asymptotic | The coefficients of Ramanujan's f(q), i.e. N(0,2,n)−N(1,2,n), satisfy α(n) ~ (−1)^{n+1} e^{π√(n/6−1/144)}/(2√(n−1/24)), and (−1)^{n+1}α(n) > 0 for every n ≥ 1, so even- and odd-rank partitions alternate in which is more numerous | [Literal](RamanujanTau/Dragonette/Literal.lean), [sign](RamanujanTau/Andrews/Main.lean), [write-ups](docs/ANDREWS_DRAGONETTE.md), [sign proof](docs/ANDREWS_1966.md) |
| Ono–Weaver congruences | 13 ∣ p(157525693n+111247), 17 ∣ p(48037937n+1122838), and 81 Ono- and Atkin-type families for ℓ ∈ {13,17,19,23,29,31} and every hit prime Q < 500 (e.g. 19 ∣ p(41743n+669), 29 ∣ p(142477n+31778)), via Hecke equivariance of the Shimura lift; Atkin's 13 ∣ p(17303n+237) and 15 further twisted mod-13 families for Q < 500, via an explicit Hecke operator T(Q²) on η-multiplier forms and Gauss's sign theorem | [WeaverUnconditional](RamanujanTau/AtkinSporadic/WeaverUnconditional.lean), [all families](RamanujanTau/OnoWeaverMore/All.lean), [write-ups](docs/ATKIN_SPORADIC_CONGRUENCES.md), [table](docs/ONO_WEAVER_EXTENSIONS.md), [Atkin](RamanujanTau/AtkinSporadic/Atkin13Unconditional.lean), [T(Q²)](docs/HALF_INTEGRAL_HECKE.md) |
| Classical q-series | Jacobi's triple product, Euler's pentagonal theorem, and Jacobi's cube identity | [Theorem catalog](docs/RESULTS.md) |
| Nested radicals | The classical radicals equal 3 and 4; affine radicands with linear limits have a full classification, with exponential error bounds | [Classification](RamanujanTau/NestedRadicalClassification.lean) and [accuracy](RamanujanTau/NestedRadicalAffine.lean) |
| Partition congruences | Ramanujan's congruences modulo 5, 7, and 11, and their prime-power developments | [Theorem catalog](docs/RESULTS.md) |
| Rank and crank | Rank equidistribution modulo 5; crank equidistribution modulo 5, 7, and 11 | [Theorem catalog](docs/RESULTS.md) |
| Mock theta functions | The two Hickerson identities and the χ₀ identity with its partition-rank interpretation | [Method](MOCK_THETA_METHOD.md) |
| Partition asymptotics | Hardy–Ramanujan asymptotics, ordinary and colored partition entropy (including the 24-color reciprocal-discriminant coefficients), Rademacher's exact formula, and log-concavity for every n ≥ 26 | [Theorem catalog](docs/RESULTS.md) |
| Bosonic occupation model | Exact equivalence with colored partitions; finite Hilbert spaces with an occupation basis; 24-species charge-shell entropy grows as 4π√n with a specified vacuum offset | [Standalone module](RamanujanTau/BosonicOccupation.lean) |
| Algebraic oscillators | Creation and annihilation satisfy the canonical commutation relations; Hamiltonian eigenspaces have exactly the colored partition dimensions | [Operators](RamanujanTau/BosonicOscillator.lean) and [spectrum](RamanujanTau/BosonicSpectrum.lean) |
| Finite-shell adjoints | Factorial normalization gives square-root occupation coefficients; creation and annihilation are proved Hilbert adjoints between finite energy shells | [Normalization](RamanujanTau/BosonicNormalization.lean) and [adjoints](RamanujanTau/BosonicAdjoint.lean) |
| Primes 13, 17, 19, 23 | A single p-adic multiplier gives the partition recurrence at b = m modulo p^m | [OrdQuot.Atkin](RamanujanTau/OrdQuot/Atkin.lean) |
| Every power of 29 | One 29-adic multiplier gives the partition recurrence for every b ≥ 2m−1 modulo 29^m | [AllPowers29](RamanujanTau/FiniteArithmetic/AllPowers29.lean) |
| Sparse triple products | Persistent coefficient vanishing is equivalent to an exact projective root certificate for every admissible triple and canonical residue | [Full converse](RamanujanTau/MultiQuintupleFullConverse.lean) |
| Fixed four-factor classifications | At 41 the zero residues are 21,25,26,30; at 53 they are 29,31,36,38. Every other residue has a witness by N=5 and N=8 respectively | [41](RamanujanTau/MultiQuintupleFourFortyOneConverse.lean) and [53](RamanujanTau/MultiQuintupleFourFiftyThreeConverse.lean) |
| Infinite four-factor family | Four explicit progressions vanish for every parameter t≥0, at modulus 5184t²+720t+41; primality is not required | [All-parameter theorem](RamanujanTau/MultiQuintupleFourFamily.lean) |
| Four-factor reflection families | Infinite vanishing at p=m²+n² when 9 divides one of m,n,m−n,m+n, with explicit size and coprimality conditions; the sixteen maps have an exact branch-compatibility classification | [Uniform theorem](RamanujanTau/MultiQuintupleFourReflection.lean) and [map criterion](RamanujanTau/MultiQuintupleFourReflectionCriterion.lean) |
| A second four-factor family | Two permanent zero progressions at p=450t²+180t+43 for every t≥0; every even t gives a modulus outside all integer sums of two squares | [All-parameter theorem](RamanujanTau/MultiQuintupleFourBinaryFamily.lean) |
| Four-factor witness obstructions | Exact first witnesses N=7 at prime 17 and N=632 at prime 2521; any universal linear cutoff N≤cp for admissible four-tuples requires c≥7/17 | [Lower bound](RamanujanTau/MultiQuintupleFourWitnessBound.lean) and [2521](RamanujanTau/MultiQuintupleFourWitness2521.lean) |
| Canonical quintuple products | For every odd p ≥ 5, the full canonical product vanishes in every nonsquare residue class | [Canonical family](RamanujanTau/MultiQuintupleCanonical.lean) |
| Finite arithmetic | Finite operator relations imply recurrences for every iterate; applications include partition residues and exact weighted tilings | [Framework and examples](docs/FINITE_ARITHMETIC.md) |

**The admissible sparse triple classification is complete.** For prime p≠3,
0<i<j<k, 2k<p, p dividing i²+j²+k², and 0≤R<p, every coefficient of
`Q(qⁱ,qᵖ) Q(qʲ,qᵖ) Q(qᵏ,qᵖ)` at degrees pN+R vanishes if and only if
there is a projective root certificate with the required residue condition.
The theorem concerns the actual infinite products and assumes no additional
analytic, geometric, or generation statement. The published proof passed a
9,336-job full build and a 251-declaration axiom audit. See the
[exact statement and proof map](RESEARCH_MULTI_QUINTUPLE.md#current-theorem)
and [verification record](docs/verification/full_converse_lean.json).

**Four follow-up directions now have checked results.** The four-factor example
at 41 has a complete Lean classification and now extends to an infinite family
with four proved zero progressions at every parameter. The saved prime-607 minor is now identified with
actual partition data, so the stable module needs exactly 25 generators at every
precision m≥2 (`Rank607Final.rEll_607`); at m=2 the module is
(ℤ/607²)²⁴ ⊕ ℤ/607, with 24 free summands (`Rank607Structure.lamEquiv`), and at m=1
it is free of rank 24 (`Rank607One.rEll_607_one`). The threshold there is exact:
b₆₀₇(2) = 3 (`Rank607Threshold.bEll_607_two`). Five finite seed models have proved
survival for every iterate; their partition-operator identifications remain
open; the Hasse denominator modulo p² is now identified uniformly for every
prime p≥5. The quarter-prime witness conjecture passed 5,339 expanded tests; a
23-step delay at prime 103 is proved in Lean. The universal four-factor
classification, all-prime sharpness, and universal witness bound remain open.
See the [four-direction status](docs/STATUS.md#four-direction-follow-up-2026-11-01).

**The four-factor search now reaches a different quadratic family.** Lean proves
infinite vanishing at `p=2m²+n²` under explicit hypotheses, including an
unconditional family starting at 43. Infinitely many of these moduli cannot
occur in the earlier `m²+n²` family. Separately, Lean now proves a first
nonzero coefficient at N=632 for prime 2521, beyond ⌊2521/4⌋=630. A stronger
example at prime 17 has its first witness at N=7; any universal four-factor
linear bound must therefore allow c≥7/17, about 0.412. Sufficiency of that
constant is not claimed. The original triple-product conjecture remains open. See the
[theorem and counterexample](RESEARCH_MULTI_QUINTUPLE.md#a-second-quadratic-family-beyond-sums-of-two-squares).

**The prime-29 starting threshold is exact.** For every m ≥ 1 and positive B,
a scalar multiplier works for all admissible partition progressions from
b = B onward modulo 29^m if and only if B ≥ 2m−1.
[Complete29](RamanujanTau/FiniteArithmetic/Complete29.lean) proves this for
actual partition counts; the full build and expanded axiom audit passed.
[Complete31](RamanujanTau/FiniteArithmetic/Complete31.lean) proves the same threshold at ℓ = 31.
[ExactThreshold](RamanujanTau/FiniteArithmetic/ExactThreshold.lean) translates both into
Boylan–Webb's own invariant: b₂₉(m) = b₃₁(m) = 2m−1 for every m ≥ 1
(`Exact29.bEll_29`, `Exact31.bEll_31`), where Boylan–Webb computed b₂₉ for m ≤ 3.
The same holds at the four rank-two primes 37, 41, 43, 47 (`Rank2At37.bEll_37`, …), by a
second-order error recurrence and one packed mod-ℓ² kernel evaluation per prime
([Rank2Packed](RamanujanTau/FiniteArithmetic/Rank2Packed.lean)); Boylan–Webb computed these only for m ≤ 2.
It also holds at 53 and 59 (`RankSAt53.bEll_53`, `RankSAt59.bEll_59`), where the error is a
vector moved by a 2×2 matrix ([RankSPacked](RamanujanTau/FiniteArithmetic/RankSPacked.lean)), and at every
prime 61 ≤ ℓ ≤ 139 (`RankRAt61.bEll_61`, …, `RankRAt139.bEll_139`) by an order-r version
([RankRPacked](RamanujanTau/FiniteArithmetic/RankRPacked.lean)). So b_ℓ(m) is known for every m at
every prime 13 ≤ ℓ ≤ 139. (All certificates through 139, including `RankRAt137` and `RankRAt139`, compiled in the
2026-11-04 full build.)
At ℓ = 13, 17, 19, 23 the threshold is smaller:
[SmallThreshold](RamanujanTau/FiniteArithmetic/SmallThreshold.lean) proves
b_ℓ(m) ≤ 2⌊m/2⌋+1 for every m, and b_ℓ(2) = b_ℓ(3) = 3;
[SmallThresholdFive](RamanujanTau/FiniteArithmetic/SmallThresholdFive.lean) adds b_ℓ(4) = b_ℓ(5) = 5, and
[AtkinExact](RamanujanTau/FiniteArithmetic/AtkinExact.lean) proves b_ℓ(m) = 2⌊m/2⌋+1 for every m:
the Atkin–O'Brien index b = m is exact at every precision (`ExactAtkin13.exact`, …), also stated for
partition numbers in [AtkinExactPartition](RamanujanTau/FiniteArithmetic/AtkinExactPartition.lean).
See the [verification record](docs/STATUS.md#verification).

Work on the proposed all-prime Theorem A now proves that, for every prime
ℓ ≥ 13, U_ℓ cannot kill a nonzero reduced level-six form of weight ℓ−3
with the two prescribed U₂/U₃ eigenvalues. This applies to reductions of
actual complex modular forms over embedded coefficient rings. Lean proves
the integral polynomial model, Hasse divisibility, minimal-weight theta-cycle
laws, and a full weight-six operator identity; no filtration or lifting
hypothesis remains in this result.
The eigenvalues are now derived from the Atkin–Lehner signs, using Mathlib's
actual trace. So every normalized T_ℓ-eigenform in the class has a unit ℓ-th
coefficient above ℓ, unconditionally. Injectivity of U_{ℓ²} on the
half-integral-weight space, and of Boylan–Webb's X̄ on V, is also proved
unconditionally, with a formal proof of modularity of the explicit Shimura lifts
(Ahlgren–Andersen–Dicks) by a theta kernel. It follows that b_ℓ(m) ≤ 2m−1 for every
prime ℓ ≥ 13 and that d_ℓ = 0, in the partition case of the Belmont–Lee–Musat–Trebat-Leder
conjecture. These proofs are machine-checked and have not been reviewed by a human expert.
See the [precise boundary](docs/THEOREM_A.md).

## Build and verify

With Lean's `elan` toolchain manager installed:

```sh
git clone https://github.com/tomdif/RamanujanLean.git
cd RamanujanLean
lake exe cache get
lake build
```

[lean-toolchain](lean-toolchain) selects Lean `v4.30.0-rc2`.
[lake-manifest.json](lake-manifest.json) pins Mathlib; keep it when reproducing a
build. A Mathlib cache download does not include this project's certificates.
Fresh certificate checks can take substantial time and memory; later builds
reuse the compiled proofs. Some certificates are memory-heavy: for example `GORZXiEff.CVData*` peaks near 9 GB and
each `RankRAt*` packed certificate can need up to about 16 GB. The multi-quintuple proof includes eight stable
small-prime certificate blocks; [regeneration commands](docs/FINITE_ARITHMETIC.md#multi-quintuple-classification-certificates)
are documented separately.

After a successful build, run the theorem audits and a recurrence demonstration:

```sh
lake env lean scripts/audit/atkin_obrien_closure.lean
lake env lean scripts/audit/finite_arithmetic.lean
lake env lean scripts/audit/theorem_a.lean
lake env lean scripts/audit/multi_quintuple.lean
lake env lean scripts/audit/four_directions.lean
lake env lean scripts/audit/four_family.lean
lake env lean scripts/audit/four_plane.lean
lake env lean scripts/audit/four_reflection.lean
lake env lean scripts/audit/four_binary.lean
lake env lean scripts/audit/four_witnesses.lean
lake env lean scripts/audit/nested_radical.lean
lake env lean scripts/audit/nested_radical_affine.lean
lake env lean scripts/audit/celebrated_targets.lean
lake env lean --run scripts/finite_arithmetic/demo.lean 1000000000000
```

A full root `lake build` (9,699 jobs, base `f3be2fe`) completed on 2026-11-04 after the 2026-11-03/04 campaign,
including the `RankRAt137` and `RankRAt139` certificates; `scripts/audit/celebrated_targets.lean` then reported
only `propext`, `Classical.choice`, `Quot.sound` for all 70 audited declarations. Building from scratch is
memory-heavy: the packed `RankRAt*` certificates peak near 21 GB each and `GORZXiEff.CVData*` near 9 GB, so build
those modules one at a time on smaller machines. See [Current status](docs/STATUS.md#verification).

The audits report axiom dependencies. The finite-arithmetic audit also checks
small counting values and an enormous recurrence exponent. The expected axiom
set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

Fast repository checks are separate from Lean verification:

```sh
python3 scripts/check_repository.py
python3 scripts/boylanwebb/check_cert29_error.py
```

GitHub's **Repository checks** workflow runs these lightweight checks. It does
not substitute for `lake build` or the Lean axiom audits.

## Research and contributions

The [documentation guide](docs/README.md) distinguishes current results from
historical plans, numerical experiments, and proposed paper arguments.
Current open work includes efficient high-precision seed computation, a uniform
(all-prime) proof of Boylan–Webb sharpness, and extensions beyond
the proved admissible sparse triple multi-quintuple classification, such as
four-factor products and quantitative first-witness bounds. The
[four-factor results](RESEARCH_MULTI_QUINTUPLE.md#a-second-quadratic-family-beyond-sums-of-two-squares)
now include families at both m²+n² and 2m²+n². Complete fixed-product coefficient
classifications are proved at 41 and 53; infinite zero progressions are also
proved at 43 and 97. Weil's exponent 23/4 is the best formalized τ bound;
Deligne's 11/2 is not formalized here, and Lehmer's conjecture remains open.

See [CONTRIBUTING.md](CONTRIBUTING.md) for proof, certificate, and documentation
conventions. The project is [MIT licensed](LICENSE).
