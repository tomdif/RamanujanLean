# Cylindric positivity and black hole research

Research status, 2026-11-03. Exact computations verify 520 nontrivial Warnaar
polynomials, including 492 for non-balanced profiles, with no negative
coefficients. Six Lean lemmas establish the local normalized-slice construction.
The full transfer identity and positivity for every entry bound remain unproved
in Lean. A separate source review identifies reusable estimates in the local
`unifiedtheory` checkout and the missing connection to actual black-hole
coefficient counts.

## Existing results and the research target

The October 7 revision of Huang, Lau and Ono reports an unconditional Lean
formalization of the HJO identities. Its positivity result covers balanced
coprime profiles. The broader positivity conjecture for arbitrary profiles is
the target here. See the [current paper](https://arxiv.org/abs/2609.20567),
[positivity discussion](https://arxiv.org/html/2609.20567v2#S1.SS1), and
[upstream solution](https://github.com/AxiomMath/HJO/blob/main/Solution/Basic.lean).

The October 29 [rank-three paper](https://arxiv.org/abs/2610.40079) proves
bivariate sum expressions and advances the Warnaar and Kanade–Russell
conjectures. The exploratory computations here start at rank four. No novelty
claim is made for the transfer construction or the computed examples.

For a profile `c` of rank `r` and positive level `d=sum(c)`, use the outgoing
convention `lambda[i][j] >= lambda[i+1][j+c[i]]`, with cyclic row indices.
Let `C_N` count cylinders with entries at most `N`, weighted by volume. For
`gcd(r,d)=1`, define `F_N=(q;q)_N C_N` and determine `Q_N` by

\[
F_N(q)=\sum_{m=0}^N {N\brack m}_q Q_m(q).
\]

This agrees with [Warnaar's definition and Conjecture 8.4](https://arxiv.org/html/2111.07550v3#S8).
The coprimality restriction matters: the general definition uses
`(q^g;q^g)_N`, where `g=gcd(r,d)`, and this script rejects those other cases.

## Exact finite transfer

For each positive entry level `t`, let `h_i(t)` be the number of entries in
row `i` at least `t`. The cylinder conditions become
`h_{i+1}(t) <= h_i(t)+c_i`, and the slices decrease componentwise with `t`.

Write every slice uniquely as `h=u+k*1`, with `min(u)=0`. Its nonnegative
slacks `s_i=u_i+c_i-u_{i+1}` sum to `d`. Conversely, every weak composition
of `d` into `r` parts gives one normalized slice by cumulative differences
and subtracting the minimum. Thus there are `binomial(d+r-1,r-1)` states.

For normalized slices set `D(u,v)=max_i max(v_i-u_i,0)`. The transition is

\[
u+k\mathbf1\ \geq\ v+l\mathbf1
\quad\Longleftrightarrow\quad k\geq l+D(u,v).
\]

Fix a sequence `u_1,...,u_N`. Write the offset differences as their minimum
cost plus independent nonnegative slacks, including the last offset. Summing
these slacks geometrically gives the exact rational expression

\[
C_N(q)=\frac{B_N(q)}{\prod_{j=1}^N(1-q^{rj})},\qquad
B_N(q)=\sum_{u_1,\ldots,u_N}
q^{\sum_t |u_t|+r\sum_{t=1}^{N-1}tD(u_t,u_{t+1})}.
\]

The [generator](../scripts/cylindric_positivity.py) computes this entire
numerator using integer polynomials. It divides exactly by
`prod_j(1+q^j+...+q^((r-1)j))` to obtain `F_N`, rejecting a nonzero remainder,
then uses Gaussian inversion to obtain `Q_N`. No truncation assumption is used
for these polynomial results.

The [Lean module](../RamanujanTau/Cylindric/Slices.lean) proves normalization
existence and uniqueness, preservation of cylinder inequalities, the exact
local transition, its free-slack parameterization, and the slice volume
formula. It does not yet formalize the row-conjugation bijection, finite state
enumeration, or the geometric summation above.

## Computations and verification

| Rank | Level | Cyclic profiles | Entry bounds | Nontrivial polynomials | Non-balanced polynomials |
|---|---|---|---|---|---|
| 4 | 5 | 14 | 1 through 20 | 280 | 260 |
| 4 | 7 | 30 | 1 through 8 | 240 | 232 |

All 520 divisions are exact and all resulting `Q_N` have nonnegative integer
coefficients. Their coefficient sums equal `13^N` and `29^N`, respectively.
The computation also verifies all 520 full polynomial instances of the
independent Corteel–Welsh recurrence

\[
F_N(c)=(1-q^N)F_{N-1}(c)+
\sum_{\varnothing\ne J\subseteq I_c}(-1)^{|J|-1}q^{N|J|}F_N(c(J)),
\]

where `I_c={i:c_i>0}` and `c(J)_i=c_i-1_{i in J}+1_{i-1 in J}`.
Additional checks reproduce the trefoil Gaussian identity through `N=8`,
Warnaar's complete `Q_1` at `(2,2,2,1)`, and direct enumeration of actual row
partitions through volume 10 for five profiles and `N=1,2,3`.

Records: [level 5](verification/cylindric_positivity_4_5.json),
[level 7](verification/cylindric_positivity_4_7.json),
[Lean verification](verification/cylindric_slices.json), and
[axiom report](verification/cylindric_slices.axioms.txt). The records store
coefficient hashes and initial coefficients; rerunning regenerates the full
polynomials in memory. Python checks are distinct from Lean certification.

```sh
python3 scripts/cylindric_positivity.py --rank 4 --level 5 --maximum 20 --validate --output docs/verification/cylindric_positivity_4_5.json
python3 scripts/cylindric_positivity.py --rank 4 --level 7 --maximum 8 --output docs/verification/cylindric_positivity_4_7.json
lake build RamanujanTau.Cylindric.Slices
lake env lean scripts/audit/cylindric_slices.lean
```

Python requires `python-flint` (tested with 0.6.0). The focused Lean build and
six-declaration audit pass with only `propext`, `Classical.choice`, and
`Quot.sound`. The module is outside the public root import graph.

## Next positivity proof target

Use the non-balanced profile `(0,1,2,2)` as the first all-`N` target. It is a
small perturbation of `(1,1,1,2)`, lies in a system of only 14 cyclic profiles,
and passes exact checks through `N=20`. Its first polynomial is

\[
Q_1=2q+3q^2+2q^3+3q^4+q^5+q^6+q^7.
\]

The next proof step is a positive recurrence or positive sum representation
for this sequence. The existing inclusion-exclusion recurrence has negative
terms, so positivity of the finite transfer numerator alone does not prove
positivity after division and Gaussian inversion.

## What unifiedtheory contributes to black hole work

The following paths are relative to the separate `unifiedtheory` repository.
This is a source-level scope assessment, not a fresh rebuild of that repository.

| Existing source | Reusable content | Remaining connection |
|---|---|---|
| `UnifiedTheory/Audit/KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy.lean` | Completion of the square and equality case for `2*pi^2*C_eff/beta + beta*Delta` | An actual coefficient asymptotic and control of the rest of its expansion |
| `UnifiedTheory/Audit/KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap.lean` | Finite product estimates and the algebraic exponent gap `S-S/c >= S/2` for `c>=2` | Bounds on actual Bessel factors, Kloosterman sums, and the total remainder |
| `UnifiedTheory/LayerB/BekensteinHawking.lean`, `HawkingTemperature.lean`, `ChristodoulouIrreducibleMass.lean` | Algebraic consequences of specified Schwarzschild/Kerr formulas | Derivation from a microscopic state model; the coefficient `1/4` is an input |
| `UnifiedTheory/Audit/KFCausalCSpecArakiHorizonRelativeEntropy.lean` | Constants and implications connecting explicit horizon-entropy targets to curvature balance | The AQFT and modular-theory hypotheses are still targets |

The DMZ-labelled file
`UnifiedTheory/Audit/KFCausalMultiChannelThreeByThreeGL3GramDeterminantRamanujanE8EisensteinDiscriminantMockModularBlackHoleEntropySMGUTBridge.lean`
defines its total degeneracy by adding two supplied real numbers. Its entropy
inequality assumes `d_mock>=1` and `d_appell>=0`; it does not construct the
DMZ Fourier coefficients. Its conjunction with a Schwarzschild area identity
does not identify the logarithm of those coefficients with that area.
The physical decomposition to target is the one in
[Dabholkar–Murthy–Zagier](https://arxiv.org/abs/1208.4074).

A concrete preliminary benchmark is now formalized in
[Entropy.lean](../RamanujanTau/HardyRamanujan/Entropy.lean):

\[
\frac{\log p(n)}{\sqrt n}\longrightarrow \pi\sqrt{2/3}.
\]

`HardyRamanujan.entropy_sqrt_limit` proves this for
`p(n)=card(Nat.Partition n)`. The stronger `entropy_log_correction` proves

\[
\log p(n)-\pi\sqrt{2n/3}+\log n\longrightarrow-\log(4\sqrt3).
\]

Both follow from the [existing Hardy–Ramanujan theorem](../RamanujanTau/HardyRamanujan/Main.lean),
by taking logarithms of its positive normalized ratio. The proof then uses
`log n / sqrt n → 0` for the leading limit. These are formalized standard
consequences, with no novelty claim.

The isolated port in [CardySaddle.lean](../RamanujanTau/CardySaddle.lean) proves
the completion-of-the-square identity and the balance equality.
`partition_cardy_leading` matches unifiedtheory's normalization at
`C_eff=1/12` and `Delta=n` to `pi*sqrt(2*n/3)`.
For `n≥1`, `partition_saddle_minimum` proves that `beta=pi/sqrt(6*n)` attains
the global minimum over positive `beta`.
`entropy_cardy_log_correction` connects this leading term to the actual count
and its logarithmic correction. A saddle inequality alone would not establish
a coefficient asymptotic; here that input is supplied by Hardy–Ramanujan.
The [verification record](verification/partition_entropy.json) and
[ten-declaration axiom audit](../scripts/audit/partition_entropy.lean) cover
these results, with only the three standard Lean axioms.
Use `import RamanujanTau.HardyRamanujan.Entropy` directly. The new modules pass
their focused build; root integration is deferred because the full build was
interrupted during two pre-existing arithmetic certificate checks under heavy
memory pressure. The verification record preserves that limitation.

This is a normalization benchmark for ordinary partitions, not a physical
black-hole state identification.

The local toolchains differ: `unifiedtheory` uses Lean 4.28.0, while this
repository uses 4.30.0-rc2. Reuse should begin with small isolated lemma ports.

### 24-colored partitions: coefficient bridge and leading entropy

The next mathematical step is now formalized: `d(n)=p_24(n+1)`, the coefficient of
`q^n` in `1/Delta = eta^(-24)`. In the string compactification discussed in
[DMZ §3.2, equations (49), (53), and (57)](https://arxiv.org/html/1208.4074v2#S3.SS2),
these coefficients count half-BPS Dabholkar–Harvey states, with
`log d(n) ~ 4*pi*sqrt n`. This precedes the quarter-BPS mock Jacobi problem.

The new proofs establish the mathematical coefficient statement; the physical
identification is literature context, not an additional Lean theorem.
[ColoredPartitions.lean](../RamanujanTau/ColoredPartitions.lean) defines
`Partition k n` as a size tuple summing to `n`, together with an ordinary
partition for each color, and defines `count k n` as its finite cardinality.
Its `coeff_series` theorem proves, for every natural `k,n`,

\[
[q^n]\left(\sum_{j\ge0}p(j)q^j\right)^k=p_k(n).
\]

This is a convolution of coefficients, not `p(n)^k`.
`qExpansion_discriminant_mul_series` proves
`qExpansion(Delta) * map(series 24) = X`, using the existing
[analytic discriminant bridge](../RamanujanTau/TauModular.lean). Thus the
regular power series is `q/Delta`; the definition `degeneracy n = count 24 (n+1)`
accounts for the pole's one-unit coefficient shift. No Laurent-series inverse
or physical Hilbert space is used as a definition of the count.

[ColoredPartitionEntropy.lean](../RamanujanTau/ColoredPartitionEntropy.lean)
proves the leading limit for every fixed positive `k`:

\[
\frac{\log p_k(n)}{\sqrt n}\longrightarrow\pi\sqrt{2/3}\sqrt k.
\]

The proof uses the ordinary-partition limit and finite convolution bounds.
A balanced tuple
of partitions, with leftover ones added in one color, gives
`p(floor(N/k))^k <= p_k(N)`. For `epsilon>0`, an eventual bound
`log p(j) <= (a+epsilon)*sqrt j + B`, where `a=pi*sqrt(2/3)`, extends to all
`j` by choosing `B` to cover the finitely many small indices. There are at most
`(N+1)^k` tuples of nonnegative indices summing to `N`, and Cauchy–Schwarz gives
`sum sqrt(j_i) <= sqrt(k*N)`. Thus

\[
\log p_k(N)\le k\log(N+1)+(a+\epsilon)\sqrt{kN}+kB.
\]

The lower and upper bounds give `entropy_sqrt_limit`, and `entropy_twentyfour`
specializes the constant to `4*pi`. The shifted theorem `degeneracy_entropy`
proves `log d(n)/sqrt n → 4*pi`. Finally, `degeneracy_cardy_ratio` proves

\[
\frac{\log d(n)}{2\pi\sqrt{2\cdot2\cdot n}}\longrightarrow1,
\]

matching unifiedtheory's normalization `C_eff=2`. There is no unproved
asymptotic premise in these theorems. This establishes the leading entropy;
the colored logarithmic correction and quantitative remainder need additional
work. The [verification record](verification/colored_partition_entropy.json)
and [dedicated audit](../scripts/audit/colored_partition_entropy.lean) identify
the checked declarations and source snapshot. Use the standalone import
`RamanujanTau.ColoredPartitionEntropy`; the public root import is unchanged.
The earlier ordinary-partition verification record remains a historical
snapshot and does not claim these later colored results.

The subsequent mock Jacobi target must additionally construct a specific
finite part `psi_m^F`, its modular completion, and its coefficient asymptotic.
The colored entropy theorem does not supply those mock Jacobi results or
derive a black-hole area law from a physical state model.

### Occupation-number model and finite shell Hilbert spaces

The occupation-basis step is now formalized in
[BosonicOccupation.lean](../RamanujanTau/BosonicOccupation.lean).
For any natural `k`, `Occupation k` specifies nonnegative integer occupations
`N(i,m)` of finite support for each species, with `N(i,0)=0`. Its energy is

\[
E(N)=\sum_{i=1}^{k}\sum_{m\ge1}mN(i,m).
\]

`stateEquivPartition` explicitly identifies energy-`N` occupation states with
`k`-colored partitions of `N`. The maps convert occupation multiplicities
to partition parts and back. The cutoff is a theorem:
`state_zero_above_energy` proves that modes above `N` are unoccupied, and
`state_occupation_bound` gives `N(i,m)≤N/m` for `m>0`. No arbitrary mode
truncation is introduced. `zero_energy_unique` identifies the unique vacuum.

The finite complex Hilbert space `ShellSpace k N` has the explicit
orthonormal basis `occupationBasis k N`, indexed by these occupations.
Its dimension is `p_k(N)` (`shell_finrank`). Consequently its formal graded
dimension series is `partitionGF^k` (`shellSeries_eq`); for 24 species,
`discriminant_mul_shellSeries` identifies this series with `q/Delta` through
the cleared q-expansion identity.

The positive bosonic modes and the specified vacuum shift of −1 follow the
model discussed in [DMZ §3.2](https://arxiv.org/html/1208.4074v2#S3.SS2).
Here the shift is an explicit input, not a derived normal-ordering constant.
For natural charge `n`, `chargeStateEquivEnergy` identifies charge `n` with
energy `n+1`, and `charge_finrank` proves

\[
\dim_{\mathbb C}\operatorname{ChargeSpace}(n)=p_{24}(n+1).
\]

`charge_entropy` and `charge_cardy_ratio` transfer the earlier proved limits
to these actual finite-dimensional spaces:

\[
\frac{\log\dim_{\mathbb C}\operatorname{ChargeSpace}(n)}{\sqrt n}
\longrightarrow4\pi,
\qquad
\frac{\log\dim_{\mathbb C}\operatorname{ChargeSpace}(n)}
{\operatorname{Cardy.leadingEntropy}(2,n)}\longrightarrow1.
\]

The [verification record](verification/bosonic_occupation.json) and
[23-declaration audit](../scripts/audit/bosonic_occupation.lean) cover this
step. Use the standalone import `RamanujanTau.BosonicOccupation`.
The new module passes its focused build; the root import is unchanged and
the previously recorded full-build limitation remains.

This construction supplies the occupation-basis equivalence that the earlier
coefficient calculation did not include. A full infinite Fock representation,
creation and annihilation operators with their commutation relations, and
an analytic infinite operator trace remain separate tasks. Identification
with the physical string Hilbert space, string duality, and a gravitational
area law are also not proved. The quarter-BPS mock Jacobi problem still
requires the finite part, modular completion, and coefficient asymptotic
described above. No new mathematical or physical discovery is claimed.

### Algebraic oscillator operators and energy eigenspaces

The next step constructs operators on the same occupation labels.
[BosonicOscillator.lean](../RamanujanTau/BosonicOscillator.lean) uses complex
polynomials in variables indexed by `(i,j)`, where `i` is a species and
the positive mode frequency is `omega(i,j)=j+1`.
`occupationEquiv` identifies their monomial exponents with all of the earlier
occupation arrays. `energy_toOccupation` proves that weighted exponent
energy equals `BosonicOccupation.energy`.

Creation `C_a` multiplies by `X_a`; annihilation `A_a` differentiates with
respect to `X_a`. The monomial basis is unnormalized: creation has coefficient
1 and annihilation has coefficient equal to the occupation number. The
canonical relations hold on every algebraic state:

\[
[A_a,C_b]=\delta_{ab}I,\qquad [A_a,A_b]=[C_a,C_b]=0.
\]

The Hamiltonian is the derivation specified by `H(X_a)=omega_a X_a`.
It kills the vacuum and satisfies

\[
[H,C_a]=\omega_a C_a,\qquad [H,A_a]=-\omega_a A_a.
\]

`hamiltonian_occupation` proves that each occupation monomial is an
eigenvector with eigenvalue equal to its previously defined total energy.
[BosonicSpectrum.lean](../RamanujanTau/BosonicSpectrum.lean) proves the converse:
an eigenvalue-`N` polynomial has nonzero coefficients only at exponents of
energy `N` (`mem_energySpace`). Consequently `energySpaceEquivShell` gives
an explicit complex-linear equivalence from this actual Hamiltonian
eigenspace to `BosonicOccupation.ShellSpace k N`. It is finite-dimensional,
with dimension `p_k(N)`.

For 24 species the specified charge operator is `Q=H−I`.
`chargeEigenspace_eq` identifies its eigenvalue-`n` space with the energy-`n+1`
space. The previously established count and entropy therefore now apply to
the operator's eigenspaces:

\[
\dim_{\mathbb C}\ker(Q-nI)=p_{24}(n+1),\qquad
\frac{\log\dim_{\mathbb C}\ker(Q-nI)}{\sqrt n}\longrightarrow4\pi
\quad(n\in\mathbb N).
\]

`chargeEigenspace_cardy_ratio` also proves that the ratio to
`Cardy.leadingEntropy 2 n` tends to 1. These statements have no additional
asymptotic hypothesis. The
[verification record](verification/bosonic_spectrum.json) and
[dedicated audit](../scripts/audit/bosonic_spectrum.lean) cover this extension.
Use the standalone import `RamanujanTau.BosonicSpectrum`.

This completes the algebraic creation/annihilation and eigenspace step.
The equivalence to the finite shells is linear, not asserted isometric.
No Hilbert completion, operator adjoint relation, self-adjoint unbounded
Hamiltonian, or analytic infinite trace has been proved. The vacuum offset
is still specified. String duality, the gravitational area law, and the
quarter-BPS mock Jacobi construction remain separate obligations. Earlier
verification files preserve the boundaries of their own snapshots.

### Factorial normalization and finite-shell Hilbert adjoints

[BosonicNormalization.lean](../RamanujanTau/BosonicNormalization.lean)
defines `factorialWeight(d)=prod_a (d_a!)` and proves both its positivity and
the recurrence obtained by increasing one occupation. It constructs the
normalized polynomial basis

\[
b_d=\frac{X^d}{\sqrt{\prod_a d_a!}}.
\]

The existing algebraic operators act by

\[
C_a b_d=\sqrt{d_a+1}\,b_{d+e_a},\qquad
A_a b_{d+e_a}=\sqrt{d_a+1}\,b_d,
\]

and `A_a b_d=0` if `d_a=0`. These are proved rescaling identities for the
earlier multiplication and differentiation operators.
`normalized_coordinate_adjoint` proves the conjugate-transpose relation for
their coordinates on the full algebraic basis.

[BosonicAdjoint.lean](../RamanujanTau/BosonicAdjoint.lean) restricts these
coordinates to each exact energy eigenspace. `normalizedShellEquiv` is an
explicit complex-linear equivalence to the finite Euclidean space indexed
by energy-`N` exponents. Its inverse sends the orthonormal coordinate basis
to `b_d` (`normalizedShellEquiv_symm_basis`). The coordinate shell is
isometrically equivalent to the previously constructed occupation shell
through `normalizedShellIsometry`.

Creation preserves the upward energy shift; the new
`annihilate_mem_energySpace` proves the corresponding downward shift.
`createShell a N` and `annihilateShell a N` are obtained by restricting the
original polynomial maps and transporting them through the normalized
coordinate equivalences. Neither is defined to be the other's adjoint.
The theorem `annihilateShell_eq_adjoint` proves

\[
A_{a,N}=C_{a,N}^{*},\qquad
C_{a,N}:\mathcal H_N\longrightarrow\mathcal H_{N+\omega_a},
\]

and `shell_inner_adjoint` proves the corresponding inner-product identity
for arbitrary vectors in those two shells. `normalizedShell_finrank`
preserves dimension `p_k(N)`, so normalization does not alter the counting
input to the established entropy results.

The [verification record](verification/bosonic_adjoint.json) and
[dedicated audit](../scripts/audit/bosonic_adjoint.lean) cover this step.
Use the standalone import `RamanujanTau.BosonicAdjoint`.

The adjoint statement is for finite shells. A completed infinite Fock space,
domains and adjoints of unbounded operators, a self-adjoint infinite
Hamiltonian, and an analytic infinite trace remain separate tasks. The
vacuum offset is still specified, and the gravitational/string-theoretic
identification and quarter-BPS mock Jacobi problem remain unproved here.
Earlier verification records retain the boundaries of their own snapshots.
