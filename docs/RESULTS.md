# Detailed theorem catalog

[Overview](../README.md) · [Current status](STATUS.md) · [Finite arithmetic certificates](FINITE_ARITHMETIC.md)

Module paths in this catalog are relative to `RamanujanTau/` unless stated otherwise.
Named hypotheses are part of a theorem's statement; an axiom audit does not discharge them.
The research notes are indexed separately in [the documentation guide](README.md).

## Theorem A: all-prime ordinarity on the prescribed level-six eigenspace

`TheoremA/BinaryOrdinarity.lean` proves
`U_ne_zero_of_binary_sign_eigenvalues` for every prime ℓ ≥ 13 and every
field of characteristic ℓ. A nonzero series in the weight-ℓ−3 integral
level-six model with eigenvalues (q/ℓ)q^{(ℓ−5)/2} for U_q, q = 2,3,
cannot be killed by U_ℓ. `ReducedLevelSixOrdinarity.lean` transfers this
to reductions of actual complex level-six modular forms over embedded
coefficient rings. The two initial eigenvalue formulas remain explicit;
filtration and weight-six lifting are no longer hypotheses.

`TheoremA/WeightSixIdentity.lean` proves
`classicalWeightSixAnnihilator_eq_zero`: (U₃+9)(U₂²+6U₂+32)=0 on the
actual complex cusp space S₆(Γ₀(6)). It also proves
`weightSix_finrank_eq_three` and an explicit linear equivalence between this
space and its first three positive q-coefficients.

The proof constructs three actual eta quotient cusp forms. It verifies their
transformations on a proved generating set for Γ₀(6), holomorphy, vanishing
at every cusp, and their integer Fourier coefficients through q⁹. The
coefficient bound in `LevelSixSturm.lean` and the finite certificate in
`WeightSixCertificate.lean` then establish the full operator identity.
No old/new decomposition or dimension formula is assumed.

`LevelSixModularSturm.lean` proves that the first k+1 coefficients determine
every level-six modular form of nonnegative integral weight k. The general
eta certificate in `EtaQuotientForms.lean` allows nonnegative cusp rates.
`WeightTwoForms.lean` and `WeightTwoQExpansion.lean` construct actual forms
A, B, C with integral Fourier expansions and AC=B², including the identity
over ℤ. `WeightTwoCoordinates.lean` proves dim M₂(Γ₀(6)) = 3, reconstruction
from the first three coefficients, and descent over any coefficient ring
embedded in ℂ.

`EvenWeightForms.lean` constructs a uniform eta basis with leading terms
1,q,…,q²ⁿ. `EvenWeightCoordinates.lean` proves dim M₂ₙ(Γ₀(6)) = 2n+1,
integer reconstruction, and descent in every even weight. `EvenWeightProducts.lean`
proves the multiplication rule and generation by A,B,C with unique normal
monomials AᵃBᵇCᶜ, b < 2. `BinarySeries.lean` and `BinaryModel.lean` identify
this model with homogeneous binary polynomials of degree 2n; evaluation is
injective in each even degree over every commutative ring.

`LevelSixSerre.lean` constructs the actual Serre derivative, using Cauchy's
estimate to verify boundedness at every cusp. `EvenWeightSerre.lean` proves
that 12θ−kE₂ preserves the integral model and raises its weight by two in
every coefficient ring.

`BinaryEisenstein.lean` proves the explicit E₄ and E₆ binary formulas and
full series identities. `BinaryPullback.lean` proves weight-preserving
substitution and no common projective zero. `BinaryHasse.lean` identifies
the Hasse invariant and companion, proves their expansions are 1 and E₂,
and characterizes equal expansions in one weight class as Hasse-power multiples.
`BinaryBaseChange.lean` and `HasseSeparation.lean` prove projective separation
and coprimality on both affine charts over every characteristic-ℓ field, ℓ ≥ 5.

`BinaryTheta.lean` constructs a homogeneous numerator with expansion 12θ.
`BinaryDivisibility.lean` proves `hasse_dvd_theta_iff` away from weights zero
modulo ℓ and `hasse_dvd_iff_lower_expansion`: a Hasse factor is exactly the
ability to lower weight by ℓ−1 without changing the full series.
`BinaryFiltration.lean` defines the least representing half-weight in one
class modulo (ℓ−1)/2 and proves the theta step and drop laws.
`BinaryFiltrationCycle.lean` proves `theta_four_binaryRep`: if a nonzero
weight-ℓ−3 series is killed by U_ℓ, its fourth theta iterate has a
weight-six representation. This does not assume a general Katz comparison
or independence of expansions across different weight classes.

`BadPrimeForms.lean` and `BadPrimeQExpansion.lean` construct actual U_p on
Γ₀(N) for every integral weight and prime p dividing nonzero N, prove the
coefficient-extraction formula, and prove the operators commute.
`IntegralCusp.lean` and `ClassicalWeightSix.lean` transport the weight-six
identity through any coefficient ring embedded in ℂ to its residue rings.
Consequently `eq_zero_of_reduced_weightSix_eigenpair` excludes a nonzero
(4,9) eigenvector in every such reduced cusp space of characteristic at least five.

`BadPrimeModular.lean` extends the actual bad-prime operators and expansion
identities to the full modular-form space. `ModularWeightSixData.lean`
kernel-checks two 7×7 matrices against coefficients through q¹⁸.
`ModularWeightSixAction.lean` proves these are the actual operators on the
integral basis. `ModularWeightSixIdentity.lean` proves
(U₂−1)(U₂−32)(U₃+9)(U₂²+6U₂+32)=0 throughout the weight-six model over
every coefficient ring. It evaluates to −108864 at (4,9), which is nonzero
in characteristic ℓ ≥ 13. This supplies the contradiction in the
all-prime ordinarity theorem without a cusp-lifting assumption.

`NewClass.lean` derives those eigenvalues from the Atkin–Lehner signs, and
`newform_coeff_ell_ne_zero` proves unconditionally that a normalized
T_ℓ-eigenform in the class has a unit ℓ-th coefficient above ℓ.
`SignLattice.latticeT_det_not_dvd` proves T_ℓ invertible modulo ℓ on the integer
sign lattice. `ThetaLift.theoremA_unconditional` and `ThetaLift.X_injective_unconditional` prove the half-integral
and Boylan–Webb forms, and `ThetaLift.aadModularity` proves Theorem 1.1 of
Ahlgren–Andersen–Dicks. `BLBound.bEll_le` and `BLBound.dEll_eq_zero` give b_ℓ(m) ≤ 2m−1 and d_ℓ = 0
for every prime ℓ ≥ 13. `BLBound.rank_Xbar_pow` gives rank X̄^k = ⌊(ℓ+12)/24⌋, and `BLBound.rEll_le` gives the known
Folsom–Kent–Ono bound r_ℓ(m) ≤ ⌊(ℓ+12)/24⌋ for these primes. `BLBound.partition_recurrence` gives the congruence with
⌊(ℓ+12)/24⌋ terms, modulo ℓ^m, for all b ≥ 2m−1. `BLBound.ahlgren_boylan` proves the Ahlgren–Boylan theorem: no prime ℓ ≥ 13
has a congruence p(ℓn+β) ≡ 0 with β < ℓ, and `BLBound.ramanujan_congruence_iff` completes the classification over all primes: only (ℓ,β) = (5,4), (7,5), (11,6). `BLBound.rc_lift` is the Rankin–Cohen lift of θ, computing U/ℓ on [g, E_{ℓ−1}]₁ modulo ℓ. `ThetaLift.gen_modular` proves modularity of the Shimura lift of G/η^j on Γ₀(6) for general j and weight, and `TheoremA.dvd_coeff_hEight_of_binary_kernel` shows a U_p-kernel in weight p−5 of the sign class forces p ∣ a_p(h₈). `BLBound.class_sep` is Swinnerton-Dyer's independence of weight classes, and `BLBound.rEll_eq_one` gives r_ℓ(m) = 1 for 13 ≤ ℓ < 36.
See the [declaration ledger and remaining work](THEOREM_A.md).

## Results at a glance

**Added 2026-11-03** (see [STATUS](STATUS.md#results-of-2026-11-03)):
- `TauBound.tau_isBigO_47_8_unconditional` — `τ(n) =O n^{47/8+ε}` for every ε > 0 (Kloosterman 1927), unconditional (superseded by the 35/6 and 23/4 entries below).
- **`GORZXi.xi_gorz_unconditional`** — GORZ Theorem 1 for Riemann Ξ, unconditional (`xiKernelHyp_holds`); `GORZXi.gorz_thm3` — the abstract GORZ Theorem 3 (unconditional); `GORZXi.gammaMathlib_eq` — integral formula for the Taylor coefficients of Ξ from Mathlib's completed zeta.
- `GORZ.jensen_eventually_hyperbolic` — for every d, `J^{d,n}` is hyperbolic for all large n (Griffin–Ono–Rolen–Zagier 2019, partition case); `GORZ.tendsto_coeff_Jhat` — renormalized Jensen polynomials → Hermite.
- `GORZXiEff.gamma_eq_mom` — the Taylor coefficients of Ξ as moments of Riemann's Φ; **`GORZXiEff.turan_gamma_unconditional`** — the Turán inequalities for the Taylor coefficients of Ξ for every n (Csordas–Norfolk–Varga), unconditional.
- `RankinSharpGeneral.rankinSelberg_power_saving_sharp_general` — for every level-one cusp form and every δ < 1/5, `|Σ_{n≤N}|a_f(n)|²/n^{k−1} − c_f N| ≤ C_f N^{1−δ}` (supersedes `RankinErrorGeneral.rankinSelberg_power_saving_general`, exponent 1/84).
- **`RankinSelbergGeneral.rankinSelberg_asymptotic`** — the Rankin–Selberg asymptotic for every level-one cusp form f: `(1/N)Σ_{n≤N}|a_f(n)|²/n^{k−1} → (3/π)(4π)^k‖f‖²/(k−1)!`; `rankinSelberg_weight16` … `rankinSelberg_weight26` for ΔE₄, ΔE₆, ΔE₈, ΔE₁₀, ΔE₁₄.
- **`Stirling.rankinSelberg_power_saving_third`** — `|Σ_{n≤N} τ(n)²/n¹¹ − cN| ≤ C N^{1−δ}` for every δ < 1/3, and for every level-one cusp form (`…_third_general`); `Stirling.norm_Gamma_ratio_le_of_le` — `|Γ(α+it)/Γ(β+it)| ≤ C|β+it|^{α−β}`; `Stirling.norm_Gamma_le_stirling` / `stirling_le_norm_Gamma` — two-sided Stirling bounds in vertical strips.
- **`RankinSharp.rankinSelberg_power_saving_sharp`** — `|Σ_{n≤N} τ(n)²/n¹¹ − cN| ≤ C N^{1−δ}` for every δ < 1/5 (supersedes the 1/84 exponent; Rankin's is 2/5).
- **`RankinError.rankinSelberg_power_saving_84`** — `|Σ_{n≤N} τ(n)²/n¹¹ − cN| ≤ C·N^{1−1/84}`, unconditional power-saving error (Rankin's is 2/5).
- **`RankinSelbergFE.RStar_one_sub`** — the Rankin–Selberg functional equation R*(1−s) = R*(s) for R*(s) = 2π^{−s}Γ(s)Γ(s+11)(4π)^{−s−11}ζ(2s)Σ τ(n)²n^{−11−s}, with R* holomorphic off {0,1}, simple poles of residue ±‖Δ‖² (`RStar_eq`, `RStar_residue_one`); `meromorphic_Rcont` — Σ τ(n)²n^{−11−s} is meromorphic on ℂ, with `Rcont_residue_one` (residue (3/π)(4π)¹²‖Δ‖²/11!); `EpsteinStar_one_sub` — E*(z,1−s) = E*(z,s) for the completed real-analytic Eisenstein series.
- **`EisensteinReal.rankinSelberg_asymptotic_zagier_unconditional`** — the Rankin–Selberg asymptotic `Σ_{n≤N} τ(n)²/n¹¹ ~ (3/π)(4π)¹²‖Δ‖²/11!·N`, unconditional; `horocycleLimit_zagier` — horocycle equidistribution for |Δ|²y¹².
- `EisensteinReal.karamata` — Karamata's Tauberian theorem for power series with nonnegative coefficients; `rankinSelberg_asymptotic_of_horocycle` (conditional on `HorocycleLimit`).
- `RankinSelberg.rankinSelberg_two_sided` — `c₁N ≤ Σ_{n≤N} τ(n)²/n¹¹ ≤ c₂N`: the order of magnitude in Rankin–Selberg.
- **`MeanSquare.mean_square_tauL`** — Carlson–Potter mean value: (1/T)∫₀ᵀ|L(Δ,σ+it)|² dt → Σ τ(n)² n^{−2σ} for every σ > 37/6 (the classical range is σ > 6); `MeanSquare.mv_poly` — ∫₀ᵀ|Σ_{n≤N} b_n n^{−it}|² dt = TΣ|b_n|² + O(log N·Σ n|b_n|²).
- **`MeanSquareFull.mean_square_tauL_full`** — the Carlson–Potter mean square on the full classical range σ > 6, by a functional-equation bootstrap (thresholds y_n = 1/(6+4n) → 0); `MeanSquareFull.norm_tauL_left_le` — ‖L(Δ,6−y+iu)‖ ≤ 6e¹⁰(1+|u|)^{2y}‖L(Δ,6+y+iu)‖ for 0 ≤ y ≤ 1/2.
- **`MeanSquareLeft.mean_square_tauL_left`** — for every σ < 6, ∫₀ᵀ |L(Δ,σ+it)|² dt ~ (2π)^{4σ−24} RS(24−2σ) T^{25−4σ}/(25−4σ); `mean_square_tauL_every_line` — the mean square on every vertical line (σ > 6, σ = 6, σ < 6); `tendsto_Qr` — |Γ(b+it)|/(|Γ(a+it)| t^{b−a}) → 1.
- **`HardyZeros.tauL_infinitely_many_critical_zeros`** — Hardy's theorem for L(Δ,s): ∀ T, ∃ t > T, L(Δ,6+it) = 0 (also `tauL_zeros_on_critical_line_infinite`); `HardyZeros.hardy_abstract` — Hardy's argument for any even real Z with Fourier–Laplace transform vanishing to all orders at the edge π/2.
- **`HardyZerosGeneral.fL_infinitely_many_critical_zeros`** — Hardy's theorem for every nonzero level-one cusp form f of weight k with real coefficients: infinitely many zeros of L(f,s) on Re s = k/2 (k ≡ 2 mod 4, root number −1, included).
- **`HardyCount.tauL_critical_zeros_count`** — for every ε > 0, L(Δ,s) has ≫ T^{1/2−ε} distinct zeros on Re s = 6 with 0 < t ≤ T; `tauL_critical_zero_gaps` — every window [t₀ − Kt₀^{1/2+ε}, t₀ + Kt₀^{1/2+ε}] contains one (Hardy–Littlewood's ≫ T is not reached).
- **`HardyCountLinear.tauL_critical_zeros_loglog`** — L(Δ,s) has ≫ T/log log T distinct zeros on Re s = 6 with 0 < t ≤ T (`tauL_critical_zeros_one_sub_eps`: ≫ T^{1−ε}); Hafner's ≫ T is not reached.
- **`HardyCountHafner.tauL_critical_zeros_linear`** — Hafner's theorem: L(Δ,s) has ≫ T distinct zeros on Re s = 6 with 0 < t ≤ T; `mean_square_uniform` — ∫_T^{2T}|L(Δ,6+x+it)|² dt ≪ T/x uniformly for 0 < x ≤ 1.
- **`HafnerGeneral.fL_critical_zeros_linear`** — Hafner's theorem for every nonzero level-one cusp form f with real coefficients: ≫ T distinct zeros of L(f,s) on Re s = k/2 up to height T.
- **`CriticalMeanSquare.critical_mean_square_upper`** — ∫₀ᵀ |L(Δ,6+it)|² dt ≪ T log T (upper bound only); `weighted_parseval` — ∫|Λ(6+it)|²e^{2βt}dt = 2π∫|e^{6(u+iβ)}Δ(ie^{u+iβ})|²du for 0 ≤ β < π/2.
- **`CriticalMeanSquareLower.critical_mean_square_isTheta`** — ∫₀ᵀ |L(Δ,6+it)|² dt ≍ T log T (lower bound `critical_mean_square_lower`).
- **`CriticalMeanSquareAsymp.critical_mean_square_asymptotic`** — Good's theorem: (∫₀ᵀ |L(Δ,6+it)|² dt)/(T log T) → c_Δ = 2c = (6/π)(4π)¹²‖Δ‖²/11! (`rankin_normalization`: c is the constant of Σ_{n≤N} τ(n)²/n¹¹ = cN + O(N^{3/5})).
- **`GeneralCuspMoments.fL_critical_mean_square_asymptotic`** — Good's asymptotic for every nonzero level-one cusp form f of weight k: ∫₀ᵀ |L(f,k/2+it)|² dt ~ 2c_f T log T, c_f = (3/π)(4π)^k‖f‖²/(k−1)! (no real-coefficient hypothesis).
- **`ZeroCount.zeroCount_window`** — L(Δ,s) has ≪ log T zeros (with multiplicity) with T < Im s ≤ T+1; `zeroCount_two_sided` — cT ≤ N(T) ≤ CT log T (sharpened by `ZeroCountRvM.riemann_von_mangoldt`).
- **`ZeroCountRvM.riemann_von_mangoldt`** — N(T) = (T/π) log(T/(2πe)) + O(log T) for the zeros of L(Δ,s) (with multiplicity, 0 < Im ≤ T); `arg_principle_rect` — the argument principle on rectangles for entire functions.
- **`GeneralZeros.riemann_von_mangoldt_gen`** — for every nonzero level-one cusp form f with first nonzero coefficient a_f(n₀): N_f(T) = (T/π) log(T/(2πe·n₀)) + O(log T). `fL_zero_free_region` — for every normalized eigenform, zeros with |Im ρ| ≥ t₀ satisfy Re ρ ≤ (k+1)/2 − c/log|Im ρ| (unconditional); all heights conditional on L(f,(k+1)/2) ≠ 0.
- **`EdgeNonvanishing.tauL_ne_zero_edge`** — L(Δ, 13/2+it) ≠ 0 for every real t (Rankin/Ogg/Moreno; proved here without Sym² holomorphy or Deligne); with `tauL_ne_zero_of_ge`, `tauL_ne_zero_of_le`, all nontrivial zeros lie in 11/2 < Re s < 13/2.
- **`ZeroFreeRegion.tauL_zero_free_region_uniform`** — de la Vallée-Poussin region for L(Δ,s): every nontrivial zero s satisfies 11/2 + c/log(|Im s|+2) ≤ Re s ≤ 13/2 − c/log(|Im s|+2); unconditional, no exceptional zero.
- **`TauPNT.tau_PNT_smoothed`** — unconditional smoothed PNT for τ: Σ_p τ(p)p^{−11/2} log p · p^{−σ} has a finite limit as σ → 1⁺. **Conditional (level 2):** `tau_prime_sign_changes` [DeligneBound] — τ(p) > 0 and τ(p) < 0 for infinitely many primes; `tau_PNT_tau` [DeligneBound, WienerIkeharaHyp] — Σ_{p<N} τ(p) log p = o(N^{13/2}).
- **`WienerIkehara.wienerIkehara`** — the Wiener–Ikehara Tauberian theorem (continuous boundary extension form), discharging `WienerIkeharaHyp`; port of PrimeNumberTheoremAnd (Apache-2.0). Corollaries: `PNT_psi` — the prime number theorem ψ(x)/x → 1; `tau_PNT_tau_deligne` [DeligneBound] — Σ_{p<N} τ(p) log p = o(N^{13/2}).
- **`TauPNTError.tau_PNT_tau_error_uncond`** — unconditional PNT for τ with de la Vallée-Poussin error: Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N) (no Deligne); `psiDelta_error_uncond` — Σ_{n≤x} Λ_Δ(n) ≪ x exp(−b√log x); `negLogDeriv_bound` — ‖L'/L(Δ,s)‖ ≪ log²(|t|+2) for σ ≥ 13/2 − c/log(|t|+2) (normalized).
- **`TauPNTUncond.tau_prime_sign_changes_uncond`** — unconditionally, τ(p) > 0 for infinitely many primes and τ(p) < 0 for infinitely many primes; `Rcont_ne_zero_edge` — L(Δ×Δ,1+it) ≠ 0 (t ≠ 0); `Lsym2_ne_zero_edge` — L(Sym²Δ,1+it) ≠ 0 (L(Sym²Δ,s) := ζ(2s)R(s)/ζ(s)); `rs_prime_PNT` — Σ_{p<N} τ(p)² log p / p¹¹ ~ N.
- **`TauSignsQuant.tau_pos_count_frequently`** (and `_neg_`) — unconditionally, for every θ < 9/20, #{p < x : τ(p) > 0} ≥ x^θ for arbitrarily large x (same for τ(p) < 0); **conditional (level 2):** `tau_pos_count_deligne` [DeligneBound] — #{p < N : τ(p) > 0}·log N ≥ N/12 for large N.
- **`EigenformEdge.fL_ne_zero_edge_of_ne`** — for every normalized level-one Hecke eigenform f (`IsNormalizedEigenform`), L(f,(k+1)/2+it) ≠ 0 for all t ≠ 0. **Conditional (level 2):** `fL_ne_zero_edge`, `fL_zeros_in_strip`, `eigen_PNT_smoothed` on the real point L(f,(k+1)/2) ≠ 0; `eigen_PNT`, `eigen_prime_sign_changes` additionally on `[DeligneBoundF f]`.
- **`TauPartialSums.tau_partial_sum_bound`** — Σ_{n≤x} τ(n) ≪_ε x^{181/30+ε} (below the trivial x^{13/2}; improved to 59/10 in `TauPartialSumsSharp`; 35/6 is proved conditionally on `DeligneBound` in `VoronoiPointwise.tau_partial_sum_35_6`); `cuspForm_partial_sum_bound` — x^{(k−1)/2+8/15+ε} for every level-one cusp form.
- **`TauPartialSumsSharp.tau_partial_sum_sharp`** — Σ_{n≤x} τ(n) ≪_ε x^{59/10+ε}, unconditionally (no Deligne); `cuspForm_partial_sum_sharp` — x^{(k−1)/2+2/5+ε} for every level-one cusp form; `kernelZero_sharp` — the degree-2 Landau kernel J₀(y) ≪ y^{k/2−1/4}.
- **`TauOmegaPartial.tau_partial_sum_omega`** — Σ_{n≤x} τ(n) = Ω(x^{23/4}): ∃ c > 0, |Σ_{n≤x} τ(n)| ≥ c x^{23/4} for arbitrarily large x; `cuspForm_partial_sum_omega` — Ω(x^{(k−1)/2+1/4}) for every nonzero level-one cusp form.
- **`TauOmegaPM.tau_partial_sum_omega_pm`** — Ω± for partial sums of τ: for every β < 28/5 and every c, Σ_{n≤x} τ(n) < −c x^β and > c x^β for arbitrarily large x (the exact exponent 23/4 is reached in `VoronoiTrunc.tau_omega_pm_exact`); `landau_mellin` — Landau's theorem for Mellin transforms of nonnegative functions.
- **`Voronoi.tau_log_mean_square`** — with S(x) = Σ_{n≤x} τ(n): c log X ≤ ∫₁^X S(x)² x^{−25/2} dx ≤ C log X; `tau_mean_square_upper` — ∫₁^X S² ≪ X^{25/2} log X; `tau_mean_square_omega` — ∫₁^X S² ≥ cX^{25/2} infinitely often; `tau_critical_mean_square_convergent` — ∫₁^∞ S²x^{−2σ−1} < ∞ for σ > 23/4. (Truncated Voronoi: see `VoronoiTrunc` below.)
- **`VoronoiTrunc.voronoi_truncated_L2`** — truncated Voronoi formula in L²: X^{−25/2}∫_X^{2X}(S(x) − x^{23/4}/(π√2) Σ_{n≤X^θ} τ(n)n^{−25/4}cos(4π√(nx) − π/4))² → 0 (0 < θ ≤ 1/4); **`tau_cramer`** — X^{−25/2}∫₁^X S² → B/(50π²); **`tau_omega_pm_exact`** — Ω±(x^{23/4}): for c < 1/(2π√2) and all large X, S exceeds c x^{23/4} and falls below −c x^{23/4} in [X, 2X]. No Deligne. See [VORONOI_TRUNC](VORONOI_TRUNC.md).
- **`VoronoiTruncGeneral.cusp_voronoi_truncated_L2`, `cusp_cramer`, `cusp_omega_pm_exact`** — the same three for every nonzero level-one cusp form f of weight k with real coefficients: truncated Voronoi in L² (phase −π/4 for all even k), X^{−k−1/2}∫₁^X S_f² → Σa(n)²n^{−k−1/2}/((4k+2)π²), and Ω±(x^{(k−1)/2+1/4}) when a(1) ≠ 0 (`eigenform_omega_pm_exact` for normalized Hecke eigenforms). See [VORONOI_TRUNC_GENERAL](VORONOI_TRUNC_GENERAL.md).
- **`VoronoiTruncComplete.cusp_cramer_complex`, `cusp_voronoi_truncated_L2_complex`, `cusp_omega_pm_exact'`, `cusp_re_omega_pm`, `cusp_im_omega_pm`** — the restrictions removed: complex coefficients (Cramér limit for \|S_f\|², L² Voronoi), and Ω± from the first nonzero coefficient (no a(1) ≠ 0). See [VORONOI_TRUNC_COMPLETE](VORONOI_TRUNC_COMPLETE.md).
- **`VoronoiPointwise.tau_voronoi_pointwise`** — pointwise truncated Voronoi, unconditional: \|S(x) − V_N(x)\| ≪ x^{121/20+ε}N^{−1/4} for N ≤ x^{3/5}. **Conditional (level 2, [DeligneBound]): `tau_voronoi_pointwise_deligne`** — \|S − V_N\| ≪ x^{6+ε}N^{−1/2} for N ≤ x^{1/3}, and **`tau_partial_sum_35_6`** — Σ_{n≤x} τ(n) ≪ x^{35/6+ε}. See [VORONOI_POINTWISE](VORONOI_POINTWISE.md).
- **`CramerMeanSquare.tau_cramer_log`** — Cramér–Tong: ∫₁^X S(x)² x^{−25/2} dx ~ (B/(4π²)) log X, B = Σ τ(n)²n^{−25/2}; `tau_cramer_constant` — if X^{−25/2}∫₁^X S² converges, its limit is B/(50π²) (existence proved in `VoronoiTrunc.tau_cramer`); `tau_mean_square_uniform` — the mean value of |L(Δ,σ+it)|² uniformly for σ ∈ [31/5, 25/4].
- **`Subconvexity.wilton_bound`** — Wilton (1929): ‖Σ_{n≤M} τ(n)e(nα)‖ ≤ C M⁶ log(1+2M) uniformly in α; `twLambda_functional_equation` — for a·ā ≡ 1 mod q, the completed additive twist satisfies Λ(−ā/q, 12−s) = Λ(a/q, s). (Subconvexity is proved in `SCSProof`, below.)
- **Conditional (level 2): `SubconvexityCond.tauL_subconvex_of_SCS`** [ShiftedConvolutionBound η B] — |L(Δ,6+it)| ≪ (1+|t|)^{1/2−η/(10B+24)}; the hypothesis is the arithmetic bound |Σ_{n≤N} λ(n)λ(n+h)| ≪ (N+h)^{1−η}h^B (Selberg 1965 / Good give η < 1/3; not formalized).
- **`SCSProof.tauL_subconvex`** — unconditional t-aspect subconvexity: \|L(Δ,6+it)\| ≪ (1+\|t\|)^{1/2−1/832000} (`tauL_subconvex_3_5`), from **`SCSProof.shiftedConvolutionBound_3_5`**: \|Σ_{n≤N} λ(n)λ(n+h)\| ≪ (N+h)^{1−1/8000}h⁸ (Rankin's exact 3/5 error as input)
- **`SCSSharp.tauL_subconvex_sharp`** — \|L(Δ,6+it)\| ≪ (1+\|t\|)^{1/2−1/231}, from **`shiftedConvolutionBound_sharp`**: \|Σ_{n≤N} λ(n)λ(n+h)\| ≪ (N+h)^{1−1/22}h^{1/2}, and the reduction `tauL_subconvex_of_SCS'` (δ = η/(5B+8)). See [SCS_SHARP](SCS_SHARP.md).
- **`SCSSharp2.tauL_subconvex_sharp2`** — \|L(Δ,6+it)\| ≪ (1+\|t\|)^{1/2−1/134}, from **`shiftedConvolutionBound_sharp2`**: \|Σ_{n≤N} λ(n)λ(n+h)\| ≪ (N+h)^{1−1/21}h^{1/21} (gcd-form Weil bound) and the reduction `tauL_subconvex_of_SCS2`. See [SCS_SHARP2](SCS_SHARP2.md).
- **Conditional (level 2): `SubconvexGeneral.fL_subconvex_of_SCSf`** [SCSf f η B] — for every real-coefficient level-one cusp form (so every normalized eigenform), ‖L(f, k/2+it)‖ ≪ (1+\|t\|)^{1/2−η/((1+u)(4B+6+2η))}; unconditional at f = Δ (`fL_discriminant_subconvex`, δ = 1/134).
- **`SubconvexGeneral2.fL_subconvex_eigenform`** — unconditional t-aspect subconvexity for every normalized Hecke eigenform of level one (indeed every real-coefficient cusp form, `fL_subconvex_general`): ‖L(f, k/2+it)‖ ≪ (1+\|t\|)^{1/2−1/180}, via `scsf_general`: \|Σ_{n≤N} λ_f(n)λ_f(n+h)\| ≪ (N+h)^{1−1/22}h^{1/2}; sharpened to 1/134 in **`SubconvexGeneral3.fL_subconvex_eigenform134`** (`scsf_general21`: SCS(1/21, 1/21) for every real-coefficient f).
- **`CuspConj.fL_subconvex_all`** — ‖L(f, k/2+it)‖ ≪ (1+\|t\|)^{1/2−1/134} for **every** level-one cusp form f; `cuspConj` — the conjugate cusp form f^ρ(z) = conj f(−z̄) with coefficients conj a(n); `eq_reF_add_imF` — f = Re f + i·Im f with real-coefficient cusp forms. See [CUSP_CONJ](CUSP_CONJ.md).
- **Conditional (level 2): `HafnerProportion.tauL_positive_proportion_of_selberg`** [SelbergHyp] — a positive proportion of the zeros of L(Δ,s) lie on Re s = 6 (N₀(T) ≫ T log T); the hypothesis is the mollified second moment plus Selberg's key lemma. Unconditional ingredients: `selberg_zeros` (abstract Selberg method), `mollified_first_moment`, `selberg_H1`, `selberg_H2`. See [HAFNER_PROPORTION](HAFNER_PROPORTION.md).
- **`HeckeAFE.tauL_afe`** — exact smoothed approximate functional equation for L(Δ,s) in 5 < Re s < 7, with weights uniform in t (`V_decay`, `V_sub_one`) and root number \|ε(6+it)\| = 1; **`tauL_afe_truncated`** — L(Δ,6+it) = S₁ + εS₂ + O((1+\|t\|)^{−B}) with sums of length (1+\|t\|)^{1+η}. See [HECKE_AFE](HECKE_AFE.md). See [SUBCONVEX_GENERAL](SUBCONVEX_GENERAL.md). (two-point Poincaré series on Γ\(ℍ×ℍ) + Weil; no Deligne). See [SCS_PROOF](SCS_PROOF.md).
- **`RankinExact.rankinSelberg_exact`** — Rankin's theorem: |Σ_{n≤N} τ(n)²/n¹¹ − cN| ≤ C N^{3/5}, with the exact exponent; `rankinSelberg_exact_general` gives the same for every level-one cusp form.
- **`RankinOmega.rankinSelberg_error_omega`** — the Rankin–Selberg error is Ω(N^{3/8}): \|Σ_{n≤N} τ(n)²/n¹¹ − cN\| ≥ c'N^{3/8} for arbitrarily large N; `cuspForm_rankin_omega_nat` for every nonzero level-one cusp form; `zeta_mean_sq` — ∫_T^{2T}\|ζ(u−it)\|² ≪ T uniformly for u ∈ [3/4, 1]. See [RANKIN_OMEGA](RANKIN_OMEGA.md).
- **`RankinOmegaPM.tau_rankin_omega_pm`** — the Rankin–Selberg error changes sign at scale x^β: Ω±(x^β) for every β < 3/20; `tau_rankin_mellin_mean_sq_lower` — ∫₁^∞ R²x^{−2σ−1} ≫ 1/(σ − 3/8); `tau_rankin_log_mean_sq_omega` — ∫₁^X R²x^{−7/4} ≫ log X infinitely often; `landau_mellin_strip` — Landau's theorem needing analyticity only on a strip about the real axis. Every level-one cusp form. See [RANKIN_OMEGA_PM](RANKIN_OMEGA_PM.md).
- **`ZetaMeanSquare.zeta_mean_square_tendsto`** — Hardy–Littlewood: (1/T)∫₁^T \|ζ(σ+it)\|² dt → ζ(2σ) for every 1/2 < σ ≤ 1; `zeta_mean_value_uniform` — uniformly on [σ₀, 1] with error O(T^{3/2−σ} + T^{2−2σ}log²T); `riemannZeta_conj` — ζ(s̄) = conj ζ(s).
- **`ZetaCritical.zeta_critical_mean_square`** — Hardy–Littlewood (1918): ∫₀ᵀ \|ζ(1/2+it)\|² dt ~ T log T; `zeta_critical_mean_square_bound` — error ≤ C·T√(log T). See [ZETA_CRITICAL](ZETA_CRITICAL.md). **`tau_rankin_omega_pm_quarter`** — the Rankin–Selberg error is Ω±(x^β) for every β < 1/4 (every cusp form). See [ZETA_MEAN_SQUARE](ZETA_MEAN_SQUARE.md).
- **`KernelPhase.rankinSelberg_landau_uncond`** — Rankin–Selberg error O(N^{1−δ}) for every δ < 2/5 (Rankin 1939 via Landau's method), unconditional; `rankinSelberg_landau_61_100_uncond` gives O(N^{61/100}), and `rankinSelberg_landau_general_uncond` gives every level-one cusp form. Inputs: `RankinLandau.dual_rep` (exact dual expansion) and `KernelPhase.kernelOne_sharp` (‖J₁(y)‖ ≤ C y^{9/8}).
- `HeckeL.heckeLambda_functional_equation` — Hecke: Λ(s) = (2π)^{−s}Γ(s)L(Δ,s) is entire, bounded in vertical strips, and Λ(12−s) = Λ(s); `HeckeL.tauLSeries_entire` — L(Δ,s) is entire; `HeckeL.tauLSeries_center_pos` — L(Δ,6) > 0.
- **`HeckeConvex.tauL_convexity`** — convexity bound ‖L(Δ,6+it)‖ ≤ C_ε(1+|t|)^{1/2+ε} (strip version `tauL_convexity_strip`); **`HeckeConvex.LSeriesSummable_tau_of_gt_13_2`** — Rankin 1939: L(Δ,s) converges absolutely for Re s > 13/2 without Deligne.
- **`HeckeConvexGeneral.fL_convexity`** — for every f ∈ S_k(SL₂(ℤ)): Hecke's functional equation Λ(f,k−s) = i^kΛ(f,s) (`heckeLambda_functional_equation`), absolute convergence of L(f,s) for Re s > (k+1)/2 (`LSeriesSummable_coef`), and ‖L(f,k/2+it)‖ ≪ (1+|t|)^{1/2+ε}.
- **`TauOmega.tau_omega`** — |τ(n)| ≥ c·n^{11/2} infinitely often; `tau_not_isBigO`: τ(n) ≠ O(n^{11/2−δ}) for every δ > 0 (Deligne's exponent is optimal), from the Rankin–Selberg lower bound.
- `TauOmega.coeff_omega` / `coeff_not_isBigO` — the same for every nonzero f ∈ S_k(SL₂(ℤ)): |a_f(n)| ≥ c·n^{(k−1)/2} infinitely often.
- **`LandauSigns.landau`** — Landau's theorem: a Dirichlet series with nonnegative coefficients that agrees with an entire function to the right of some line converges absolutely everywhere (not in Mathlib). **`LandauSigns.coeff_sign_changes`** — every nonzero f ∈ S_k(SL₂(ℤ)) with real coefficients has a_f(n) > 0 and a_f(n) < 0 for infinitely many n.
- **`HeckeZeros.tauL_zeros_in_strip`** — every zero of L(Δ,s) other than 0, −1, −2, … has 11/2 ≤ Re s ≤ 13/2; with the Euler product L(Δ,s) = ∏_p(1 − τ(p)p^{−s} + p^{11−2s})^{−1} on Re s > 13/2 (`tauL_eulerProduct`), non-vanishing there (`tauL_ne_zero_of_gt`), and the symmetries s ↦ 12 − s, s ↦ s̄.
- `TauSigns.tau_sign_changes` — τ(n) changes sign infinitely often; `TauSigns.tau_sign_change_short_interval_limit` — both signs occur in every (x, x + A x^{θ}], θ > 3/4; `TauSigns.card_signChanges_ge_limit` — ≫ X^{1/4−ε} sign changes up to X; `TauSigns.hecke_partial_sum` — Σ_{n≤M} τ(n) = O(M^{6+ε}).
- `KolbergTau.tau_mod2048_one_mod8` — Kolberg's congruence τ(n) ≡ σ₁₁(n) mod 2¹¹ for n ≡ 1 mod 8; instance `TauMod2_11`.
- `TauDensity.tau_eq_zero_iff` — τ(n) = 0 iff some prime p with τ(p) = 0 divides n to an odd power; `TauDensity.card_tau_ne_zero_ge_sqrt` — at least ⌊√N⌋ of the n ≤ N have τ(n) ≠ 0. `TauDensity.tau_norm_form_ne_zero` — τ(x²+691y²) ≠ 0; `TauDensity.card_tau_ne_zero_ge_div_log` — at least N/(585103(1+log N)) of the n ≤ N have τ(n) ≠ 0.
- `LehmerSmall.lehmer_below_214928639999` — `τ(n) ≠ 0` for all `1 ≤ n < 214928639999`, exactly Lehmer's 1947 bound (supersedes `lehmer_below_74627999`, `lehmer_below_258710399`, `lehmer_below_21492863999`; see [LEHMER_SMALL_N](LEHMER_SMALL_N.md)); `LehmerSmall.tau_prime_pow_ne_zero` — `τ(p) ≠ 0 ⇒ τ(pᵏ) ≠ 0`; `tau_mod7_all`, `tau_mod25_all`, `tau_mod3_all` — Ramanujan-type congruences for every n.
- **`StepanovAS.weilPrimeBound`** — Weil's bound `|S(1,b;p)| ≤ 2√p` for every prime p and b ≢ 0; **`StepanovAS.tau_isBigO_23_4_unconditional`** — `τ(n) = O(n^{23/4+ε})` (Weil 1948).
- `Stepanov.hasseWeil_charSum_le` — Stepanov's bound `|Σ_{x∈F_p} χ(f(x))| ≤ 12m²√p` for squarefree f of degree m; `Stepanov.hasse_elliptic` — Hasse's theorem up to the constant, `|#{y² = f(x)} − p| ≤ 108√p` for squarefree cubics; `Stepanov.saliePrimeBound` and `tau_isBigO_35_6_unconditional` — `τ(n) = O(n^{35/6+ε})`.
- `KloostermanL.kloosterman_L_rational` — rationality of the Kloosterman L-function over any finite field: L(T) = 1 + K₁T + qT², so K_r = −(α^r+β^r); `tau_isBigO_23_4_of_stepanov` — Weil's τ bound from the named Stepanov hypothesis.
- `WeilKloosterman.norm_kloosterman_primePow_le_sqrt` — `|S(1,n;p^k)| ≤ 6√(p^k)` for every prime p and k ≥ 2; `tau_isBigO_23_4_of_weil` — Weil's `τ(n) = O(n^{23/4+ε})` from the named prime bound `WeilPrimeBound`.
- `JensenThreshold.jensen6_threshold_unconditional` / `jensen7_threshold_unconditional` — `J^{6,n}` hyperbolic ⟺ (n ≥ 610 among n ≥ 609); `J^{7,n}` likewise at 908.
- `Dragonette.dragonette_literal` — `α(n) ~ (−1)^{n+1} e^{π√(n/6−1/144)}/(2√(n−1/24))` for `α(n) = [qⁿ]f(q) = N(0,2,n)−N(1,2,n)`.
- `AtkinSporadic.Weaver.ono_13_unconditional`, `weaver_17_unconditional` — `13 ∣ p(157525693n+111247)`, `17 ∣ p(48037937n+1122838)`; `Atkin13.atkin_13_unconditional` — `13 ∣ p(17303n+237)` (Atkin 1968), via `HalfHecke.etaHecke_11_168`.
- `Andrews.alpha_sign`, `Andrews.rank_parity_sign_all` — `0 < (−1)^{n+1}α(n)` for every `n ≥ 1`: even-rank minus odd-rank partitions of `n` has sign `(−1)^{n+1}`.
- **`MockCusp.andrews_1966_sqrt_log_unconditional`** — Andrews' 1966 theorem exactly as stated: α(n) = his printed main term over k ≤ √n + O(√n log n), unconditional (`MockCusp.HbSharp_holds`; the cruder `andrews_1966_unconditional` has error O(n log n)).
- `MockCusp.Hb_odd` — `‖f(q)‖ ≤ C‖z‖^{−3/2}` near every odd-denominator root of unity (uniform in h, K), the odd half of `Hb`.
- `Andrews66.andrews_1966_printed_isBigO_of_Hb` (conditional on `Hb`) — Andrews' 1966 theorem with his printed main term over k ≤ √n: `α(n) − andrewsPrinted n = O(√n log n)`.
- `AtkinTwisted.G1.atkin_13_89` etc. — 16 twisted mod-13 families for Q < 500, e.g. `13 ∣ p(9164597n+39275)`, `13 ∣ p(658489n+6788)`; `AtkinTwisted.eigen_all` — twisted series is a T(Q²)-eigenform mod 13 for every prime 5 ≤ Q < 500, Q ≠ 13.
- `GaussSign.gaussQuad_eval` — Gauss's sign: `Σ_{r mod N} e(r²/N) = √N` (N ≡ 1 mod 4) or `i√N` (N ≡ 3 mod 4) for every odd N; `GaussSign.etaHecke_all` — T(Q²) stabilizes η⁻¹S_k for every prime Q ≥ 5.
- `Andrews66.andrews_k1_isBigO` — `α(n) − (−1)^{n+1}·√24/√(24n−1)·sinh(π√(24n−1)/12) = O(exp(π√(n/6) − √(24n)/(2450π)))`: Andrews' first term with a power saving.
- `OnoWeaverMore.L<ℓ>.ono_ℓ_Q`, `atkin_ℓ_Q` — 81 congruence families mod ℓ ∈ {13,17,19,23,29,31} for every hit prime Q < 500, e.g. `L19.atkin_19_13_progression`: `19 ∣ p(41743n+669)`; `L29.atkin_29_17_progression`: `29 ∣ p(142477n+31778)`.
- `BWSharpAll.tendsto_bEll` — `b_ℓ(m) → ∞` for every prime ℓ ≥ 13.

| Theorem | Statement |
|---|---|
| **Euler's pentagonal number theorem** | `(q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}` |
| **Jacobi's cube identity** | `(q;q)_∞³ = Σ_{m≥0} (−1)ᵐ(2m+1) q^{m(m+1)/2}` |
| **Ramanujan's congruence (mod 5)** | `5 ∣ p(5n+4)` |
| **Ramanujan's congruence (mod 7)** | `7 ∣ p(7n+5)` |
| **Ramanujan's congruence (mod 11)** | `11 ∣ p(11n+6)` |
| **Ramanujan's "most beautiful identity"** | `Σ_{n≥0} p(5n+4) qⁿ = 5·(q⁵;q⁵)_∞⁵ / (q;q)_∞⁶` |
| **Ramanujan's congruence (mod 25)** | `25 ∣ p(25n+24)` |
| **Ramanujan's mod-7 identity** | `Σ p(7n+5) qⁿ = 7(q⁷;q⁷)³/(q;q)⁴ + 49q(q⁷;q⁷)⁷/(q;q)⁸` |
| **Ramanujan's congruence (mod 49)** | `49 ∣ p(49n+47)` |
| **Crank generating function** (Andrews–Garvan) | `Σ_{λ⊢n} z^{crank λ} = [qⁿ] (q;q)_∞/((zq;q)_∞(q/z;q)_∞)` |
| **Crank equidistribution mod 5 / mod 7** | `5·#{λ⊢5n+4 : crank ≡ i} = p(5n+4)`, `7·#{λ⊢7n+5 : crank ≡ i} = p(7n+5)` |
| **Winquist's identity** | `J(a)J(b)J(ab)J(a/b) = W(a,b)·(q;q)_∞²` for all `a, b ∈ ℂˣ` |
| **Crank equidistribution mod 11** (Dyson's conjecture) | `11·#{λ⊢11n+6 : crank ≡ i} = p(11n+6)` |
| **Rank equidistribution mod 5** (Dyson's conjecture; Atkin–Swinnerton-Dyer) | `5·#{λ⊢5n+4 : rank ≡ i} = p(5n+4)`, rank = largest part − number of parts |
| **Garvan's Hecke–Rogers identities** (2.18), (2.19) | `(zq)(q/z)·R(z;q)` and `(q)(zq)(q/z)·R(z;q²)` as indefinite theta series |
| **Ramanujan's 5-dissection of the rank generating function** (Lost Notebook p. 20) | `R(ζ₅;q) = Σ qᵏR_k(q⁵)` with `R₁ = J₅²/J₅,₁`, `R₂ = (ζ+ζ⁴)J₅²/J₅,₂`, `R₄ = 0`, and `R₀`, `R₃` in terms of the mock theta functions `φ`, `ψ` |
| **The Mock Theta Conjectures** (Hickerson 1988; Andrews–Garvan form) | `f₀(q) = θ₄(0,q⁵)/((q;q⁵)_∞(q⁴;q⁵)_∞) − 2Φ(q²)` and `f₁(q) = θ₄(0,q⁵)/((q²;q⁵)_∞(q³;q⁵)_∞) − 2q⁻¹Ψ(q²)`, `f₀ = Σ q^{n²}/(−q;q)ₙ`, `f₁ = Σ q^{n²+n}/(−q;q)ₙ` (`MTC.mock_theta_conjecture_f0`, `MTC.mock_theta_conjecture_f1`) |
| **The χ₀ mock theta conjecture and Andrews–Garvan's rank statement** (via Watson 1937) | `χ₀(q) − 2 = 3(Φ(q) − 1) − (q⁵;q⁵)²_∞J_{5,2}/J_{5,1}²` and `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀(q)` for `n ≥ 1`, `χ₀ = Σ qⁿ/(q^{n+1};q)ₙ` (`Watson.chi0_identity`, `MTC.Chi0L.rank_chi0`) |
| **Watson's fifth-order relations** (Ramanujan's last letter; Watson 1937) | `χ₀(q) = 2F₀(q) − φ₀(−q)`, `f₀(q) + ϑ₄(q)G(q) = 2φ₀(−q²)`, `f₀(q) − ϑ₄(q)G(q) = 2qψ(q²)H(q⁴) − 2(F₀(q²)−1)` (`Watson.chi0_R1_watson`, `Watson.watson_2_0`, `Watson.watson_3_0`) |
| **Ramanujan's first series for `1/π`** (1914) | `Σ_{n≥0} (6n+1)((1/2)_n)³/(n!³4ⁿ) = 4/π` (`RamanujanPi.ramanujan_first_pi_series`); also `Σ (−1)ⁿ(6n+1)((1/2)_n)³/(n!³8ⁿ) = 2√2/π` (`RamanujanPi.ramanujan_pi_series`) |
| **Rademacher's exact formula** (1937) | `p(n) = Σ_{k≥1} A_k(n)·(π/12k)^{3/2}·2π·4(u_k cosh u_k − sinh u_k)/(√π u_k³ k)`, `u_k = (π/k)√((2/3)(n−1/24))`, as a convergent series (`Rademacher.rademacher_dedekind`). Here `A_k(n) = Σ_{(h,k)=1} e^{πi s(h,k) − 2πinh/k}` is Rademacher's Kloosterman sum, with `s(h,k)` the Dedekind sum. Dedekind's reciprocity law is proved too (`Rademacher.dsum_reciprocity`) |
| **Log-concavity of `p(n)`** (DeSalvo–Pak 2015) | `p(n−1)p(n+1) < p(n)²` for every `n ≥ 26`, and it fails at every odd `n ≤ 25` (`LogConcave.partition_logConcave`, `logConcave_fails`). The proof uses an explicit Lehmer-type bound `\|p(n) − Ke^U(U−1)/(2U³)\| ≤ Ke^{U/2}`, read off Rademacher's series |
| **The Hardy–Ramanujan asymptotic formula** (1918) | `p(n) ~ e^{π√(2n/3)}/(4n√3)` for the honest partition count `p(n) = #(Nat.Partition n)` (`HardyRamanujan.hardy_ramanujan_isEquivalent`; ratio form `hardy_ramanujan`) |
| **Partition entropy and Cardy saddle normalization** | For the same count, `log p(n) − π√(2n/3) + log n → −log(4√3)` and `log p(n)/√n → π√(2/3)` (`HardyRamanujan.entropy_log_correction`, `entropy_sqrt_limit`). The saddle at `C=1/12`, `E=n≥1` has this leading exponent (`partition_cardy_leading`, `partition_saddle_minimum`). No black-hole state identification is asserted. |
| **Colored partition entropy and reciprocal discriminant** | For each fixed natural `k>0`, `log p_k(n)/√n → π√(2/3)√k`, where `p_k` is an actual finite count (`ColoredPartitions.entropy_sqrt_limit`). The generating-series coefficient bridge is exact. At 24 colors, `d(n)=p_24(n+1)` gives the nonnegative-charge coefficients of `1/Δ`, and `log d(n)/√n → 4π` (`degeneracy_entropy`); its ratio to the Cardy leading term at `C=2` tends to 1 (`degeneracy_cardy_ratio`). |
| **Bosonic occupation numbers and shell dimensions** | `BosonicOccupation.stateEquivPartition` identifies finite-support occupation arrays of energy `N` with `k`-colored partitions of `N`. The complex shell space has an occupation-number orthonormal basis and dimension `p_k(N)` (`occupationBasis`, `shell_finrank`). With 24 species and specified charge `energy−1`, `charge_finrank` gives dimension `p_24(n+1)` and `charge_entropy` gives its log-dimension divided by `√n` tending to `4π`. |
| **Algebraic oscillator relations and spectrum** | The polynomial representation has `[A_a,C_b]=δ_ab I`, commuting creation operators and commuting annihilation operators, and `[H,C_a]=ω_a C_a`, `[H,A_a]=−ω_a A_a` (`BosonicOscillator.annihilate_create`, `create_create`, `annihilate_annihilate`, `hamiltonian_create`, `hamiltonian_annihilate`). `energySpaceEquivShell` identifies the actual energy eigenspaces with the finite occupation shells; `chargeEigenspace_entropy` proves the `4π` limit for the eigenspaces of the specified `H−I`. |
| **Normalized finite-shell Hilbert adjoints** | The polynomial basis `X^d/√(∏_a d_a!)` has creation coefficient `√(d_a+1)` and annihilation coefficient `√d_a`. The independently defined polynomial operators restrict to finite energy shells, and `BosonicOscillator.annihilateShell_eq_adjoint` proves `annihilateShell a n = (createShell a n).adjoint`. The shell dimensions remain `p_k(n)` (`normalizedShell_finrank`). |
| **Atkin–O'Brien-type congruences for ℓ = 13, 17, 19, 23 valid at `b = m`** | ∃ κ ∈ ℤ_ℓ: `ℓ^m ∣ p((ℓ^{m+2}n+1)/24) − κ·p((ℓ^m n+1)/24)` for all m ≥ 1 and n ≥ 0 with `24 ∣ ℓ^m n + 1` (`OrdQuot.atkin_obrien_13/17/19/23`, no additional operator-bound hypotheses). Uses formal layers for formal groups of elliptic curves, Lubin quotients, the canonical subgroup, Katz expansions, Igusa, Deligne, Ramanujan's ODEs, Vélu, the Tate curve and Hecke operators. See [the proof record](ATKIN_OBRIEN_PROOF.md). The displayed theorem proves sufficiency at `b = m`; minimality is a separate assertion. **Awaiting expert review.** |
| **Ramanujan's conjecture for powers of 11** (Atkin 1967) | `24m ≡ 1 (mod 11ʳ)`, `r ≥ 1` ⟹ `11ʳ ∣ p(m)` (`Atkin11.ramanujan_pow11_unconditional`). All three Atkin–Gordon inputs are proved: the degree-11 modular equation for `φ = q⁵E(q¹²¹)/E(q)` (`modeq_proved`), the curve relation R2 (`r2_proved`) and the 55 seed rows (`Atkin11Seed.seeds_proved`) |
| **Ramanujan's value `R(e^{−2π})`** (first letter to Hardy, 1913) | `e^{−2π/5}(q;q⁵)_∞(q⁴;q⁵)_∞/((q²;q⁵)_∞(q³;q⁵)_∞) = √((5+√5)/2) − (√5+1)/2` at `q = e^{−2π}` (`RRValue.rogers_ramanujan_value`) |
| **Ramanujan's deathbed claim at `q → −1`** (last letter to Hardy, 1920) | `f(q) + b(q) → 4` as `q → −1` radially, `f = Σ q^{n²}/(−q;q)ₙ²`, `b = (1−q)(1−q³)⋯(1−2q+2q⁴−⋯)` (`MockTheta3.Radial.ramanujan_radial_limit`) |
| **Watson's third-order identities** (1936) | `2φ(−q) − f(q) = b(q)` and `f(q) + 4ψ(−q) = b(q)` (`MockTheta3.Watson3.watson_W1`, `watson_W2`) |
| **`f(q)` counts rank parity** | `[qⁿ] f(q) = N(0,2,n) − N(1,2,n)` (`MockTheta3.f3_rank`) |
| **Andrews' Hecke-type identities for `f₀`, `f₁`** | `(q;q)_∞f₀ = ΣΣ_{\|j\|≤n}(−1)ʲq^{n(5n+1)/2−j²}(1−q^{4n+2})`, `(q;q)_∞f₁ = ΣΣ(−1)ʲq^{n(5n+3)/2−j²}(1−q^{2n+1})` |
| **Hickerson–Mortenson Theorem 0.3 for `f_{3,7,3}`** at the MTC₀ and MTC₁ points | Hecke-type double sum = Appell–Lerch sums + theta quotient (`MTC.hm03_xstar`, `MTC.hm03_x1`) |
| **Partition-count bridge** | `[qⁿ] 1/(q;q)_∞ = #(Nat.Partition n)` — `p(n)` is the honest count |
| **Euler's recurrence** | `p(n) = p(n−1)+p(n−2)−p(n−5)−p(n−7)+⋯` |
| **Ramanujan's theta functions** | `φ(q)=Σq^{n²}`, `ψ(q)=Σq^{n(n+1)/2}`, `f(−q)=(q;q)_∞`, with product forms |
| **Canonical quintuple family** | For every odd `p ≥ 5`, `∏_{i=1}^{(p-1)/2}Q(qⁱ,qᵖ)` vanishes in every nonsquare class mod `p` |
| **Three quintuple products (`p=7`)** | `[q^{7n+r}] Q(q,q⁷)Q(q²,q⁷)Q(q³,q⁷) = 0` for `r=3,5,6` |
| **Infinite sparse quintuple family** | For `p=9t²+15t+7`, `[q^{pN+3t+3}] Q(q,qᵖ)Q(q^{3t+2},qᵖ)Q(q^{3t+3},qᵖ)=0` for all natural `t,N`, including composite p |
| **Root--Vanishing classification** | For every admissible sparse triple and canonical residue, persistent vanishing is equivalent to an exact projective root certificate |


Build instructions and current verification status are maintained in the [overview](../README.md) and [status page](STATUS.md).

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

### `PartitionCongruenceMod11.lean` — Ramanujan's third congruence
```lean
theorem eleven_dvd_partition_card (n : ℕ) : 11 ∣ Fintype.card (Nat.Partition (11*n+6))
theorem eleven_dvd_coeff_qfac10 (a : ℕ) (ha : a % 11 = 6) : (11 : ℤ) ∣ coeff a (qfacInf ^ 10)
```
Mod 11 needs more than a product of Jacobi series: classically it is Winquist's two-variable identity.
Here a one-variable form of Winquist's argument is used instead. With
`R_N = Σ_{n₁+n₂+n₃=N} q^{Σ nᵢ(nᵢ−1)/2}` (the `z^N`-slice of `triTheta³`):

* `L3` (the third `d/dz` at `z = −1`) of the triangular JTP cubed gives `6·(q;q)_∞⁹ = Σ_N w₃(N)·R_N`.
* Shifting all indices by 1 gives `R_{N+3} = q^N R_N`, and `n ↦ 1−n` gives `R_{3−N} = R_N`.
  So every slice is a `q`-shift of `R₀` or `R₁`.
* Winquist's specialization `a = q^{1/3}` regroups the triple sum into Euler's pentagonal series cubed.
  This identifies `(q;q)_∞·R₀` and `(q;q)_∞·R₁` as the exponent-mod-3 parts (residues 0 and 1) of
  Jacobi's `(q;q)_∞³`.
* At `q^a` with `a ≡ 6 (mod 11)`, each term carries a Jacobi weight `±(2n+1)` with
  `(2n+1)² + y² = 24a + 10 ≡ 0 (mod 11)`. Since `−1` is a non-residue mod 11, `11 ∣ 2n+1`.
* The char-11 Frobenius `1/(q;q) ≡ (q;q)¹⁰/(q¹¹;q¹¹) (mod 11)` (a port of the mod-7 file) finishes the proof.

Fully unconditional; axioms `[propext, Classical.choice, Quot.sound]`; no `native_decide`.

### `RankMod5.lean` (+ `RankBailey`, `RankGF`, `RankHR1`, `RankHR2*`, `RankTheta`, `RankDissect`) — Dyson's rank mod 5
```lean
theorem rank_equidistribution_mod5 (n : ℕ) {i : ℕ} (hi : i < 5) :
    5 * (univ.filter fun l : (5*n+4).Partition => rank l % 5 = i).card = Fintype.card (5*n+4).Partition
```
Dyson's 1944 conjecture, first proved by Atkin and Swinnerton-Dyer (1954). The proof follows Garvan's
2020 approach (arXiv 2012.06676):

1. **Rank generating function** (`rank_durfee`): `Σ_{λ⊢n} z^{rank λ} = [qⁿ] Σ_k q^{k²}/((zq)_k(q/z)_k)`,
   on Mathlib's `Nat.Partition`.
2. **Hecke–Rogers (2.18)** (`hecke_rogers_18`): Euler-expand `(zq^{k+1})_∞(q^{k+1}/z)_∞`, regroup by
   `a = i − j`, and sum each block with a finite Bailey pair relative to `a = qᵏ` (telescoping certificate).
3. **Hecke–Rogers (2.19)** (`hecke_rogers_19`): odd Euler + odd Jacobi product, then the base-`q²` (2.18).
   The remaining identity is a signed lattice-point count, closed by an explicit involution of `ℤ²`
   (rotation in `ℤ[(1+√−3)/2]`) applied per exponent.
4. **Endgame at `ζ = ζ₅`**: Jacobi triple products `J_{a,b}`, their 5-dissections as lattice sums, and three
   linear equations for the dissection components of `R(ζ;q²)`. Two product identities force `R₃ = 0`.
   This gives `Σ_{λ⊢5n+4} ζ^{rank λ} = 0`, and the cyclotomic step finishes.

### `RankASD5.lean` — Atkin–Swinnerton-Dyer rank equalities mod 5
```lean
theorem rank_mod5_ASD (n : ℕ) :
    rankCount (5*n+1) 1 = rankCount (5*n+1) 2 ∧ rankCount (5*n+2) 0 = rankCount (5*n+2) 2
```
These follow directly from the Lost Notebook dissection: `R₁` has no `ζ`, and `R₂ = (ζ+ζ⁴)·(integer series)`. Since the
minimal polynomial of `ζ₅` is `Φ₅`, an integer relation `Σ c_k ζ₅^k = 0` forces all `c_k` to be equal (`cyc_equalZ`).
Together with the `5n+4` theorem, these are all the equalities that hold in every residue class (checked numerically).

### `SptMoment.lean` — Andrews' spt identity in moment form
```lean
theorem crank_moment_sub_rank_moment {m : ℕ} (hm : 2 ≤ m) :
    (∑ l : m.Partition, crank l ^ 2) - (∑ l : m.Partition, rank l ^ 2) = 2 * spt m
```
This is `M₂(n) − N₂(n) = 2·spt(n)`. With Dyson's `M₂(n) = 2n·p(n)` it becomes Andrews'
`spt(n) = n·p(n) − ½N₂(n)`. The spt-crank identity holds coefficientwise in `ℤ[z,z⁻¹]`, because a Laurent
polynomial that vanishes at every unit of `ℂ` is zero. The second-moment functional sends `(2 − z − z⁻¹)·L` to
`−2·L(1)`.

### `RankDiff5.lean` — the rank-difference generating functions mod 5 are mock theta functions
```lean
theorem rank_diff_mod5 (n : ℕ) :
    N(1,5n) − N(2,5n) = [qⁿ] φ ∧ N(0,5n) − N(2,5n) = [qⁿ](J₅²·J_{5,2}/J_{5,1}²) − 2[qⁿ]φ ∧
    N(1,5n+1) = N(2,5n+1) ∧ N(0,5n+1) − N(2,5n+1) = [qⁿ](J₅²/J_{5,1}) ∧
    N(0,5n+2) = N(2,5n+2) ∧ N(1,5n+2) − N(2,5n+2) = [qⁿ](J₅²/J_{5,2}) ∧
    N(0,5n+3) − N(2,5n+3) = −[qⁿ⁺¹] ψ ∧ N(1,5n+3) − N(2,5n+3) = −2[qⁿ⁺¹]ψ − [qⁿ](J₅²·J_{5,1}/J_{5,2}²)
```
These are the Atkin–Swinnerton-Dyer generating functions for the rank differences mod 5 (with `N(k,·)` the count
`rankCount`, and `N(k) = N(5−k)` by conjugation; `5n+4` is equidistribution). Here
`φ = Σ q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n) − 1` and `ψ = Σ q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n) − 1` are Ramanujan's
fifth-order mock theta functions. The theorem reads them off the Lost Notebook dissection through `cyc_shift5`: if
`Σ N_k ζ₅^k = Σ a_k ζ₅^k` with integers `a_k`, then all the `N_k − a_k` are equal.

### `ALRank7Main.lean` (+ `ALBase`…`ALSplitM`, `ALThetaCore`, `ALCore7`, `ALNewForm`, `ALClass7`, `ALRank7Pre`) — Dyson's rank mod 7
```lean
theorem rank_equidistribution_mod7 (n : ℕ) {i : ℕ} (hi : i < 7) :
    7 * (univ.filter fun l : (7*n+5).Partition => rank l % 7 = i).card = Fintype.card (7*n+5).Partition
```
This proof does not follow Atkin–Swinnerton-Dyer. It works with Appell–Lerch sums over `ℂ((t))` (Hahn series):

1. **New formula** (`newform`): `R(ζ;q)·θ = (1−ζ)(θ − m₂ − ζ⁶m₁)`, where `m₁, m₂` are Appell–Lerch sums `m(x,q,z)`.
   It is proved from five Weierstrass three-term instances.
2. **7-split** (`m_split_msum`): each `m` is rewritten as seven `m`'s at base `q^{147}` plus theta corrections.
3. **Decomposition** (`decomp`): `R(ζ) = (1−ζ)(1 − m-sum₂ − ζ⁶ m-sum₁) + Θ_g`.
   The theta corrections are matched to an explicit `Θ_g` by the 38 level-21 class identities of `ALCore7`
   (62 Weierstrass instances), modulo `Φ₇(ζ)`.
4. **Class-5 vanishing** (`rank7_no5`): every mock summand is class-pure. Exactly one summand in each `m`-sum
   has class 5, and those two cancel by `m(q^{-49},q^{140}) = q^{49} m(q^{49},q^{7})` (`orbit7`).
   `Θ_g` has no class-5 exponents. Hence `Σ_{λ⊢7n+5} ζ₇^{rank λ} = 0`, and the cyclotomic step finishes.

Axioms `[propext, Classical.choice, Quot.sound]`.

### `ALRankASD7.lean` (+ `ALRankASD7Count`) — Atkin–Swinnerton-Dyer rank equalities mod 7
```lean
theorem rank_mod7_ASD (n : ℕ) :
    N(2,7n) = N(3,7n) ∧ N(1,7n+1) = N(2,7n+1) = N(3,7n+1) ∧ N(0,7n+2) = N(3,7n+2) ∧
    N(0,7n+3) = N(2,7n+3) ∧ N(1,7n+3) = N(3,7n+3) ∧ N(0,7n+4) = N(1,7n+4) = N(3,7n+4)
```
Here `N(k,m)` is `rankCount7 m k`. These are all the equalities that hold in every residue class (checked numerically);
the class `7n+5` case is the theorem above. `decomp` is rewritten in a canonical form
`R(ζ) = Σ_t C(P_t(ζ))·G_t`, with 31 `ζ`-free, class-pure pieces `G_t` and integer coefficient vectors for the `P_t`.
A discrete Fourier transform over the seven roots of unity (`rank_eq_of_decomp`) turns `v_{t,a} = v_{t,b}`, for every
piece of class `c`, into `N(a,7,7n+c) = N(b,7,7n+c)`. That condition is finite data and is checked by `decide`.
Axioms `[propext, Classical.choice, Quot.sound]`.

### `SptFinal.lean` (+ `SptT`, `SptSeries`, `SptGF`) — Andrews' spt congruences mod 5 and 7
```lean
theorem spt_mod5 (n : ℕ) : 5 ∣ spt (5 * n + 4)
theorem spt_mod7 (n : ℕ) : 7 ∣ spt (7 * n + 5)
```
`spt(n)` is the total number of smallest parts over all partitions of `n` (Andrews 2008). The proof avoids
second moments and Andrews' `spt(n) = np(n) − ½N₂(n)`. Instead:

1. **Finite identity** (`SF_eq_TS`, any field): `Σ_{r≤n} q^{r²}α_r (zq)_n(q/z)_n/((q)_{n−r}(q)_{n+r}) = Σ_{j≤n} (z)_j(z⁻¹)_j q^j/(q)_j`.
   Here `α_r` are the Appell–Lerch weights of `rank_AL`. It is proved by creative telescoping against the second-order
   recurrence of the right side, with an explicit certificate. Each local step is a rational identity, closed by
   abstracting the denominator factors, then `field_simp`, `subst` and `ring`.
2. **Spt-crank identity** (`rank_sub_crank`): letting `n → ∞` and using `rank_AL` gives
   `R(z) − C(z) = (1−z)(1−z⁻¹)·C(z)·U(z)` in `ℂ⟦q⟧`, where `C` is the crank product and
   `U = Σ_{j≥1}(zq)_{j−1}(q/z)_{j−1}q^j/(q)_j`.
3. **Integrality**: `S = C·U` lifts to `ℤ[z,z⁻¹]⟦q⟧`. At `z = 1` its coefficients are `spt(n)` (`spt_gf`, via
   Mathlib's `Nat.Partition.genFun` with weights `[parts ≥ k]·(count_k+1)` and `[parts ≥ k]`).
4. **Roots of unity**: at `z = ζ₅`, `n = 5m+4`, both rank and crank sums vanish, so `[qⁿ]S(ζ₅) = 0`. The integer
   Laurent coefficients, grouped by exponent mod 5, are then all equal (`Φ₅` is the minimal polynomial), so
   `spt(n) = 5·(group sum)`. The same argument works mod 7 with `ζ₇`.

Axioms `[propext, Classical.choice, Quot.sound]`.

### `RankR03.lean` (+ `RankRamanujan5`, `RankSpec`, `RankP2`) — Ramanujan's rank dissection
```lean
theorem lost_notebook_rank_mod5 :
    Rk 0 = ψ (eQ^2 * Jab 5 2 * (Jab 5 1)⁻¹^2) + C (tζ - 2) * ψ (Phi 1 - 1) ∧ Rk 1 = ψ (eQ^2 * (Jab 5 1)⁻¹)
    ∧ Rk 2 = C tζ * ψ (eQ^2 * (Jab 5 2)⁻¹) ∧ X * Rk 3 = C (sζ - tζ) * ψ (Phi 2 - 1) + C (sζ + 1) * X * ψ (…)
    ∧ Rk 4 = 0
```
The full mod-5 rank identity from p. 20 of Ramanujan's Lost Notebook (Garvan (4.1)). Here `Rk k` is the
`k`-th 5-dissection component of `R(ζ₅;q)`, and `Phi 1 = 1+φ`, `Phi 2 = 1+ψ` are Ramanujan's mock theta functions
`Σ q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n)` and `Σ q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n)`.

- `R₁, R₂, R₄` come from the mod-5 linear system and the product identities.
- `R₀, R₃` avoid Garvan's (2.20). Instead:
  1. (2.18) is re-proved at `z = qᵏ` in base `q⁵` (`spec_coeff`), giving `J_{5,k}·Φ_k` as a Hecke-type sum.
  2. Five explicit index bijections (`bij_i`–`bij_v`) identify one orbit of the class-1 / class-3 parts of
     (2.18) with `J_{5,1}φ` and `J_{5,2}ψ` (`orbit_mock`).

### `RankAL.lean` — the Appell–Lerch (Lambert) form of the rank generating function
```lean
theorem rank_AL {z : ℂ} (hz : z ≠ 0) : Dser z z⁻¹ = ψ (Ring.inverse qfacInf) * ALser z
```
`(q;q)_∞ · Σ_n q^{n²}/((zq;q)_n(q/z;q)_n) = 1 + Σ_{r≥1} (−1)^r q^{r(3r+1)/2}(1+q^r)(1−z)(1−z⁻¹)/((1−zq^r)(1−q^r/z))`.
The proof uses the Bailey pair relative to `a = 1` with `β_n = 1/((zq)_n(q/z)_n)`. Its finite form (`al_pair`) is proved in any
field by a telescoping certificate, then moved to `ℂ⟦X⟧`, and the limit is taken with `durfee_rect_base`.
This is milestone 1 of the rank mod-7 programme.

### `ALBase.lean`, `ALChangeZ.lean` — change of `z` for Appell–Lerch sums
```lean
theorem change_of_z ... :
    θ(z₀)θ(xz₀)θ(xz₁)A(x,z₁) − A(x,z₀)θ(xz₀)θ(z₁)θ(xz₁) + z₀ κ θ(z₁/z₀) θ(xz₀z₁) = 0
```
This is Hickerson–Mortenson's change-of-`z` theorem, `m(x,q,z₁) − m(x,q,z₀) = −z₀κ θ(z₁/z₀)θ(xz₀z₁)/(θ(z₀)θ(z₁)θ(xz₀)θ(xz₁))`,
with `κ = θ(x)A(x,1)`. It is proved in `ℂ((t))` for monomial points `x = c t^a`, `zᵢ = cᵢ t^{bᵢ}`, `q = t^N`, in the
range `0 < val(xz) < N`. The proof is a formal theta-function uniqueness argument with no analysis:
- `F(z) = θ(xz)A(x,z) − m₀θ(z)θ(xz) + cθ(z/z₀)θ(xz₀z)` is a bilateral `z`-series with `F_{k+2} = q^k x F_k` (`AA_rec`, `TT_rec`).
- So `F = F₀E₀ + F₁E₁` (`sol_basis`).
- `F` vanishes at `z = 1` and `z = z₀`, and the 2×2 determinant has an explicit nonzero leading term (`det_ne`).
- Hence `F ≡ 0`. The sums are `HahnSeries.SummableFamily` sums, and the Appell sum is expanded on its geometric cone.

### `CrankAndrewsGarvan.lean` — Dyson's crank: the combinatorial explanation of mod 5 and mod 7
```lean
theorem crank_generating_function {z : ℂ} (hz : z ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∑ l : n.Partition, z ^ crank l = coeff n (pochInf 1 1 * Ring.inverse (pochInf z 1 * pochInf z⁻¹ 1))
theorem crank_equidistribution_mod5 (n : ℕ) {i : ℕ} (hi : i < 5) :
    5 * (univ.filter fun l : (5*n+4).Partition => crank l % 5 = i).card = Fintype.card (5*n+4).Partition
theorem crank_equidistribution_mod7 (n : ℕ) {i : ℕ} (hi : i < 7) :
    7 * (univ.filter fun l : (7*n+5).Partition => crank l % 7 = i).card = Fintype.card (7*n+5).Partition
```
Dyson conjectured a statistic that splits the partitions of `11n+6` into 11 equal classes. Andrews and
Garvan found it: for a partition with `ω` ones and `μ` parts larger than `ω`, the crank is the largest
part if `ω = 0`, and `μ − ω` otherwise. The same statistic also splits `5n+4` and `7n+5`. The crank is
defined directly on Mathlib's `Nat.Partition`.

1. **Generating function.** The `q`-binomial theorem is proved from its functional equation and an
   `X`-adic limit, together with Euler's identity. Splitting each partition by its number of ones and
   matching weights against `Nat.Partition.genFun` gives the two-variable product.
2. **At a root of unity.** Multiply through by the missing `(ζʲq;q)_∞`. The denominator becomes
   `∏_{j<p}(ζʲq;q)_∞ = (q^p;q^p)_∞`, from Mathlib's `X^p − a = ∏(X − ζʲα)` evaluated at `X = 1`. The
   numerator pairs into the triangular Jacobi triple product evaluated at `u = −ζʲ`.
3. **Vanishing.** In `Σ_m uᵐ q^{m(m−1)/2}` with `uᵖ = −1`, the terms `m` and `1−m` cancel whenever
   `p ∣ 2m−1`. For `p = 5` this is combined with the empty pentagonal classes of `(q;q)_∞`. For `p = 7`
   it is applied to `Θ(−ζ²)Θ(−ζ³)`, using that `−1` is a non-residue mod 7.
4. **Cyclotomic step.** `minpoly ℚ ζ = Φ_p` has degree `p−1`, so `Σ_k N_k ζᵏ = 0` forces all `N_k` equal.

Mod 11 is in `CrankWinquistMod11.lean` (below).

### `CrankWinquistMod11.lean` — Winquist's identity and the crank mod 11
```lean
theorem winquist {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Jx a * Jx b * Jx (a * b) * Jx (a / b) = Wlat a b * (Elat * Elat)
theorem crank_equidistribution_mod11 (n : ℕ) {i : ℕ} (hi : i < 11) :
    11 * (univ.filter fun l : (11*n+6).Partition => crank l % 11 = i).card = Fintype.card (11*n+6).Partition
```
This proves Dyson's 1944 conjecture in the form Garvan established in 1988: the crank splits `11n+6` into
11 equal classes. The key input is Winquist's identity. It is proved here as a reindexing of `ℤ⁴`, with
no functional equations and no analysis:

* In each `(N, M)`-fibre (`N`, `M` = the degrees in `a` and `b`) the quadratic form is `3/2·(s²+t²)`
  plus linear terms.
  * An affine shift turns the fibre into a pair of pentagonal series, i.e. `±q^e·(q;q)_∞²` by Euler.
  * Otherwise a reflection cancels the fibre.
* The surviving exponents satisfy `24e+10 = (2N−3)²+(2M−1)²`. In the class `11n+6` this forces
  `11 ∣ 2N−3` (because `−1` is a non-residue mod 11), and `N ↦ 3−N` then cancels the class.

The lattice sums are `tsum`s in `ℂ⟦X⟧` under the coefficientwise topology. The small API (`lat_mul`,
`lat_equiv`, `lat_fubini`, `lat_eq_zero_of_invol`) is reusable for other theta-product identities.

### `Ramanujan7Identity.lean` — Ramanujan's mod-7 identity, and `49 ∣ p(49n+47)`
```lean
theorem ramanujan_identity_mod7 :
    (PowerSeries.mk fun n => (Fintype.card (Nat.Partition (7*n+5)) : ℤ)) * qfacInf ^ 8
      = 7 * (E7 qfacInf) ^ 3 * qfacInf ^ 4 + 49 * X * (E7 qfacInf) ^ 7
theorem fortynine_dvd_partition_card (n : ℕ) : 49 ∣ Fintype.card (Nat.Partition (49*n+47))
```
This is the 7-analogue of the "most beautiful identity".
* Euler's product dissects as `E = E(q⁴⁹)(x − qy − q² + q⁵z)`.
* Jacobi's cube has no exponents `≡ 2, 4, 5 (mod 7)`, which gives three relations among `x, y, z`.
  These imply `xyz = 1`.
* The norm over the 7th roots of unity is `E(q⁷)⁸/E(q⁴⁹)`. A degree-35 polynomial identity, checked
  once in `Ramanujan7Norm.lean` (about 10 minutes), says it equals `N(x,y,z,q⁷)`.
* `F = x³y + Qy³z − Q²xz³ − 8Q` satisfies `F² = N`, so `F = (E(q⁷)/E(q⁴⁹))⁴`.
* The `q^{≡5}` part of the inverted factor is `7q⁵(F + 7q⁷)`, which gives the identity.
* The mod-49 congruence follows from the identity, the char-7 Frobenius, and `7 ∣ 2k+1` on the class-6
  terms of Jacobi's cube.

### `Pow5Final.lean` (+ `Pow5`, `Pow5Stage`) — Ramanujan's conjecture for all powers of 5 (Watson 1938)
```lean
theorem ramanujan_pow5 (k m : ℕ) (hm : 24 * m ≡ 1 [MOD 5 ^ k]) : 5 ^ k ∣ Fintype.card (Nat.Partition m)
```
This holds for every `k`: `5 ∣ p(5n+4)`, `25 ∣ p(25n+24)`, `125 ∣ p(125n+99)`, `625 ∣ p(625n+599)`, …
The proof follows Hirschhorn–Hunt, built on the 5-dissection of `RamanujanMostBeautiful`, and needs no roots of unity:

1. **Watson's modular equation** (`modular_eq`): with `y = qE(q²⁵)/E(q)` and `τ = qE(q⁵)⁶/E(q)⁶`,
   `y⁵ = τ(q⁵)·(25y⁴ + 25y³ + 15y² + 5y + 1)`. It is a polynomial identity in `A, B, q` modulo `AB = 1`.
2. **`U₅(yᵏ) = Σ_j m_{k,j} τʲ`** (`Ys_dis`): the cases `k ≤ 4` are polynomial identities through the inversion
   polynomial `𝒬`, and the modular equation gives a five-term recurrence for `k ≥ 5`.
3. **5-adic bound** (`mc_dvd`): `ν₅(m_{k,j}) ≥ ⌊(5j − k − 1)/2⌋`, together with `m_{k,j} = 0` unless `k ≤ 5j ≤ 5k`.
4. **Stages** (`trans_even`, `trans_odd`): `L_k = Σ_n p(5ᵏn + δ_k)qⁿ⁺¹` alternates between `(1/E)·b(τ)` and
   `(1/E(q⁵))·a(τ)`, with `a_l = Σ_s b_s m_{6s+1,l+s}` and `b_s = Σ_l a_l m_{6l,s+l}`. Each transition is proved
   by multiplying by `τ(q⁵)^M`, using `τ(q)τ(q⁵) = y⁶`, applying `U₅`, reindexing in `ℤ[X]`, and cancelling.
5. **Invariant** (`stagePoly_dvd`): `ν₅(coeff_i L_k) ≥ k + ⌊(5i−5)/2⌋`, so `5ᵏ` divides all of `L_k`.
   Finally `24δ_k ≡ 1 (mod 5ᵏ)` and `δ_k < 5ᵏ`.

Axioms `[propext, Classical.choice, Quot.sound]`.

### `Pow7Final.lean` (+ `Pow7`, `Pow7B`, `Pow7Pm`, `Pow7Mod`, `Pow7Stage`) — Watson's congruences for powers of 7
```lean
theorem ramanujan_pow7 {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (hm : 24 * m ≡ 1 [MOD 7 ^ k]) :
    7 ^ ((k + 2) / 2) ∣ Fintype.card (Nat.Partition m)
```
This is Ramanujan's conjecture for 7, as corrected by Watson (1938): `7 ∣ p(7n+5)`, `49 ∣ p(49n+47)`,
`49 ∣ p(343n+243)`, `343 ∣ p(2401n+2301)`, …  The proof follows Garvan (1984) and has the same structure as the
powers-of-5 proof, built on the 7-dissection `E = E(q⁴⁹)·L₇(x, y, z)`:

1. **Modular equation** (`modular7_eq`): with `y = q²E(q⁴⁹)/E(q)` and `τ = qE(q⁷)⁴/E(q)⁴`,
   `y⁷ = τ(q⁷)(49y⁶+35y⁵+7y⁴) + τ(q⁷)²(343y⁶+343y⁵+147y⁴+49y³+21y²+7y+1)`. It is proved as a polynomial
   identity modulo the four relations of the 7-dissection, with a sympy-generated certificate.
2. **`U₇(yᵏ) = Σ_j m_{k,j} τʲ`** (`Y7_dis`): the cases `k ≤ 6` are computed class by class through the
   product rule `dis7_mul`, and the modular equation gives a seven-term recurrence for larger `k`.
3. **7-adic bound** (`mc7_dvd`, Garvan): `ν₇(m_{k,j}) ≥ ⌊(7j − 2k − 1)/4⌋`, together with `m_{k,j} = 0`
   unless `2k ≤ 7j ≤ 14k`.
4. **Stages** (`trans_even7`, `trans_odd7`): `a_l = Σ_s b_s m_{4s+1,l+s}` and `b_s = Σ_l a_l m_{4l,s+l}`.
5. **Invariant** (`stagePoly7_dvd`): `4d + 3 + 2(k mod 2) ≤ 2k + 7i ⇒ 7ᵈ ∣ coeff_i L_k`.
   This gives `7^⌊(k+2)/2⌋` for every `i ≥ 1`. Finally `24δ_k = (17 or 23)·7ᵏ + 1` and `δ_k < 7ᵏ`.

Axioms `[propext, Classical.choice, Quot.sound]`.  Note: `Pow7.lean` takes about an hour to compile, because of
the class-by-class `k ≤ 6` base cases.

### `DysonM2.lean` — Dyson's crank moment `M₂(n) = 2n·p(n)`, Euler's σ-recurrence, Andrews' `spt = np − ½N₂`
```lean
theorem euler_sigma_sum (n : ℕ) :
    (n : ℤ) * Fintype.card n.Partition
      = ∑ x ∈ antidiagonal n, (Fintype.card x.1.Partition : ℤ) * (ArithmeticFunction.sigma 1 x.2 : ℤ)
theorem crank_moment_two {n : ℕ} (hn : 2 ≤ n) :
    ∑ l : n.Partition, crank l ^ 2 = 2 * n * (Fintype.card n.Partition : ℤ)
theorem spt_eq_np_sub_rank_moment {n : ℕ} (hn : 2 ≤ n) :
    2 * (spt n : ℤ) = 2 * n * (Fintype.card n.Partition : ℤ) - ∑ l : n.Partition, rank l ^ 2
```
Both moment identities are first-order computations over the dual numbers `ℤ[ε]`:
* **Euler**: the substitution `q ↦ (1+ε)q` (`rescale`) sends `(q;q)_∞` to `(q;q)_∞(1 − ε Σ_d d qᵈ/(1−qᵈ))` and sends
  `p(n)` to `p(n)(1 + nε)`.
* **Dyson**: since `(1−zqᵈ)(1−qᵈ/z) = (1−qᵈ)² + w qᵈ` with `w = 2 − z − z⁻¹`, every coefficient of the crank
  generating function is a polynomial `f(w)`, and the second moment of `f(2 − z − z⁻¹)` is `−2f′(0)`
  (`mom2_ιW`). Mapping `w ↦ ε` gives `∏((1−qᵈ)² + εqᵈ) = (q;q)²(1 + ε Σ qᵈ/(1−qᵈ)²)`.
Both divisor sums equal `Σ σ(k)qᵏ`. Combined with `crank_moment_sub_rank_moment` (`M₂ − N₂ = 2 spt`), this gives
Andrews' original definition `spt(n) = n·p(n) − ½N₂(n)`. Axioms `[propext, Classical.choice, Quot.sound]`.

### `Kolberg.lean` — Kolberg's theorem (1959): `p(n)` is even infinitely often and odd infinitely often
```lean
theorem kolberg (N : ℕ) :
    (∃ n, N ≤ n ∧ Even (Fintype.card (Nat.Partition n))) ∧ (∃ n, N ≤ n ∧ Odd (Fintype.card (Nat.Partition n)))
```
The proof uses Euler's pentagonal recurrence mod 2. If `p ≡ c (mod 2)` from `N` on, set `n = ω(N) + r` with
`r < N`. The pentagonal numbers around `ω(N) = (N+1)(3N+2)/2` are more than `N` apart, so the recurrence collapses
to `p(n) ≡ p(r)`. Every other pair contributes `c + c ≡ 0`. Hence `p(r) ≡ c` for all `r`, which contradicts
`p(0) = 1` and `p(2) = 2`. Axioms `[propext, Classical.choice, Quot.sound]`.

### `RogersRamanujan.lean` — the Rogers–Ramanujan identities (product forms)
```lean
theorem rogers_ramanujan_1 :
    tsumQsq (fun n => Ring.inverse (qfac n)) = Ring.inverse (Pinf 1 5 * Pinf 4 5)   -- Σ q^{n²}/(q)_n = 1/((q;q⁵)(q⁴;q⁵))
theorem rogers_ramanujan_2 :
    tsumQsqQ (fun n => Ring.inverse (qfac n)) = Ring.inverse (Pinf 2 5 * Pinf 3 5)  -- Σ q^{n²+n}/(q)_n = 1/((q²;q⁵)(q³;q⁵))
```
The repo's Bailey-pair transforms reduce the sums to the theta series `Σ q^{n²}αₙ` and `(1−q)Σ q^{n²+n}αₙ`.
These are matched term by term with the Jacobi triple products `J_{5,2}` and `J_{5,1}` (`alphaC_theta`,
`alphaB_theta`), so the quintuple product is not needed. The residue split `(q;q)_∞ = ∏_{r=1}^5 (q^r;q⁵)_∞`
then cancels the denominator. Axioms `[propext, Classical.choice, Quot.sound]`.

### `RogersRamanujanComb.lean` — the Rogers–Ramanujan identities, combinatorial form (MacMahon, Schur)
```lean
-- partitions with parts differing by ≥ 2  ↔  partitions into parts ≡ ±1 (mod 5)
theorem rogers_ramanujan_1_comb (m : ℕ) :
    #(gapTwo m 0) = #(Nat.Partition.restricted m fun i => i % 5 = 1 ∨ i % 5 = 4)
-- parts ≥ 2 differing by ≥ 2  ↔  parts ≡ ±2 (mod 5)
theorem rogers_ramanujan_2_comb (m : ℕ) :
    #(gapTwo m 1) = #(Nat.Partition.restricted m fun i => i % 5 = 2 ∨ i % 5 = 3)
```
`gapTwo m t` is the set of partitions of `m` with distinct parts `≥ t+1`, no two consecutive.
* **Gap side**: such a partition is its set of parts. The `n`-element sets with elements `≥ t+1` satisfy
  `|A(m,n+1,t)| = |A(m,n+1,t+1)| + |A(m−t−1,n,t+2)|`, according to whether `t+1` is a part. This is the
  recursion of `q^{n²+nt}/(q;q)_n` (`card_A`).
* **Product side**: Mathlib's `hasProd_powerSeriesMk_card_restricted`, compared with `(q^{r₁};q⁵)(q^{r₂};q⁵)`
  block by block (five factors at a time).
Axioms `[propext, Classical.choice, Quot.sound]`.

### `FourSquares.lean` (+ `FourSquaresWZ`, `FourSquaresLimit`) — Jacobi's four-square theorem
```lean
theorem jacobi_four_squares {N : ℕ} (hN : 1 ≤ N) :
    r4 N = 8 * ∑ d ∈ N.divisors with ¬4 ∣ d, d
theorem r4_eq_ncard (N : ℕ) :   -- r4 counts all integer solutions
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ)}.ncard = r4 N
```
Mathlib only proves existence (`Nat.sum_four_squares`). This file proves the exact count.
1. **Terminating identity** (`St_eq_one`): the specialization `a = 1, b = c = d = −1` of Jackson's ₈φ₇ gives
   `(−q)ₙ⁴/(q)ₙ⁴ + Σ_{k=1}^n 8(−1)^k q^k/(1+q^k)² · (−q)_{n−k}(−q)_{n+k}(−q)ₙ²/((q)_{n−k}(q)_{n+k}(q)ₙ²) = 1`.
   It is proved by a WZ certificate found with sympy: `G(n,k) ∝ (−q)_{n+1−k}(−q)_{n+k}/((q)_{n+1−k}(q)_{n+k})`.
   The three resulting rational identities are checked in the fraction field of `ℤ⟦q⟧` with `field_simp`.
2. **Limit** (`limit_identity`): working modulo `qᴺ` through the quotient map gives
   `((−q;q)_∞/(q;q)_∞)⁴ (1 + 8 Σ (−1)^k q^k/(1+q^k)²) = 1`.
3. **Gauss** (`theta_mul_mfacInf`): `(q;q)_∞/(−q;q)_∞ = J_{2,1} = Σ (−1)^m q^{m²}`, by the Jacobi triple product
   `jtp_ab 2 1`. Hence `φ(−q)⁴ = 1 + 8 Σ (−1)^k q^k/(1+q^k)²` (`theta_pow_four`).
4. **Counting**: the coefficient of `qᴺ` in `φ(−q)⁴` is `(−1)ᴺ r₄(N)`, since `a ≡ a² (mod 2)`. On the right,
   `(−1)ᴺ Σ_{d∣N} (−1)^{N/d+d+1} d = Σ_{d∣N, 4∤d} d` (`coeff_Lser_eq`), proved by splitting the divisors of `2M`.
Axioms `[propext, Classical.choice, Quot.sound]`.

### `TwoSquares.lean` — Jacobi's two-square theorem
```lean
theorem jacobi_two_squares {N : ℕ} (hN : 1 ≤ N) :
    (r2 N : ℤ) = 4 * ((N.divisors.filter (· % 4 = 1)).card - (N.divisors.filter (· % 4 = 3)).card : ℤ)
theorem r2_eq_ncard (N : ℕ) : {v : ℤ × ℤ | v.1 ^ 2 + v.2 ^ 2 = (N : ℤ)}.ncard = r2 N
```
The proof uses the same pipeline as the four-square theorem, with the specialization `a = 1, b = i, c = −i, d = −1`
of Jackson's ₈φ₇. This gives `(b)_k(c)_k = (−1;q²)_k`, so `(−q)ₙ²/(q)ₙ² + Σ 4(−1)^k q^k/(1+q^{2k}) ·
(−q)_{n−k}(−q)_{n+k}/((q)_{n−k}(q)_{n+k}) = 1`. Its WZ certificate is
`c(n) = −q^{n+1}/((1−q^{n+1})(1+q^{n+1}))`. The limit is `φ(−q)² = 1 + 4 Σ (−1)^k q^k/(1+q^{2k})`, and its
coefficients give the odd-divisor character sum `d₁ − d₃`. Axioms `[propext, Classical.choice, Quot.sound]`.

`TwoSquaresCor.lean` derives three corollaries:
```lean
theorem r2_prime_one_mod_four {p : ℕ} (hp : p.Prime) (h : p % 4 = 1) : r2 p = 8      -- Fermat, with uniqueness
theorem r2_prime_three_mod_four {p : ℕ} (hp : p.Prime) (h : p % 4 = 3) : r2 p = 0
theorem gauss_two_triangular (n : ℕ) :                                                -- Gauss
    (t2tri n : ℤ) = #((4n+1).divisors with · % 4 = 1) - #((4n+1).divisors with · % 4 = 3)
```
The last uses `r₂(8n+2) = 4 t₂(n)`. Both squares must be odd, `±(2a+1), ±(2b+1)`.

### `RRContinuedFraction.lean` — the Rogers–Ramanujan continued fraction
```lean
-- cf N 0 = 1/(1 + q/(1 + q²/(⋯/(1 + q^N))))
theorem rogers_ramanujan_cf (N : ℕ) :
    X ^ (N + 1) ∣ cf N 0 - Pinf 1 5 * Pinf 4 5 * Ring.inverse (Pinf 2 5 * Pinf 3 5)
```
So `1/(1 + q/(1 + q²/(1 + ⋯))) = (q;q⁵)_∞(q⁴;q⁵)_∞/((q²;q⁵)_∞(q³;q⁵)_∞)` coefficientwise. This is the identity
from Ramanujan's first letter to Hardy, without the `q^{1/5}` prefactor. With `G_m = Σ q^{n²+mn}/(q)_n`, the
functional equation `G_m = G_{m+1} + q^{m+1}G_{m+2}` (`Gs_func`) gives `ρ_m = G_{m+1}/G_m = 1/(1 + q^{m+1}ρ_{m+1})`.
Each level of the fraction gains one power of `q` (`rho_sub_cf`), and `G₀`, `G₁` are the two Rogers–Ramanujan products.

**Ramanujan's `R⁵` identity** (`RamanujanR5.lean`): `1/R(q)⁵ − 11 − R(q)⁵ = (q;q)_∞⁶/(q (q⁵;q⁵)_∞⁶)`, where
`R(q) = q^{1/5}(q;q⁵)(q⁴;q⁵)/((q²;q⁵)(q³;q⁵))`:
```lean
theorem ramanujan_R5 :
    eQ ^ 6 * ((Pinf 2 5 * Pinf 3 5) ^ 10 - 11 * X * (Pinf 1 5 * Pinf 4 5) ^ 5 * (Pinf 2 5 * Pinf 3 5) ^ 5
        - X ^ 2 * (Pinf 1 5 * Pinf 4 5) ^ 10)
      = qfacInf ^ 6 * (Pinf 1 5 * Pinf 4 5) ^ 5 * (Pinf 2 5 * Pinf 3 5) ^ 5
```
It combines the 5-dissection norm identity (`norm_identity`, from the "most beautiful identity" proof) with
Ramanujan's `α = J_{5,2}/J_{5,1}` (`J5_relations`).

### `Legendre.lean` — four triangular numbers: `t₄(n) = σ(2n+1)`
```lean
theorem legendre_four_triangular (n : ℕ) : t4 n = ∑ d ∈ (2 * n + 1).divisors, d
theorem sum_four_triangular (n : ℕ) :
    ∃ a b c d : ℕ, a*(a+1)/2 + b*(b+1)/2 + c*(c+1)/2 + d*(d+1)/2 = n
```
Here `t4 n` counts `(x₁,…,x₄) ∈ ℕ⁴` with `Σ xᵢ(xᵢ+1) = 2n`. The proof is a corollary of Jacobi's four-square
theorem. A solution of `Σ vᵢ² = 8n+4` has all `vᵢ` even or all odd, because squares are `0, 1 (mod 4)`. Halving
the even solutions gives `r₄(2n+1)`. The odd solutions are `vᵢ = ±(2xᵢ+1)`, sixteen for each element of `t4 n`.
So `16 t₄(n) = 8·3σ(2n+1) − 8σ(2n+1)`.

### `AndrewsGordon.lean`, `AndrewsGordonAll.lean`, `Bressoud.lean` — the Andrews–Gordon identities (every `1 ≤ i ≤ k`) and Bressoud's even-modulus companions
```lean
theorem andrews_gordon (j : ℕ) : tsumQsq (agBeta j) * agProd (2 * j + 5) (j + 2) = 1
```
With `k = j + 2`, this is
`Σ_{n₁≥⋯≥n_{k−1}≥0} q^{n₁²+⋯+n_{k−1}²}/((q)_{n₁−n₂}⋯(q)_{n_{k−2}−n_{k−1}}(q)_{n_{k−1}}) = ∏_{n ≢ 0,±k (mod 2k+1)} 1/(1−qⁿ)`.
Here `agBeta` is the iterated chain `β⁽ʲ⁺¹⁾ₙ = Σ_{m≤n} q^{m²}/(q)_{n−m} β⁽ʲ⁾_m`, starting from `1/(q)_n`, and
`agProd a b = ∏_{r ≢ 0, ±b (mod a)} (q^r;q^a)_∞`. `k = 2` is the first Rogers–Ramanujan identity.
The proof is Andrews's Bailey chain: `k − 2` applications of the repo's limiting Bailey lemma to the
Rogers–Ramanujan pair. The Bailey transform then gives `(1/(q)_∞) Σ q^{(k−1)n²}αₙ = J_{2k+1,k}/(q)_∞`. A general
residue split `(q;q)_∞ = ∏_{r=1}^a (q^r;q^a)_∞` (`Pinf_split`) finishes the proof.

The **`i = 1` family** is also proved, by the same route with the `a = q` Bailey chain applied to the
Rogers–Ramanujan-2 pair:
```lean
theorem andrews_gordon_one (j : ℕ) : tsumQsqQ (agBetaQ j) * agProd (2 * j + 5) 1 = 1
```
That is, `Σ q^{n₁²+⋯+n_{k−1}² + n₁+⋯+n_{k−1}}/((q)_{n₁−n₂}⋯(q)_{n_{k−1}}) = ∏_{n ≢ 0,±1 (mod 2k+1)} 1/(1−qⁿ)`,
where `(1−q) Σ q^{(k−1)(n²+n)} αₙ = J_{2k+1,1}`.

**Every intermediate `i`** (`AndrewsGordonAll.lean`), via one step of the **Bailey lattice**:
```lean
-- k = s + t + 2, i = t + 2
theorem andrews_gordon_i (s t : ℕ) : tsumQsq (agBetaI s t) * agProd (2 * s + 2 * t + 5) (t + 2) = 1
```
That is, `Σ q^{n₁²+⋯+n_{k−1}² + n_i+⋯+n_{k−1}}/((q)_{n₁−n₂}⋯(q)_{n_{k−1}}) = ∏_{n ≢ 0,±i (mod 2k+1)} 1/(1−qⁿ)`.

The key step is the switch from `a = q` to `a = 1` (`isBaileyPair_toOne`). An `a = q` pair `(α, β)` is also an
`a = 1` pair `(α°, β)`, with the same `β` and `α°_r = (1−q)(α_r/(1−q^{2r+1}) − q^{2r−1}α_{r−1}/(1−q^{2r−1}))`.
This follows from the partial fraction `1/((q)_{n−r}(q)_{n+r+1}) = [1/((q)_{n−r}(q)_{n+r}) − q^{2r+1}/((q)_{n−r−1}(q)_{n+r+1})]/(1−q^{2r+1})`.

The steps are: `k − i` steps of the `a = q` chain from the RR2 pair (these carry the linear terms), the switch,
`i − 2` steps of the `a = 1` chain, then the Bailey transform. On the `α` side, `q^{(i−1)n²}α°_n` is exactly the
`±n` pair of terms of `Σ_{n∈ℤ}(−1)ⁿq^{(2k+1)n(n−1)/2+in}`, so the Jacobi triple product gives `J_{2k+1,i}`.
At `s = 0` this recovers `andrews_gordon`.

**Bressoud's even-modulus identities** (`Bressoud.lean`, Bressoud 1980). For `1 ≤ i ≤ k−1`,
`Σ q^{n₁²+⋯+n_{k−1}² + n_i+⋯+n_{k−1}}/((q)_{n₁−n₂}⋯(q)_{n_{k−2}−n_{k−1}}(q²;q²)_{n_{k−1}}) = ∏_{n ≢ 0,±i (mod 2k)} 1/(1−qⁿ)`:
```lean
theorem bressoud_one (s : ℕ) : tsumQsqQ (brBetaQ s) * agProd (2 * s + 4) 1 = 1              -- i = 1, k = s + 2
theorem bressoud_i (s t : ℕ) :                                                            -- i = t + 2, k = s + t + 3
    tsumQsq (brBetaI (s + 1) t) * agProd (2 * (s + 1) + 2 * t + 4) (t + 2) = 1
```
The route is the same as for Andrews–Gordon, starting instead from the `a = q` pair
`(αₙ = (−1)ⁿq^{n²}(1+⋯+q^{2n}), 1/(q²;q²)ₙ)` (`isBaileyPairQ_A`). Its theta side is `J_{2k,i}`.

### `GollnitzGordon.lean`, `GollnitzGordon2.lean` (+ WZ files) — the Göllnitz–Gordon identities
```lean
-- Σ q^{n²}(−q;q²)_n/(q²;q²)_n = 1/((q;q⁸)_∞(q⁴;q⁸)_∞(q⁷;q⁸)_∞)
theorem gollnitz_gordon_1 :
    tsumQsq (fun n => Mq n * Ring.inverse (Qf n)) * (Pinf 1 8 * Pinf 4 8 * Pinf 7 8) = 1
```
This needs a new piece of Bailey machinery: **Bailey's lemma with the parameter `ρ = −q` in base `q²`**
(`isBaileyPair2_rho`, `bailey_transform_rho`). The repo previously had only the limiting form. Its inner sum
`Σ_i (−q;q²)_{r+i} q^{2ri+i²}/((q²)_{N−i}(q²)_i(q²)_{2r+i}) = (−q;q²)_{r+N}/((q²)_N(q²)_{2r+N})` (`inner_gg`) is
proved by a WZ certificate found with sympy. Each rational identity is checked once in an abstract field and
transferred with `linear_combination`. The transform then takes the Rogers–Ramanujan pair in base `q²` to
`(−q;q²)_∞ J_{8,3}/(q²;q²)_∞`, which reduces to the product by residue splits mod 8.

```lean
-- Σ q^{n²+2n}(−q;q²)_n/(q²;q²)_n = 1/((q³;q⁸)_∞(q⁴;q⁸)_∞(q⁵;q⁸)_∞)
theorem gollnitz_gordon_2 :
    tsumQsq (fun n => X ^ (2 * n) * (Mq n * Ring.inverse (Qf n))) * (Pinf 3 8 * Pinf 4 8 * Pinf 5 8) = 1
```
The second identity uses the same scheme relative to `a = q²`, with `aq/ρ = −q³`. The inner sum (`inner_gg2`) has
its own WZ certificate `R = q²x(y−1)(q²yz²−1)/((q²x−y)(q³xz+1))`. Applied to the second Rogers–Ramanujan pair in
base `q²`, the factors `(1+q)/(1+q^{2r+1})` and `(1−q^{4r+2})/(1−q²)` combine to `1−q^{2r+1}`, and the theta series
is `J_{8,1}`.

**Combinatorial form** (`GollnitzGordonComb.lean`; Göllnitz 1967, Gordon 1965):
```lean
-- distinct parts differing by ≥ 2, even parts by ≥ 4   ↔   parts ≡ 1, 4, 7 (mod 8)
theorem gollnitz_gordon_comb (m : ℕ) :
    #(gapGG m) = #(Nat.Partition.restricted m fun i => i % 8 = 1 ∨ i % 8 = 4 ∨ i % 8 = 7)
```
The gap side splits on whether `2s+1`, `2s+2`, or neither is a part. An even part `2s+2` excludes `2s+3` and `2s+4`.
This is the recursion of `q^{n²+2sn}(−q;q²)_n/(q²;q²)_n` (`card_AG`). The product side uses a general version of the
restricted-partition lemma for any modulus and residue set (`restricted_mul_eq_one_gen`).
The second identity also has a combinatorial form, `gollnitz_gordon_comb_2`: gap partitions with all parts `≥ 3` are
equinumerous with partitions into parts `≡ 3, 4, 5 (mod 8)`. This is the case `s = 1` of the same recursion.

### `RamanujanMostBeautiful.lean` — Ramanujan's "most beautiful identity", and `25 ∣ p(25n+24)`
```lean
theorem ramanujan_most_beautiful_identity :
    (PowerSeries.mk fun n => (Fintype.card (Nat.Partition (5*n+4)) : ℤ)) * qfacInf ^ 6 = 5 * (E5 qfacInf) ^ 5
theorem twentyfive_dvd_partition_card (m : ℕ) : 25 ∣ Fintype.card (Nat.Partition (25*m+24))
```
Hardy called this identity the best of Ramanujan's. Its proof is Ramanujan's own argument:

1. **Dissect Euler's product mod 5.** From the pentagonal theorem, `(q;q)_∞ = E(q²⁵)(A − q − q²B)` with
   `A, B` series in `q⁵`. The exponent classes `≡ 3, 4 (mod 5)` are empty, and class `≡ 1` is exactly
   `−q E(q²⁵)`.
2. **Show `AB = 1`.** Cubing the dissection and comparing with Jacobi's `(q;q)_∞³`, which has no exponent
   `≡ 2 (mod 5)`, forces it.
3. **Take the norm over the fifth roots of unity.** In `ℂ⟦X⟧`, via `PowerSeries.rescale`,
   `∏_ω E(ωq) = E(q⁵)⁶/E(q²⁵)`, which gives `A⁵ − 11q⁵ − q¹⁰B⁵ = E(q⁵)⁶/E(q²⁵)⁶`.
4. **Invert.** `(A − q − q²B)·𝒬 = A⁵ − 11q⁵ − q¹⁰B⁵`, and the only `q^{≡4}` term of `𝒬` is `5q⁴`.

The mod-25 congruence follows from the identity together with the char-5 Frobenius.

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

### Ramanujan's own claims: `1/π`, `R(e^{−2π})`, the deathbed letter

**`RamanujanPi.lean`: Ramanujan's first series for `1/π`** (*Modular equations and approximations to π*, 1914):
`Σ (6n+1)((1/2)_n)³/(n!³4ⁿ) = 4/π`. The proof uses no modular forms.
* The summand is deformed to `F(k,n) = (6n+4k+1)(1/2)_n³/(n!(1+k)_n²4ⁿ)`.
* A Zeilberger-type certificate `G = 8r_k n/(6n+4k+1)·F`, with `r_k = ((2k+2)/(2k+1))²`, telescopes. This gives `S(k+1) = r_k S(k)`.
* For `n ≥ 1` the terms are `O(4⁻ⁿ/k)`, so `S(k) ~ 4k+1`.
* `∏_{i<k} r_i = (2k+1)W_k`, and Mathlib's Wallis product `W_k → π/2` finishes.
* The same method proves `Σ (−1)ⁿ(6n+1)((1/2)_n)³/(n!³8ⁿ) = 2√2/π`. That limit is `((4k+1)/∏r)² = (4k+1)/((2k+1)W_{2k}W_k) → 8/π²`.

**`RRValue.lean`: `R(e^{−2π}) = √((5+√5)/2) − (√5+1)/2`**, from Ramanujan's first letter to Hardy.
* **Formal identity.** The 5-dissection of Euler's product gives `(x;x)_∞u(x⁵)v(x⁵) = (x²⁵;x²⁵)_∞(v² − xuv − x²u²)`, i.e. `1/R − 1 − R = η(τ/5)/η(5τ)`.
* **Analytic transfer.** `Realize.lean` turns it into an identity of holomorphic functions on the disc. Each product `∏(1 − q^{b+ak})` is a locally uniform limit of integer polynomials, and Taylor's theorem identifies the two sides.
* **Evaluation.** Mathlib's `η(−1/z) = √z·η(z)/√i` at `z = 5i` gives `η(i/5) = √5·η(5i)`. Positivity of the real products picks the root of `R² + (1+√5)R − 1 = 0`.

**`Atkin11*.lean`, `Atkin11Seed/*.lean`: Ramanujan's conjecture for powers of 11.**
* **The theorem.** `Atkin11.ramanujan_pow11_unconditional : ∀ r ≥ 1, 24m ≡ 1 (mod 11ʳ) → 11ʳ ∣ p(m)`. It is `Atkin11.ramanujan_pow11 : Inputs → …` (Step 1) applied to `Atkin11.inputs_proved` (Steps 2 and 3).
* **The objects (`Atkin11Defs`, `Atkin11CDefs`).**
  * `g₂` is Atkin's generator, in theta form `g₂ = GN(c)/GD(c)`. The `c_k` are the level-11 eta ratios `c₀ = η₄/η₂, c₁ = −η₂/η₁, c₂ = −η₅/η₃, c₄ = −qη₁/η₅, c₇ = η₃/η₄` with `η_a = (q^a, q^{11−a}; q¹¹)_∞`.
  * `g₃` is defined by (R1) `g₂g₃ = g₂² − g₃ + 11z`, with `z = q⁵E₁₁¹²/E₁¹²`.
* **`Inputs`.** Three q-series identities:
  * (R2) `g₃² = g₂³ − g₂g₃ − z` (the curve 11a1): **proved**, `Atkin11.r2_proved`;
  * the degree-11 modular equation for `φ`: **proved**, `Atkin11.modeq_proved`;
  * 55 seed relations `U₁₁(φ^λ J_i) = Σ_ν C^λ_{i,ν}J_ν`, `λ ≤ 10` (3031 integers in `Atkin11Data`): **proved**, `Atkin11Seed.seeds_proved`.
* **What is proved from them (Step 1).**
  * The multiplication table, from R1 and R2.
  * Gordon's matrices for all `λ`, via the recurrence (`Atkin11.U_C` in `Atkin11Matrix.lean`).
  * Gordon's 11-adic bound `11^{⌊(11ν−i−5λ+δ)/10⌋} ∣ C^λ_{i,ν}`. The kernel checks a periodic box and the seeds; one entry of the published δ table is corrected (δ(2,3) = 3).
  * The shift `z(q)z(q¹¹) = φ¹²`.
  * The induction `L_r = Σ_{ν≥1} a_ν J_ν` with `11^{r+⌊(ν−1)/2⌋} ∣ a_ν`, and the link to `p(11ʳn + μ_r)`.
* **How the modular equation and R2 are proved (Step 2).** Everything is elementary q-series algebra plus kernel-checked certificates; there are no modular forms.
  1. **Quintuple product** (`ALz.quint_theta` in `ALQuint.lean`): `(Σ(−1)ⁿq^{n(3n−1)/2}z^{3n}(1+zqⁿ))·θ(z) = E(q)·θ(z²)`. It is proved over `ℂ((t))` by splitting `ℤ²` by parity; two classes biject onto the right side and two cancel.
  2. **11-dissection of `E`** (`ALz11.E_dissect`, `Atkin11.E_dissect_PS`): `E(q) = E(q¹²¹)·(c₀ + qc₁ + q²c₂ + q⁴c₄ + q⁵ + q⁷c₇)(q¹¹)`. It comes from the 11 pentagonal branches, quasi-periodicity, and the quintuple product at `z = Q^a`.
  3. **Ten level-11 three-term (Weierstrass) relations** among `θ(Q^a;Q¹¹)` (`Atkin11Weier`). A 25-element Gröbner basis of their ideal is certified (`Atkin11Cert.Common`).
  4. **Certificates.** Every coefficient identity (`E3, E4, M1–M6`), the quintic `g₂⁵ = z(1+13g₂+34g₂²) + 121z²`, and Cayley–Hamilton for `ψ = 1/φ` are certified, with up to 74k cofactor terms. They are checked by a kernel-evaluated sparse-polynomial checker (`SPoly*`): packed monomials, merge-sorted runs, and soundness = preservation of the evaluated sum. Large certificates are split into trees and DAGs of small checks.
  5. **The norm** (`Atkin11.norm_E11`): `e₁₁(ψ)·z = 1`. `φ` is a root of a degree-11 polynomial with `q¹¹`-coefficients, and its 11 conjugates `φ(ζᵏq)` are distinct roots. So the constant term is `∏φ(ζᵏq)`, which `prod_conj_E` evaluates as `z(q¹¹)`.
  6. **Assembly** (`Atkin11ModEq`). The certified identities are pulled back from `ℂ((t))` to `ℤ⟦q⟧` along the injective `ιN`; units are cleared, and the modular equation and R2 follow.
* **How the seeds are proved (Step 3, `Atkin11Seed/`).**
  1. **Exact arithmetic** (`JArith`, `Eval`). Elements of `span{J_ν}` are five dense `ℤ[z]`-lists (one for each of `1, g₂, g₃, g₄, g₆`), and polynomials in `Y` have such coefficients. Products use Atkin's table, which is sound by R1 and R2. Reduction modulo the monic modular equation `P` preserves the value at `Y = φ`. The kernel evaluates everything under `decide +kernel`.
  2. **H2** (`Unique`, `H2`, `H2Check*`). `P'(φ)·g = S(φ)` for `g = g₂, g₃, g₄, g₆`, with explicit `S` (`SData`; 211–692 coefficients of up to 79 digits). Kernel checks give R1 and R2 for `(S₂, S₃)/P'(φ)` modulo `P`, using `z = φ¹²/V(z)`. These imply the homogeneous quintic for `S₂(φ)`, and its root is unique in `ℤ⟦q⟧`: every root is `q⁵¹·(11 + O(q))`, and the cofactor of `y − y'` is `q²⁰⁴(5·11⁴ + O(q))`. So `S₂(φ) = P'(φ)g₂`; then `g₃`, `g₄`, `g₆` follow.
  3. **Lagrange over the conjugates** (`Trace`). Over `ℂ⟦q⟧`, `P = ∏(Y − φ(ζᵏq))` with distinct roots, so `P'(φ(ζᵏq)) = ∏_{j≠k}(…)`. Lagrange interpolation then gives `Σ_k φ(ζᵏq)^λ g(ζᵏq) = [Y¹⁰](Y^λ S(Y) mod P)`, and the left side is `11·(U₁₁(φ^λ g))(q¹¹)`.
  4. **The seed check** (`SeedCheck`). For each of the five `S` and each `λ ≤ 10`, the kernel computes `Y^λ S mod P` and compares `[Y¹⁰]` with `11·C^λ_{i,·}`.
  * Reproduce the data with `scripts/atkin11/seeds/` (`compute_S.py`, `jarith.py`, `gen_data.py`, `gen_h2.py`).
  * The kernel checks take about 4 minutes in total; the largest file (`H2CheckI`) peaks near 10 GB.

**`Rademacher/*.lean`: Rademacher's exact convergent series for `p(n)`** (`Rademacher.rademacher_dedekind`). The proof follows Apostol's Ford-circle route, without contour deformation:
* **η on SL₂(ℤ)** (`EtaGeneral`, `FTransform`): `η(γτ) = ε√(cτ+d)η(τ)` with `ε²⁴ = 1`. It comes from log-derivatives and Mathlib's `E2_slash_action`, plus the modularity of Δ. Specialized, it gives `F(e^{2πi(h+iz)/k}) = ω√z e^{π(1/z−z)/12k} F(e^{2πi(h'+i/z)/k})`. The multiplier `ω_{h,k}` is canonical (`Rademacher.omega` in `Integrand.lean`).
* **Dedekind sums** (`Dedekind`, `DedekindOmega`, `Classical`).
  * `s(h,k) = Σ_r ((r/k))((hr/k))`, and **Dedekind reciprocity** `s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 − 1/4`. The proof is elementary: `r ↦ hr mod k` permutes residues, and lattice points are counted for `Σ⌊hr/k⌋²`.
  * The multiplier obeys the same recursion. Compare the transformation at `h/k` (at `z = 1`), the `S`-transformation at `(h+i)/k`, and the transformation at `−k/h` (at `Z = k/(h+i)`): all three hit the same far point. This gives `ω_{h,k} = ω_{−k,h}e^{−πi/4}e^{πi(h/k+k/h+1/(hk))/12}`.
  * Induction along Euclid, with base case `ω_{0,1} = 1`, then gives **`ω_{h,k} = e^{πi s(h,k)}`** (`omega_eq_dsum`).
* **Laplace and Bessel** (`Laplace`, `Bessel`, `Closed`):
  * `∫₀^∞ x^{β−1}e^{−sx} = Γ(β)s^{−β}` for `Re s > 0`, by the identity theorem;
  * `∫_ℝ (c+it)^{−5/2}e^{(c+it)+y/(c+it)}dt = 2πΣ yᵐ/(m!Γ(m+5/2))`, by Fourier inversion;
  * the closed form of that series is `4(u cosh u − sinh u)/(√π u³)`.
* **Farey/Ford** (`Farey`, `Pieces`). Stern–Brocot recursion gives completeness, no duplicates, and the neighbour chain. The explicit primitive `G` of `F(e^{2πiτ})e^{−2πinτ}` on ℍ turns the sum of Ford-segment integrals (vertical segments `w = k+iu`, `u ∈ [−k₁,k₂]`) into an exact telescoping identity for `p(n)`.
* **Main terms and errors** (`Integrand`, `MainTerm`, `Chord`, `Assembly`).
  * Each segment integrand is `(ω e^{−2πinh/k}/k)·w^{−5/2}e^{aw+b/w}F(q′)`.
  * The main part is the full-line Bessel integral minus tails of size `O(N^{−1/2}/k)`.
  * The error part is moved to the chord by a Morera primitive on a disc in `Re z > 0`, which gives `O(N^{−3/2})`.
  * In total, `|p(n) − Σ_{k≤N}…| ≤ C(1+log N)/√N + C′N^{−1/2}`.

**`LogConcave*.lean`, `Rademacher/LogConcaveTail.lean`: DeSalvo–Pak log-concavity** `p(n)² > p(n−1)p(n+1)` for `n ≥ 26`.
* **Explicit error** (`p_sub_main_le`). Put `U = π√((2/3)(n−1/24))` and `K = (π/12)^{3/2}·2π·4/√π`. Then
  `|p(n) − Ke^U(U−1)/(2U³)| ≤ Ke^{U/2}`. This is not taken from the error terms of the proof of Rademacher's
  formula. It comes from the limit itself:
  * `|A_k(n)| ≤ k`, since `|ω_{h,k}| = 1`;
  * `(u cosh u − sinh u)/u³ ≤ cosh(u)/3`, by monotonicity;
  * `Σ_{k≥2} k^{−3/2} ≤ 2`, by telescoping against `2(1/√(k−1) − 1/√k)`.
* **Main-term inequality** (`main_ineq`, for `U ≥ 60`, i.e. `n ≥ 549`). Write `P = u₊u₋` and `S = u₊ + u₋`, where
  `u_±² = U² ± 2π²/3`. The concavity saving `e^{−(2U−S)}`, with `2U − S ≥ γ²/(4U³)`, beats the loss from
  `P < U²` by `γ²/(64U⁷)`. The `e^{−u/2}` terms are bounded by `x²⁰/20! ≤ eˣ`.
* **Finite range** (`logConcave_table`, `26 ≤ n ≤ 548`). Kernel check, about 25 s, on a table of `p(n)` built
  by Euler's pentagonal recurrence. The table is proved equal to `#(Nat.Partition n)`.

**`HardyRamanujan/*.lean`: the Hardy–Ramanujan asymptotic formula** `p(n) ~ e^{π√(2n/3)}/(4n√3)`.
* **Generating function** (`GenFun`): `F(q) = 1/(q;q)_∞ = Σ p(n)qⁿ` on the unit disc. The proof uses Taylor's theorem plus Leibniz on `(q;q)_∞·F = 1`, against the formal recurrence.
* **Modularity** (`Modular`): `F(e^{−z}) = √(z/2π)·e^{π²/(6z) − z/24}·F(e^{−4π²/z})` for `Re z > 0`, from Mathlib's `η(−1/τ) = √(τ/i)η(τ)`.
* **Coefficient integral** (`Coeff`): `2πp(n) = ∫_{−π}^{π} F(e^{−(t+iθ)})e^{n(t+iθ)} dθ`, by termwise integration.
* **Minor arc** (`Minor`): `‖F(e^{−t−iθ})‖ ≤ ‖F(e^{−t})‖e^{−1/(200t)}` for `t ≤ |θ| ≤ π`. Per factor, `‖1 − xe^{iφ}‖ ≥ (1−x)e^{x(1−cos φ)/8}`; summed, `Σrᵏ(1 − cos kθ) = r/(1−r) − Re(q/(1−q))`.
* **Major arc** (`Major`, `Param`). Take `t = π/√(6n)`, `A = nt`, `θ = tv/√A`. The exponent is exactly `2A − v²/(1 + iv/√A)`, and dominated convergence gives the integral `→ √π`.
* **Assembly** (`Bounds`, `Main`). The normalizing factor times the main term is exactly `J_n/√π`; both error terms are `O(n e^{−c√n})`.

**[Partition entropy](../RamanujanTau/HardyRamanujan/Entropy.lean) and
[Cardy saddle algebra](../RamanujanTau/CardySaddle.lean).**
For the actual partition count, `HardyRamanujan.entropy_log_correction` proves
`log p(n) − π√(2n/3) + log n → −log(4√3)` as natural `n → ∞`.
`entropy_sqrt_limit` gives `log p(n)/√n → π√(2/3)`. These are standard
corollaries of the preceding asymptotic, with no additional hypotheses.
For real `C,E≥0` and `β>0`, `Cardy.saddle_sub_leading` identifies the difference
between `2π²C/β + βE` and `2π√(2CE)` as a square. At `C=1/12`, `E=n≥1`,
`HardyRamanujan.partition_saddle_minimum` proves the minimum is attained at
`β=π/√(6n)`, and `partition_cardy_leading` identifies its value with `π√(2n/3)`.
`entropy_cardy_log_correction` combines the normalization with the coefficient
asymptotic. The algebra is ported from the separate unifiedtheory repository;
the partition-count asymptotic is proved here. This does not construct DMZ
mock Jacobi coefficients or derive a black-hole area law. See the
[research record](CYLINDRIC_RESEARCH.md#what-unifiedtheory-contributes-to-black-hole-work).

**[Colored partitions](../RamanujanTau/ColoredPartitions.lean) and
[their leading entropy](../RamanujanTau/ColoredPartitionEntropy.lean).**
`ColoredPartitions.Partition k n` is the finite type of an ordered tuple of
ordinary partitions whose sizes sum to `n`; `count k n` is its cardinality.
For every natural `k,n`, `coeff_series` identifies this count with the `n`th
coefficient of `partitionGF^k`. `qExpansion_discriminant_mul_series` proves
`qExpansion(Δ) * map(series 24) = X` for the actual analytic modular
discriminant, identifying the regular series as `q/Δ`.

For any fixed `k>0`, `entropy_sqrt_limit` proves
`log(count k n)/√n → π√(2/3)√k`. The proof combines the lower bound
`p(floor(n/k))^k ≤ count k n` with an exponential upper bound on the finite
convolution; Cauchy–Schwarz controls the sum of the square roots of its indices.
The one-unit shift in `degeneracy n = count 24 (n+1)` is included in
`degeneracy_entropy`, which proves `log(degeneracy n)/√n → 4π`.
`degeneracy_cardy_ratio` proves that this logarithm divided by
`Cardy.leadingEntropy 2 n` tends to 1. There are no unproved asymptotic
hypotheses. These are leading limits, without a colored logarithmic correction
or a quantitative remainder. Physical state identification, the area law, and
the quarter-BPS mock Jacobi extension are not formalized by these theorems.
Use the standalone import `RamanujanTau.ColoredPartitionEntropy`.

**[Bosonic occupation model](../RamanujanTau/BosonicOccupation.lean).**
`Occupation k` consists of `k` finitely supported arrays of nonnegative
integer occupations, with mode zero excluded. Energy is `sum_i sum_m m*N(i,m)`.
`stateEquivPartition k N` gives an explicit bijection between energy-`N`
occupation states and colored partitions. `state_zero_above_energy` derives
the cutoff `N(i,m)=0` for `m>N`, and `state_occupation_bound` proves
`N(i,m)≤N/m` for positive modes. The vacuum is the unique zero-energy state.

`ShellSpace k N` is the finite complex Hilbert space on this basis;
`shell_finrank` gives dimension `p_k(N)`. Its formal graded dimension series
is the colored partition series, and `discriminant_mul_shellSeries` proves
that the analytic discriminant's q-expansion times the 24-species series is `X`.
For the specified charge `energy−1`, `ChargeSpace n` has dimension
`p_24(n+1)` (`charge_finrank`), with `log(dim)/√n → 4π` (`charge_entropy`)
and ratio to the Cardy leading term at `C=2` tending to 1 (`charge_cardy_ratio`).
The vacuum offset is an input. A full oscillator representation, an infinite
operator trace, string duality, and a gravitational area law are not proved.
Use the standalone import `RamanujanTau.BosonicOccupation`; see its
[verification record](verification/bosonic_occupation.json).

**[Algebraic oscillators](../RamanujanTau/BosonicOscillator.lean) and
[their energy eigenspaces](../RamanujanTau/BosonicSpectrum.lean).**
`Space k` is the complex polynomial ring with variables indexed by species
and positive mode. `occupationEquiv` identifies all monomial exponents with
the preceding occupation arrays, and `energy_toOccupation` identifies their
weighted degrees with the preceding energy function. Multiplication by a
variable defines `create`; its partial derivative defines `annihilate`.
The three canonical commutation relations hold on every polynomial state.
`hamiltonian_occupation` makes every occupation monomial an eigenvector with
the correct energy; the Hamiltonian commutators give the mode energy shifts.

`EnergySpace k N` is the Hamiltonian's actual eigenvalue-`N` subspace.
`mem_energySpace` characterizes it by its monomial support, and
`energySpaceEquivShell` gives a linear equivalence to the earlier finite
Hilbert shell. Thus `energySpace_finrank` proves dimension `p_k(N)`.
With the explicitly specified `chargeOperator=H−I`, the nonnegative charge
eigenspace has dimension `p_24(n+1)` (`chargeEigenspace_finrank`), whose
log-dimension divided by `√n` tends to `4π` (`chargeEigenspace_entropy`).
Its ratio to the Cardy leading term at `C=2` tends to 1.

This is an algebraic representation in an unnormalized monomial basis.
The equivalence is linear; no isometry, creation/annihilation adjoint relation,
Hilbert completion, or unbounded self-adjoint operator is asserted. The
vacuum shift, physical state identification, and gravitational interpretation
retain their earlier boundaries. Use `import RamanujanTau.BosonicSpectrum`;
see the [verification record](verification/bosonic_spectrum.json).

**[Factorial normalization](../RamanujanTau/BosonicNormalization.lean) and
[finite-shell adjoints](../RamanujanTau/BosonicAdjoint.lean).**
`factorialWeight d` is the product of occupation factorials; it is strictly
positive and multiplies by `d(a)+1` when one particle is added at mode `a`.
`normalizedBasis` rescales each polynomial monomial by the inverse square
root of this weight. `create_normalizedBasis` and
`annihilate_normalizedBasis_raise` prove the square-root occupation amplitudes;
`annihilate_normalizedBasis_zero` handles an unoccupied mode.
`normalized_coordinate_adjoint` proves conjugate-transpose coordinates for
the existing creation and annihilation operators on the entire algebraic basis.

`normalizedShellEquiv` identifies each polynomial energy eigenspace with
finite Euclidean coordinates in these normalized monomials. Its inverse sends
the orthonormal coordinate basis to those monomials
(`normalizedShellEquiv_symm_basis`). `normalizedShellIsometry` identifies the
coordinate space isometrically with the earlier occupation shell.
`createShell a n` and `annihilateShell a n` are transported restrictions of the
original operators between energies `n` and `n+frequency(a)`.
`annihilateShell_eq_adjoint` proves their actual Hilbert adjoint equality, and
`shell_inner_adjoint` states the inner-product identity for all shell vectors.
`normalizedShell_finrank` preserves the exact colored partition dimensions.

This completes the finite-shell adjoint step. It does not prove the domains
or adjoints of unbounded operators on an infinite Hilbert completion, nor
derive the vacuum offset or a physical black-hole interpretation. Use
`import RamanujanTau.BosonicAdjoint`; see the
[verification record](verification/bosonic_adjoint.json).

**`MockTheta3*.lean`: the third-order mock theta function and the deathbed letter.**
* **`MockTheta3`.** `f(q) = Σ q^{n²}/(−q;q)ₙ²` is the rank generating function at `z = −1`. So `[qⁿ]f = N(0,2,n) − N(1,2,n)`.
* **`MockTheta3Watson`.** Watson's identities `2φ(−q) − f(q) = b(q)` and `f(q) + 4ψ(−q) = b(q)`, with `b(q) = (q;q²)_∞ Σ_ℤ(−1)ⁿq^{n²}`.
  * The route is an elementary chain at `α = qʲ` of Andrews' one-parameter generalization (1966): `F_j = Σ q^{jn+n²−n}/((−q;q)ₙ(−qʲ;q)ₙ)` and `A_j = Σ (−1)ⁿq^{n²}/(−q^{j+1};q²)ₙ`.
  * Two telescoping identities give `M_{j+2} = (1+qʲ)(1+q^{j+1})M_j` for `M_j = 2A_j − F_j`. Also `M_j ≡ Θ (mod qʲ)`.
  * The contraction `(−qʲ;q)_∞ M_j = Θ` and Euler's `(−q;q)_∞(q;q²)_∞ = 1` finish. No Appell–Lerch sums or theta certificates are needed.
* **`MockTheta3Radial`.** Ramanujan's claim that `f(q) − (−1)ᵏb(q)` stays bounded as `q` tends to an even-order root of unity, at `q → −1`. In fact the limit exists: **`f(q) + b(q) → 4`**, even though `f` and `b` each blow up.
  * `Taylor.lean`: the Taylor-series map `T` is a ring map that commutes with locally uniform limits. It lifts Watson's identity to the disc.
  * `MockTheta3Analytic.lean`: holomorphic realizations of series `Σ ±q^{n²}/Pₙ(q)ᵏ`.
  * Then `φ(t) = Σ t^{n²}/(−t²;t²)ₙ`, with terms `≤ 2⁻ⁿ`, tends to `2` by Tannery's theorem.

### Bounds for τ

* **Hecke's bound** `RamanujanTau.tau_isBigO : τ(n) = O(n⁶)` (`TauLSeries.lean`; real-valued form `tau_isBigO_real` in `TauHeckeBound.lean`), from Mathlib's
  `CuspFormClass.qExpansion_isBigO` through the Δ bridge.
* **Small cases, kernel-checked** (`TauSmallChecks.lean`, `decide +kernel`): Ramanujan's conjecture
  `τ(p)² ≤ 4p¹¹` for all primes `p < 50` (`ramanujan_bound_lt50`) and Lehmer's `τ(n) ≠ 0` for `n < 30`
  (`lehmer_lt30`). Deligne's theorem itself (étale cohomology of Kuga–Sato varieties) is out of reach of current Mathlib.
* **Sub-Hecke bounds (2026-11-03/04), unconditional:** `TauBound.tau_isBigO_47_8_unconditional` (Kloosterman, 47/8),
  `Stepanov.tau_isBigO_35_6_unconditional` (Salié, 35/6), and the current best,
  `StepanovAS.tau_isBigO_23_4_unconditional` (Weil, `τ(n) = O(n^{23/4+ε})`). Lehmer's non-vanishing is now proved
  for `n < 214,928,639,999 (Lehmer 1947)` (`LehmerSmall.lehmer_below_214928639999`).

### `MTC/` — the Mock Theta Conjectures (Hickerson–Mortenson route)
```lean
theorem MTC.mock_theta_conjecture_f0 :
    f0 = Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 1 5 * Pinf 4 5) - 2 * (Ea 2 _ (Phi 1) - 1)
--  f₀(q) = (q⁵;q¹⁰)²(q¹⁰;q¹⁰)/((q;q⁵)(q⁴;q⁵)) − 2Φ(q²)   in ℤ⟦q⟧
theorem MTC.mock_theta_conjecture_f1 :
    X * f1 = X * (Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 2 5 * Pinf 3 5)) - 2 * (Ea 2 _ (Phi 2) - 1)
--  q f₁(q) = q θ₄(0,q⁵)/((q²;q⁵)(q³;q⁵)) − 2Ψ(q²)
```
Method write-up: [`MOCK_THETA_METHOD.md`](../MOCK_THETA_METHOD.md). The chain, following Hickerson–Mortenson (Proc. LMS 2014), lives in `RamanujanTau/MTC/` (≈40 files, see
`MTC_GAP_MAP.md` §6 for the full map):
* **Andrews' Hecke form** (`MockTheta5F0Pair`): a new Bailey pair relative to `a = 1` with a creative-telescoping
  certificate linear in the partial theta polynomial.
* **Hecke → Appell–Lerch** (`Ent`, `Conv`, `ThSpace`, `ThFactor`, `F373`…`Zeros373`): entire bilateral series over
  `ℂ((t))`, theta spaces `Th(m)` and a zero-counting theorem; `f_{3,7,3}` is evaluated at the specialization point by
  showing an auxiliary series in `Th(55)` vanishes at 56 explicit points (residue identities proved symbolically).
* **The rank side** (`RankALm`, `L5`): `(1+φ(q))(q⁵;q⁵)_∞` as three Appell–Lerch sums.
* **Appell–Lerch calculus** (`LamAb`, `LamInv`, `Endgame1`): Lambert form = library form, HM (2.2a–c), four changes
  of `z`; the unknown Appell–Lerch values cancel (`MTC.endgame_reduce` in `Endgame2.lean`).
* **Theta identities**: Weierstrass instances (`F1Prime`, `P11`), a product-identity engine splitting every theta
  into atoms `(q^r;q^M)_∞` (`ProdId`, `LemC`), and HM (1.9) by a zero count in `Th(Q³⁰,10)` (`ThExtra`, `H19`,
  `H19b`), which gives HM (8.17).

**The second conjecture (MTC₁)** runs the same chain at the MTC₁ point `x₁ = i t^{189}`: Andrews' Hecke form from
a new `a = q` Bailey pair (`MockTheta5F1Pair`), HM Theorem 0.3 at `x₁` (`Zeros1`), `Hecke1`, `GX1`, `ThetaX1`/`ThetaY1`,
`ψ` as Appell–Lerch sums (`L5b`), changes of `z` to `z₀ = Q²` and two Weierstrass instances (`ThetaLem1`,
`Endgame1b`), and the theta identity (8.17)₁, which is HM (1.9) at `x = Q⁶` — so the zero count `F19_zero` serves
both conjectures (`Final1`).

**HM Theorem 0.3 for `f_{1,4,1}`** (`F141`, `G141`, `T141`, `Core141`, `FCore141`, `Ev141`, `Z16`, `Zeros141`;
theorem `MTC.H141.hm03_psi`): the `n = 1, p = 3` case of the same machinery, at `y = i t¹²`, `q = t⁸` (auxiliary series
in `Th(16)`, 17 zeros). This is the Hecke → Appell–Lerch step for `ψ₀`.

**χ₀ (toward `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀`), Hecke side done.** A new `a = q` Bailey pair (`Chi0Pair`, WZ)
and Garvan's conjugate pair (`Chi0Conj`) give `(q)_∞χ₀` as a double sum (`Chi0Bailey`).
That double sum is rearranged into Garvan's four `f_{12,9,3}` values by eight cone-shift moves plus the
pentagonal theorem (`MTC/Chi0Cone`, `Chi0Theta`, `Chi0D`).
A parity split then turns those values into `f_{2,3,2}` evaluations at the seven points where HM Theorem 0.3 is proved
(`MTC/F232 … Zeros232, HM232Real, Chi0Bridge`; theorem `MTC.Chi0L.chi0_hecke_HM`).
The Appell–Lerch endgame is also done (`MTC/Chi0AL`, `Chi0Split`, `Chi0Phi`): every mock part cancels.
`MTC/Chi0Final` proves `χ₀ − 2 = 3(Φ−1) − (q⁵;q⁵)²J_{5,2}/J_{5,1}²` and `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀`
from one explicit theta-function identity `ThetaId`.

**χ₀, unconditionally (Watson's route, `RamanujanTau/Watson/`).** The χ₀ identity is now proved outright.
`ThetaId` is a theorem (`MTC.Chi0L.thetaId`), and so is the combinatorial statement (`MTC.Chi0L.rank_chi0`).
All of this is axiom-clean. The proof follows G. N. Watson, *The mock theta functions (2)* (Proc. LMS 1937),
transcribed in `docs/watson1937_R1_proof.md`.
* **Toolkit**: locally finite sums of power series with Fubini, reindexing and parity splitting (`OSum`);
  q-Pochhammer products (`Prod`); Euler's two expansions proved from their q-difference equations (`Euler`);
  the finite q-binomial theorem and the even part of Euler's expansion (`Binom`).
* **Ramanujan's relation (B₀) = R1** `χ₀ = 2F₀ − φ₀(−q)`, proved as Watson did: the two series forms of χ₀
  (`A0`), then Heine's method with a parity split (`R1`).
* **Watson's (2₀), (3₀)** `f₀ ± ϑ₄G` (`F0Rel`).
* **The closing theta identity** `4qψ(q²)H(q⁴) + ϑ₄G − 3ϑ₄(q⁵)G + 2(q¹⁰;q¹⁰)²J_{10,4}/J_{10,2}² = 0`
  (`Star`). Its certificate is five instances of HM (1.4b) `θ_mul`, found numerically and checked by
  `field_simp; ring` over atoms `(q^r;q^{80})_∞`. The Lean file is generated by a script.
* **Assembly** (`Final`): R1 at `q²`, plus (2₀), (3₀), MTC₀ and the theta identity, give the χ₀ identity.

### Multi-quintuple products: complete admissible triple classification

[`MultiQuintupleFullConverse.lean`](../RamanujanTau/MultiQuintupleFullConverse.lean)
proves the classification for the actual infinite product
`Q(qⁱ,qᵖ) Q(qʲ,qᵖ) Q(qᵏ,qᵖ)`.
The hypotheses are exactly `AdmissibleSparseTriple p i j k` and `R < p`:
p is prime, p≠3, 0<i<j<k, 2k<p, and p divides i²+j²+k².

```lean
import RamanujanTau.MultiQuintupleFullConverse

open Ramanujan.MultiQuintuple

example {p i j k R : ℕ}
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p) :
    HasProjectiveRootTarget p i j k R ↔ PersistentTripleVanishing p i j k R :=
  admissible_root_vanishing_equivalence ha hR
```

`PersistentTripleVanishing` means every coefficient at degree pN+R is zero,
for all natural N. `HasProjectiveRootTarget` is the existence of an integer
certificate with v=(i,j,k), e∈{1,2}, w≡λv modulo p, w·w=ep, v·w=pu,
and ce=2, together with the target condition

```text
2λR ≡ sum(w) − 6u                         (mod p), if ep ≡ 1 (mod 3),
cλ(2λR − sum(w) + 6u) ≡ 12                (mod p), if ep ≡ 2 (mod 3).
```

The norm condition forces w to be a short nonzero vector. A short vector alone
is insufficient: its target condition must select R. The formal certificate
is defined in
[`MultiQuintupleRootVanishingClassification.lean`](../RamanujanTau/MultiQuintupleRootVanishingClassification.lean).

| Public theorem | Result |
|---|---|
| `admissible_root_vanishing_converse` | Persistent vanishing supplies a projective root certificate |
| `admissible_root_vanishing_equivalence` | The complete equivalence for every admissible triple and canonical residue |
| `admissibleRootVanishingRigidity_proved` | Discharges the original corrected rigidity proposition |

#### How the proof is assembled

| Stage | Checked result and entry point |
|---|---|
| Actual coefficients | [Bilateral bridge](../RamanujanTau/MultiQuintupleBilateralBridge.lean) and [primal Gaussian](../RamanujanTau/MultiQuintuplePrimalGaussian.lean) identify the product coefficients with the signed lattice sum |
| Poisson transform | [Watson Poisson](../RamanujanTau/MultiQuintupleWatsonPoisson.lean) retains all eight branch signs; [Fourier amplitudes](../RamanujanTau/MultiQuintupleWatsonFourierAmplitude.lean) identify the transformed terms exactly |
| Norm shells | [Gaussian cancellation](../RamanujanTau/MultiQuintupleDualGaussianCancellation.lean) proves absolute convergence and separates each complete norm shell |
| Phase partners | [Canonical phases](../RamanujanTau/MultiQuintupleCanonicalPhaseCharacter.lean) and [dual shell partners](../RamanujanTau/MultiQuintupleDualShellPartners.lean) derive opposite partners using the actual Watson phases |
| Integral generation | [Universal short generation](../RamanujanTau/MultiQuintupleUniversalShortGeneration.lean) proves that supported vectors of squared norm < p²/2 generate the projective dual lattice over ℤ, for p≠13 |
| Large and finite ranges | [Reduced-basis geometry](../RamanujanTau/MultiQuintupleLargePrimeGeneration.lean) handles p≥1250; [finite generators](../RamanujanTau/MultiQuintupleFiniteGenerators.lean) check complete normalized-line coverage below 1250 |
| Exceptional modulus | [Converse at thirteen](../RamanujanTau/MultiQuintupleConverseThirteen.lean) settles all admissible triples and residues at p=13 |
| Root extraction | [Short dual converse](../RamanujanTau/MultiQuintupleShortDualConverse.lean) constructs one orthogonal involution, preserves the integral lattice and phases, and extracts the exact target |

The finite tables cover 201 primes from 7 through 1249 and check 14,369
short-generator certificates. Modulus 13 is excluded from the generation
conclusion and handled by six root certificates and 20 nonzero product
coefficients. The small mod-three box is checked for all 468 nonsingular
ternary Gram forms. The cutoff 1250 is a sufficient bound; no minimality
claim is made. Python supplies reproducible data; Lean checks the arithmetic
and proves that the certificates concern the required lattices and products.

The published snapshot passed **9,336 build jobs** and the expanded
**251-declaration multi-quintuple axiom audit**, with dependencies confined to
`propext`, `Classical.choice`, and `Quot.sound`.
The [verification record](verification/full_converse_lean.json) distinguishes
that snapshot from the larger development worktree; the
[raw axiom report](verification/full_converse_lean.axioms.txt) lists all audited
results. See the [certificate guide](FINITE_ARITHMETIC.md#multi-quintuple-classification-certificates)
for build, audit, regeneration, and independent-check commands.

#### Related results and exact scope

* [Canonical family](../RamanujanTau/MultiQuintupleCanonical.lean): for every
  odd p≥5, the full canonical quintuple product factors into a theta series
  and a tail supported on multiples of p, giving all nonsquare-class
  vanishings. At p=7 this includes residues 3, 5, and 6.
* [Infinite sparse family](../RamanujanTau/MultiQuintupleEisensteinFamily.lean):
  for p=9t²+15t+7, the indices (1,3t+2,3t+3) vanish at pN+3t+3 for every
  natural t,N. This separate sufficient theorem also permits composite p.
* [Projective cancellation](../RamanujanTau/MultiQuintupleProjectiveCancellation.lean)
  includes the actual 71N+61 and 79N+9 families. The general equivalence
  identifies which admissible residues have such a certificate.
* The unrestricted converse is false: the proved p=9 common-scale example
  vanishes off support without a projective root. [Local support](../RamanujanTau/MultiQuintupleLocalSupport.lean)
  also gives mixed composite-modulus vanishings. Repeated indices, arbitrary
  composite moduli, and four-factor products are outside the classification's
  stated hypotheses.
* Isotropy alone is insufficient. The research scan finds nonzero witnesses
  in every residue for (71;1,4,14); the theorem requires the full root target.

The [research record](../RESEARCH_MULTI_QUINTUPLE.md) preserves the experiments,
failed fixed-shell conjectures, and earlier conditional reductions. The analytic
bridge and admissible converse are complete. The proposed N≤⌊p/4⌋ first-witness
bound, first-spanning and first-perfect cutoff criteria, and the separate
arbitrary-automorphism paper argument remain distinct follow-up questions.
Historical JSON records retain the proof status at the time of their creation.

### Four-factor classification at 41 and a delayed triple witness

[`MultiQuintupleFourFortyOneConverse.lean`](../RamanujanTau/MultiQuintupleFourFortyOneConverse.lean)
proves that, for every R<41, all coefficients of
`Q(q,q⁴¹) Q(q⁴,q⁴¹) Q(q⁵,q⁴¹) Q(q⁹,q⁴¹)` at 41N+R vanish
if and only if R is 21, 25, 26, or 30.
`four41_residue_or_witness` supplies a nonzero coefficient with N≤5 in
all 37 other residues; `four41_finite_test_iff` therefore turns the first
six terms into an exact test for this fixed product.

The proof uses the general actual-product coefficient bridge in
[FourCancellation](../RamanujanTau/MultiQuintupleFourCancellation.lean),
explicit sign-reversing affine involutions in
[FourFortyOne](../RamanujanTau/MultiQuintupleFourFortyOne.lean), and
kernel-checked finite witnesses. This settles the four-factor example
presented as experimental in [Daniels–Huber–McLaughlin–Ye, §5](https://arxiv.org/html/2606.06701v1#S5).
It does not classify all four-factor products or establish priority over
subsequent work.

[`MultiQuintupleWitness103.lean`](../RamanujanTau/MultiQuintupleWitness103.lean)
proves `first_witness103`: for `Q(q,q¹⁰³) Q(q²²,q¹⁰³) Q(q³⁷,q¹⁰³)`, the
coefficients at 103N+63 are zero for N<23 and equal −1 at N=23. This gives
an exact benchmark for the proposed quarter-prime bound, which remains open.

### A second quadratic four-factor family

[MultiQuintupleFourBinary](../RamanujanTau/MultiQuintupleFourBinary.lean)
proves permanent coefficient zeros for indices `(2m,4m,n,3n)` at p=2m²+n²,
with positive m,n, 8m<p, 6n<p, 3 dividing m, 5 dividing n, and gcd(30m,p)=1.
The two residue conditions are R≡3m+2n−30 and R≡3m+2n modulo p.
The proof constructs two exponent-preserving, sign-reversing involutions on
the actual Watson coefficient sums; it requires no primality assumption.

[MultiQuintupleFourBinaryFamily](../RamanujanTau/MultiQuintupleFourBinaryFamily.lean)
proves the unconditional specialization `m=15t+3, n=5` for every natural t:
modulus `450t²+180t+43`, indices `(30t+6,60t+12,5,15)`, and zero residues
`45t+19` and `45t−11` (replace the latter by 32 at t=0).
Lean proves that the moduli strictly increase and that the residues are
distinct and canonical. Every even t gives a modulus that is not a sum of
two integer squares. Thus an unbounded set of these examples lies outside
the earlier sum-of-two-squares moduli. At 43 the guaranteed zeros are 19 and 32.

The [verification record](verification/four_binary.json) records the full
build, 20-declaration axiom audit, and independent comparison of 259,467
coefficients. A universal four-factor coefficient converse remains open.

### Kernel-checked obstructions to four-factor witness bounds

[FourWitness17](../RamanujanTau/MultiQuintupleFourWitness17.lean) proves that
the coefficients at 17N+5 for indices `(2,3,5,8)` are zero for N<7 and equal
1 at N=7. [FourWitnessBound](../RamanujanTau/MultiQuintupleFourWitnessBound.lean)
then proves `fourWitnessLinearBound_ge`: any real constant c giving a bound
N≤cp for all nonvanishing progressions of admissible prime-modulus four-tuples
must satisfy **c≥7/17**. Both c=1/4 and c=2/5 are ruled out. Sufficiency and
asymptotic optimality are not asserted.

[FourWitness2521](../RamanujanTau/MultiQuintupleFourWitness2521.lean) proves
that residue 2273 for `(2521;1,35,36,71)` first becomes nonzero at N=632,
with coefficient 1. This lies in the expanded reflection family and exceeds
even the rounded-up quarter cutoff 631. The proof certifies completeness of
a finite list and checks cancellation of 5,091 terms in 82 kernel-checked
slices. The [verification record](verification/four_witnesses.json) records
the build, audit, and independent arithmetic replay.

The original triple-product conjecture remains open and is unaffected.
The [earlier calculation](verification/four_quarter_counterexample.json)
additionally gives first witness N=631 for residue 67 at 2521; that residue
has not been separately formalized.

### Four congruence families and a converse for the reflection maps

[MultiQuintupleFourReflection](../RamanujanTau/MultiQuintupleFourReflection.lean)
proves infinite coefficient vanishing at `p=m²+n²` when **any one** of
`m,n,m−n,m+n` is divisible by nine, with explicit size and coprimality
conditions. The four residue criteria and complete hypotheses are in the
[research statement](../RESEARCH_MULTI_QUINTUPLE.md#four-congruence-families-and-an-exact-reflection-criterion).
The theorem includes the four zero progressions **9,13,55,64 at 97**, as well
as composite moduli. The coefficient converse at 97 is not yet formalized.

[MultiQuintupleFourReflectionCriterion](../RamanujanTau/MultiQuintupleFourReflectionCriterion.lean)
proves an exact converse for branch compatibility of the sixteen specified
reflection maps. A compatible map exists exactly in the four congruence
cases above, provided the norm is a unit modulo nine. This classifies these
maps; it does not prove that all coefficient vanishing arises from them.

The [verification record](verification/four_reflection.json) contains the full
build and axiom audit. The [independent finite check](verification/four_reflection_check.json)
compares 152,284 coefficients across 37 parameter pairs and records a separate
finite search for converse witnesses. Its finite quarter-bound observations
do not extend to all parameters: the counterexample at 2521 above lies in
this congruence family.

### Two-parameter four-factor theorem and classification at 53

[MultiQuintupleFourPlane](../RamanujanTau/MultiQuintupleFourPlane.lean)
proves infinite coefficient vanishing for factors indexed by `(m−n,n,m,m+n)`
at modulus `p=m²+n²`, subject to explicit size and coprimality conditions and
`9 | m+n`. Four linear congruences specify the zero progressions. The theorem
also covers composite moduli, including 65 and 365. See the
[precise hypotheses and residue formulas](../RESEARCH_MULTI_QUINTUPLE.md#two-parameter-plane-theorem).

[MultiQuintupleFourFiftyThreeConverse](../RamanujanTau/MultiQuintupleFourFiftyThreeConverse.lean)
proves the complete classification for the product `(53;5,2,7,9)`:
its persistent zero residues are exactly **29,31,36,38**. Every other residue
has a nonzero witness with N≤8, so testing the first nine terms is exact for
this product. The general four-factor converse remains open.

The [verification record](verification/four_plane.json) includes the full
build and dedicated axiom audit. An [independent calculation](verification/four_plane_check.json)
also compares 45,926 exact coefficients across 11 parameter pairs.

### An infinite four-factor family

[FourFamily](../RamanujanTau/MultiQuintupleFourFamily.lean) proves
`coeff_four_family_zero` for every pair t,N of natural numbers. Set

```text
p = 5184t²+720t+41,
F_t(q) = Q(q^(72t+1),q^p) Q(q^(72t+5),q^p) Q(q^(72t+9),q^p) Q(q^4,q^p).
```

The coefficient at pN+R is zero for each of

```text
R = 2592t²+468t+21, 3240t²+477t+25,
    1944t²+459t+26, 2592t²+468t+30.
```

Lean also proves that the moduli increase strictly and that the four residues
are distinct and less than p. No primality assumption is made. The case t=0
recovers the four zeros at 41; t=1 has composite modulus 5945. This theorem
guarantees those four progressions and does not exclude additional ones for
t>0. The proof checks polynomial affine involutions on all sixteen Watson
branches, uniformly in t. See the [research derivation](../RESEARCH_MULTI_QUINTUPLE.md#an-infinite-four-factor-family)
and [verification record](verification/four_family.json).

### Checked finite seed models and the numerical 607 minor

[SeedSurvival](../RamanujanTau/FiniteArithmetic/SeedSurvival.lean) proves the
cubic idempotent correction in arbitrary rings and survival from a checked
left inverse. [SeedModels](../RamanujanTau/FiniteArithmetic/SeedModels.lean)
applies the latter to the saved matrices and seeds at primes 233, 257, 307,
401, and 607, for every iteration count. The arithmetic identification with
the partition operator is not a premise proved by those finite checks.

[Rank607Witness](../RamanujanTau/FiniteArithmetic/Rank607Witness.lean) checks
an elimination matrix times the saved minor equals an upper triangular matrix.
The last diagonal entry is 607·308; the other 24 entries are one. Thus the
saved minor's determinant is nonzero modulo 607². `actual_rank_of_entries`
proves `rEll 607 m = 25` for every m≥2 under the hypothesis that its entries
agree with the actual partition-series matrix. See the
[verification record](verification/four_directions.json).

[Rank607Final](../RamanujanTau/FiniteArithmetic/Rank607Final.lean) discharges that
hypothesis, so `rEll_607` is unconditional: **`rEll 607 m = 25` for every m≥2.**
A kernel program packs each 61,308-term prefix into one integer with base-2⁶⁴
lanes, so the kernel multiplies it with GMP. Every reduction is checked rather
than trusted, by `a = r + Q·c` and a bitwise lane bound
([PackedSeries](../RamanujanTau/FiniteArithmetic/PackedSeries.lean)). The series come
from Euler's pentagonal theorem: Δ gives E₂ through θΔ = E₂Δ, and E₂ gives E₄ through
Ramanujan's equation ([Rank607Identities](../RamanujanTau/FiniteArithmetic/Rank607Identities.lean)).
The induction through L(51) uses `partition_two_eq_of_coeff_prefix`. See the
[verification record](verification/rank607_final.json).

Boylan–Webb §6.1 report r₆₀₇(m)=24 for all m≥1 but do not define rank for a non-free module. `rEll` is the least number of generators, so the two statements conflict only under that reading. At precision two, `Rank607Structure.lamEquiv` proves Λ^odd(3, 2) ≅ (ℤ/607²)²⁴ ⊕ ℤ/607: 25 generators, 24 of them free (invariant factors 1²⁴, 607). So BW's 24 is right at m=2 if their rank counts free summands, and wrong if it counts generators. At m=1, `Rank607One.lamEquiv1` proves Λ^odd(1, 1) ≅ (ℤ/607)²⁴ and `rEll_607_one` gives r₆₀₇(1)=24, agreeing with BW under either reading. `Rank607Threshold.bEll_607_two` proves the threshold b₆₀₇(2)=3=2m−1. The profile `[m×24, m−1]` for m≥3 is computed but not proved in Lean. Expert review is still needed before this is described as a correction.

### Boylan–Webb's threshold at 13, 17, 19, 23

[SmallThreshold](../RamanujanTau/FiniteArithmetic/SmallThreshold.lean) proves
b_ℓ(m) ≤ 2⌊m/2⌋+1 for every m ≥ 1 and b_ℓ(m) ≥ 3 for m ≥ 2, at ℓ = 13, 17, 19, 23.
Hence b_ℓ(2) = b_ℓ(3) = 3. The upper bound comes from the unconditional
Atkin–O'Brien recurrence ℓ^b ∣ L(b+2) − κL(b) (`AtkinOBrienFinal.L_padic`), through
`BLBound.mem_bSet_of_scalar`. The lower bound shows that no scalar c satisfies
ℓ² ∣ L(3) − cL(1). The certificate is a nonzero 2×2 determinant of the partition numbers
p(ℓm − e₁), p(ℓ³m − e₃), m = 1, 2, modulo ℓ²; the kernel computes them from a certified prefix
([PartitionPrefix](../RamanujanTau/FiniteArithmetic/PartitionPrefix.lean)). Numerics give
b_ℓ(m) = 2⌊m/2⌋+1 for all m tested.

The next step is also proved at all four primes:
[SmallThresholdFive](../RamanujanTau/FiniteArithmetic/SmallThresholdFive.lean) shows b_ℓ(m) ≥ 5
for m ≥ 4, so b_ℓ(4) = b_ℓ(5) = 5 (`SmallThresholdFive.bEll_13`, …, `bEll_23`). No scalar c
satisfies ℓ⁴ ∣ L(5) − cL(3). The certificate is the determinant
p(ℓ³−e₃)·p(2ℓ⁵−e₅) − p(2ℓ³−e₃)·p(ℓ⁵−e₅) mod ℓ⁴: 26364, 29478, 6859, 121670 at ℓ = 13, 17, 19, 23
(each vanishes mod ℓ³, as the recurrence requires). The kernel reads the partition numbers from
certified prefixes mod ℓ⁴ of 541,470 / 1,833,983 / 2,991,954 / 6,704,525 terms
(`PartitionPrefix.pgfPrefixG`). The pentagonal polynomial is built by halving, with no reductions.
The inverse comes from an untrusted Newton iteration and is checked by one product with
widened lanes. The module checks in about 70 s and 8.5 GB. (The partition-number route stops here,
since m ≥ 6 would need about 2ℓ⁷ terms; the all-m result below uses a different method.)

### Exactness of Atkin–O'Brien at 13, 17, 19, 23, and b_ℓ(m) = 2⌊m/2⌋+1

[AtkinExact](../RamanujanTau/FiniteArithmetic/AtkinExact.lean) proves b_ℓ(m) = 2⌊m/2⌋+1 for every
m ≥ 1 at ℓ = 13, 17, 19, 23 (`AtkinExact.bEll_13`, …, `bEll_23`). The input is exactness of the
Atkin–O'Brien recurrence: for every b ≥ 1 and every scalar c, ℓ^(b+1) ∤ L(b+2) − cL(b)
(`ExactAtkin13.exact`, …, `ExactAtkin23.exact`). The proved sufficient index b = m is thus minimal.

The proof is a finite model of the error dynamics ([ExactAtkin](../RamanujanTau/FiniteArithmetic/ExactAtkin.lean)).
Write L(b+2) − κL(b) = ℓ^b g_b. Then g_b lies in the offset-2 Katz envelope, T_b g_b = ℓ g_{b+1}
with T_b ∈ {U, D}, and ḡ_b is a cusp form of weight 2(ℓ−1) modulo ℓ (`env2_reduction`). Decompose
g_b = Σ c_k B_k/E² + ℓy with y in the offset-3 envelope. The matrix bounds (UB), (DB) send the
offset-3 envelope into one whose reduction is a constant plus a multiple of f̄ (`U_tail`, `D_tail`,
`tail_reduce`). So coefficient functionals killing 1 and f̄ see ḡ_{b+1} through the residues mod ℓ²
of T(B_k/E²) alone. A kernel-decided check over all c ∈ 𝔽_ℓⁿ (n = 2, 2, 3, 3) shows that ḡ_b ≠ 0
forces ḡ_{b+1} ≠ 0 for both U and D steps (`step`). The base ḡ_1 ≠ 0 is the mod-ℓ² partition
determinant of `SmallThreshold`. The per-prime data (prefixes of E₄, E₆, Δ, E_{ℓ−1}⁻¹, Φ modulo ℓ²
through degree 2ℓ or 3ℓ) are generated by `scripts/boylanwebb/gen_exact_atkin.py` and checked by
the kernel. The numerical model (U/D multipliers on the residual space) was confirmed in Python
before formalization.

In partition numbers ([AtkinExactPartition](../RamanujanTau/FiniteArithmetic/AtkinExactPartition.lean),
`partition_13`, …, `partition_23`): for every b ≥ 1 and every c ∈ ℤ_ℓ there is n with
24 ∣ ℓ^b n + 1 and ℓ^(b+1) ∤ p((ℓ^(b+2)n+1)/24) − c·p((ℓ^b n+1)/24). So the modulus ℓ^b in the
Atkin–O'Brien congruence cannot be raised, whatever multiplier is used. The proof inverts the
index map of `AtkinOBrienFinal.pser_dvd` (n = 24t − ℓ^(2⌈b/2⌉−b)) and multiplies by the unit
η-quotient relating L(b) to Σ p(ℓ^b t − e_b) q^t. As a numerical sanity check at ℓ = 13, b = 1,
the congruence mod 13 holds only for c ≡ 6, and every c mod 169 fails within 17 values of n.

### Boylan–Webb's threshold at every prime 61 ≤ ℓ ≤ 139, at every precision

`RankRAt61.bEll_61`, …, `RankRAt139.bEll_139` prove b_ℓ(m) = 2m−1 for every m ≥ 1 at
ℓ = 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113. With the earlier files, **b_ℓ(m) is now known exactly for every m at every prime
13 ≤ ℓ ≤ 139**. Boylan–Webb computed b_ℓ(2) for ℓ ≤ 89 and nothing beyond m = 3.

From 61 on the odd recurrence has order r ≥ 3 (r = d − s, with d = dim S_{ℓ−1} and s the number
of low coefficients killed by D). The generic order-r stack:

* **Hensel lift of order r** (`lift_padic_memR`, `FiniteArithmetic/OrbitLiftR.lean`).
* **Lower-bound criterion of order r** (`BLBound.not_mem_of_errorsR`, `BLBound/ThresholdR.lean`): r
  functionals with unit determinant on L(2k+1), …, L(2(k+r−1)+1) and one observation seeing U G_k;
  the coefficients are recovered with the inverse matrix (adjugate), so no rank-specific algebra.
* **Window determinant** (`RankR.Data.det_eq`): the r×r matrix of (a_{s+1}, …, a_{s+r}) on consecutive
  odd vectors is multiplied by the companion matrix at each step, so det_n = det₀·(det C)ⁿ.
* `RankRMod`, `RankRLift`, `RankRError`, `RankRMain`, `RankRPacked`, with data from
  `scripts/boylanwebb/gen_rankR.py` and one `decide +kernel` evaluation per prime (37 s at 67 to
  about 4 min and 16 GB at 109, 113). The (q^{ℓ²};q^{ℓ²}) truncation in `PackedPrime.prelude` now
  includes the q^{5ℓ²} and q^{7ℓ²} terms (`ea_trunc`, valid below 12ℓ²), and the lane count is a parameter.

Shapes (s, r): 61–71 (2, 3); 73–83 (3, 3); 89 (3, 4); 97–107 (4, 4); 109, 113 (4, 5); 127, 131 (5, 5); 137, 139 (5, 6). Kernel time at 127–139 is 14–28 min, 16–21 GB.
Controls at 61: a perturbed recurrence coefficient fails the Cayley–Hamilton identity, a perturbed
Θ entry fails the θ identities, and a perturbed z entry makes `ok` evaluate to `false`.

**Patterns in the certified data** (`scripts/frontier/pattern`-style PARI checks, not Lean):
* For every ℓ = 29, …, 113, charpoly(Θ) from the certified tables equals the prediction
  charpoly((12/ℓ)/5 · T_ℓ on S^new_{ℓ−5}(Γ₀(6)) with w₂ = −(2/ℓ), w₃ = −(3/ℓ)) of §4.4 of the research draft.
* For every ℓ = 37, …, 113, the order-r recurrence polynomial x^r − Σ kⱼxʲ (the unit part of
  charpoly X̄) equals charpoly((12/ℓ) · T_ℓ) on S^new_{ℓ−3}(Γ₀(6)) in the same sign class, and no other
  weight ℓ−7, …, ℓ+3, sign class or scalar matches. This is the integral-weight form of Theorem A,
  now confirmed on Lean-certified recurrences at 19 primes.
* dim K̄ = s = ⌊(ℓ²−1)/(24ℓ)⌋ equals the dimension of that weight-(ℓ−5) class for every prime
  29 ≤ ℓ ≤ 233, and no T_ℓ eigenvalue there is 0 mod ℓ.
* ū₀ is a cyclic vector for Θ at every ℓ = 53, …, 113 (statistically weak: a random vector would pass
  with probability about 0.8 overall). Simple θ-twists θʲL(1), θʲL(2) do not reproduce ū₀.

**Finite hypotheses at 149 ≤ ℓ ≤ 257 (numerical, not Lean).** `gen_rankR.py` (exact split-FFT products, Newton
inversion) checks every finite input of the generic Lean theorem `RankR.Data2.bEll_eq` at each prime 149 ≤ ℓ ≤ 257:
d = s + r, the order-r Cayley–Hamilton relation, det₀ ≠ 0, det C ≠ 0, Θ invertible and ū₀ ≠ 0. All hold, with
(s, r) rising to (10, 11) at 257. So b_ℓ(m) = 2m−1 for every m holds there numerically; the kernel check stops at
about 139 only for memory (about 20 GB at 127 on a 36 GB machine). An earlier run failing from 191 up was a
generator bug (pentagonal series cut at |k| ≤ 600), now fixed; data at ℓ ≤ 181 were unaffected.

**G4's hypothesis, numerically.** No prime 5 ≤ ℓ ≤ 2·10⁶ divides a_ℓ(h₈) for h₈ = 6.8.a.a (previously checked to 6·10⁴).

### Boylan–Webb's threshold at 53 and 59, at every precision

[RankSAt53](../RamanujanTau/FiniteArithmetic/RankSAt53.lean) and
[RankSAt59](../RamanujanTau/FiniteArithmetic/RankSAt59.lean) prove b_ℓ(m) = 2m−1 for every m ≥ 1 at
ℓ = 53, 59 (`bEll_53`, `bEll_59`). Boylan–Webb computed b_ℓ(2) for ℓ ≤ 89 and nothing beyond m = 3.

These are the first primes with dim S_{ℓ−1} = 4 and dim K̄ = 2. Because 2ℓ < δ = (ℓ²−1)/24, D kills
a₀, a₁, a₂, so the odd series reduce into the plane a₁ = a₂ = 0 and still satisfy a second-order
recurrence; the error is seen by two functionals and moves by a 2×2 matrix. The `Rank2` files are
generalized to s + 2 forms with s low coefficients killed (`RankSMod`, `RankSLift`, `RankSError`,
`RankSMain`, `RankSPacked`; s = 1 is the 37–47 case, s = 2 here):

* **Recurrence.** `RankS.odd_padic2`, with the odd envelope cut out by a₁ = … = a_s = 0 (needs
  ℓ s < δ) and the (a_{s+1}, a_{s+2})-determinant (−k₀)ⁿ·det₀ ≠ 0.
* **Error law.** For each of the s observations obs_a (each killing U of the plane
  a₁ = … = a_s = 0), the vector eₙ = (obs_a(U Gₙ))_a mod ℓ satisfies eₙ₊₁ = Θ eₙ
  (`RankS.Data2.divided_step`). Θ is invertible (an inverse is checked by `decide`) and e₀ ≠ 0, so
  eₙ ≠ 0 for every n, and at each n some obs_a sees Gₙ (`BLBound.not_mem_of_errors2_at`, the
  one-index form of the rank-two criterion).
* **Θ.** At 53, Θ = [[38, 18], [42, 22]], charpoly x² − 7x + 27 = (x+18)(x+28); at 59,
  Θ = [[45, 28], [34, 28]], charpoly x² − 14x + 13 = (x+46)(x+58). Both match the independent
  Katz-model table in [the research draft, §4.3](BL_SHARPNESS_PROOF.md#43-θ-numerics-n) and the
  paper. The initial error vectors are (45, 35) and (52, 58).
* **Data.** `PackedPrime.prelude` now takes the number of lane levels, so the prefixes run
  through degree 4ℓ²+1 (11,237 at 53, 13,925 at 59) over 2¹⁴ lanes. One `decide +kernel`
  evaluation of `RankSPacked.ok` per prime takes about 40 s.

The tables are proposed by `scripts/boylanwebb/gen_rankS.py`, which also reproduces θ = 20 at 37.
Controls: a perturbed z entry and a perturbed D-matrix entry make `ok` evaluate to `false` (the
`decide +kernel` run aborts), and a wrong Θ entry fails the `decide` identities.
Primes 61–71 have an order-three odd recurrence and 73 has s = 3 with order three; they are not
covered.

### Boylan–Webb's threshold at 37, 41, 43, 47, at every precision

[Rank2At37](../RamanujanTau/FiniteArithmetic/Rank2At37.lean), …,
[Rank2At47](../RamanujanTau/FiniteArithmetic/Rank2At47.lean) prove b_ℓ(m) = 2m−1 for every m ≥ 1
at the four primes with dim S_{ℓ−1} = 3 (`bEll_37`, `bEll_41`, `bEll_43`, `bEll_47`). Boylan–Webb
computed b_ℓ(2) for ℓ ≤ 89 and nothing beyond m = 3.

At these primes the odd partition series reduce modulo ℓ into the two-dimensional plane of
cusp forms vanishing to order two, so the order-one recurrence used at 29 and 31 does not exist.
The proof replaces it in four generic steps.

* **Recurrence.** A second-order Hensel lift (`lift_padic_mem2`) gives κ₀, κ₁ ∈ ℤ_ℓ with
  L(2n+5) − κ₁L(2n+3) − κ₀L(2n+1) = ℓ^(n+1)Gₙ, Gₙ in the second odd envelope (`Rank2.odd_padic2`).
  The rank-two leading-term decomposition (`Rank2.leading2`) uses that consecutive odd vectors
  have (a₂, a₃)-determinant (−k₀)ⁿ·det₀ ≠ 0 (`Data.det_eq`).
* **Non-membership.** `BLBound.not_mem_of_errors2`: two functionals separating L(2n+1), L(2n+3)
  modulo ℓ and one functional obs with obs∘U killing every odd series but not U Gₙ force
  L(2k+1) ∉ Λ^odd(2k+3, m).
* **Error law.** X Gₙ = ℓ Gₙ₊₁, and obs(U Gₙ₊₁) ≡ θ·obs(U Gₙ) (mod ℓ) (`Rank2.Data2.divided_step`),
  from the residues mod ℓ² of obs(Y fᵢ/E_{ℓ−1}) for a three-form basis fᵢ = Δ^j E₄^a E₆^b.
  θ = 20, 31, 31, 17, matching the slope-one Θ eigenvalues of
  [the research draft, §4.3](BL_SHARPNESS_PROOF.md#43-θ-numerics-n). The initial observation is
  34, 23, 10, 35.
* **Data.** [PackedPrime](../RamanujanTau/FiniteArithmetic/PackedPrime.lean) builds, for any prime p,
  packed prefixes modulo p² of (q;q)⁻¹, Δ, E₄, E₆ (from E₂ = 1 + θW/W), E_{p−1}⁻¹ ≡ 1 + 2pΣσ_{p−2}(n)qⁿ,
  and Φ_p, and proves each equal to the actual series (`prelude_spec`). One `decide +kernel`
  evaluation of `Rank2Packed.ok` per prime (about 18 s, 6 GB) checks every lane used:
  the Sturm data for U and D on the basis, the seed D(1), and the four mod-ℓ² observations.
  The identities in ZMod ℓ (Cayley–Hamilton, θ, the kill relation) are checked by `decide`.

The tables are proposed by `scripts/boylanwebb/gen_rank2.py`, whose independent q-series model
reproduces the three mod-29² data values of `ErrorDynamics29.Data` (348, 725, 696). Controls
rejected by the kernel: a perturbed z entry, a perturbed D-matrix entry, and a wrong θ.
See the [verification record](verification/rank2_threshold.json).

### Boylan–Webb's threshold at 29 and 31, at every precision

[ExactThreshold](../RamanujanTau/FiniteArithmetic/ExactThreshold.lean) proves
b₂₉(m) = b₃₁(m) = 2m−1 for every m ≥ 1 (`Exact29.bEll_29`, `Exact31.bEll_31`).
Here b_ℓ(m) is Boylan–Webb's invariant itself (`BLBound.bEll`), not the scalar
recurrence threshold of `Complete29`/`Complete31`. Boylan–Webb computed
b₂₉(1,2,3) = 1,3,5. The general criterion
([BLBound/Threshold](../RamanujanTau/BLBound/Threshold.lean)) shows that
L(2k+1) ∉ Λ^odd(2k+3, m) for all k ≤ m−2 forces equality. An ℓ-adic error
recurrence with one separating functional supplies that non-membership. See the
[verification record](verification/exact_threshold.json).

[PrecisionSquare](../RamanujanTau/FiniteArithmetic/PrecisionSquare.lean)
now proves `E ≡ 1−2pS` and `Einv² ≡ 1+4pS (mod p²)` for every prime p≥5,
where `S=Σ σ_(p−2)(n)q^n`. These are identities of the actual full Hasse
series and its inverse, not finite truncations. They identify the denominator
used in the reconstruction at 607 without computing B₆₀₆. They are the
denominator input to `Rank607Final`.

### Ramanujan's nested radical

[NestedRadical](../RamanujanTau/NestedRadical.lean) proves the classical identity

```text
sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + 4 sqrt(1 + ...)))) = 3.
```

The infinite expression is defined through finite truncations, with no
unspecified tail. More generally, for real a>0 and x≥0, define

```text
R₀(x) = a,
R_(N+1)(x) = sqrt(a² + x R_N(x+a)).
```

`bounds`, `error_bound`, and `tendsto_trunc` prove

```text
a ≤ R_N(x) ≤ x+a,
0 ≤ x+a−R_N(x) ≤ x(x+a)/(x+(N+1)a),
lim_(N→∞) R_N(x) = x+a.
```

Taking a=1 and x=2 gives `ramanujan_radical` and
`ramanujan_radical_error`: the truncations converge to 3 and their errors
are at most `6/(N+3)`. Here N counts the inserted multipliers:
the first truncations are 1, √3, √5, and √(1+2√(1+3√5)).

The algebraic pattern is `a²+x(x+2a)=(x+a)²`. Rationalizing one square
root gives the exact error identity
`(x+a−R_(N+1)(x))(x+a+R_(N+1)(x))=x(x+2a−R_N(x+a))`.
The lower bound `R_(N+1)(x)≥a` gives a telescoping error estimate.
Consequently, convergence is proved rather than assumed from the pattern.

This is a formalization of a classical identity, with an explicit convergence
proof. For mathematical context, see the
[2026 discussion of Ramanujan's iteration](https://arxiv.org/html/2602.07122v1)
and [Mukherjee's work on convergence estimates](https://arxiv.org/abs/1303.4251).
The [verification record](verification/nested_radical.json) and
[audit](../scripts/audit/nested_radical.lean) record the checked theorem boundary.

#### Affine family and exponential error bounds

[NestedRadicalAffine](../RamanujanTau/NestedRadicalAffine.lean) extends the
proof to real parameters d>0, 0≤h≤d, and x≥0. Put

```text
C(x) = d²+(d−h)x,
T₀(x) = sqrt(C(x)),
T_(N+1)(x) = sqrt(C(x)+x T_N(x+h)).
```

`tendsto_affineTrunc` proves `T_N(x) → x+d`, including h=0. The following
examples therefore have exact values:

```text
sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + 4 sqrt(...)))) = 3,   d=1, h=1, x=2;
sqrt(6 + 2 sqrt(7 + 3 sqrt(8 + 4 sqrt(...)))) = 4,   d=2, h=1, x=2;
sqrt(13 + 2 sqrt(15 + 3 sqrt(17 + 4 sqrt(...)))) = 5, d=3, h=1, x=2.
```

The coefficient rule has a full converse about actual limits in
[NestedRadicalClassification](../RamanujanTau/NestedRadicalClassification.lean).
For A,B,h≥0 and d>0, define finite radicals with radicands `A+B(x+nh)`
and multipliers `x+nh`. `linear_limit_iff` proves

```text
(For every x≥0, the finite radicals converge to x+d)
    if and only if A=d² and B=d−h.
```

Equivalently, `exists_linear_limit_iff` says that such a positive-offset
linear limit exists exactly when `A=(B+h)²` and `B+h>0`. Its value is then
`x+B+h`. Continuity forces the layer identity from the asserted limits;
`affine_identity_iff` identifies its coefficients; the quantitative family
theorem supplies the converse. This classification requires the linear answer
for **every starting x≥0**. It does not classify isolated radical values or
all possible nonlinear limits.

The new quantitative theorem `affine_error_bound` is

```text
0 ≤ x+d−T_N(x) ≤ (x+d) log((x+Nh+d)/d) / 2^N.
```

Its mechanism is that each square-root layer at least halves the logarithmic
gap between the finite tail and the exact tail. The formal theorem
`log_gap_contract` isolates that inequality for reuse. The stated error
bound proves convergence without relying on a formal infinite substitution.

For the classical radical, `ramanujan_radical_fast_error` specializes this to
`0≤3−r_N≤3 log(N+3)/2^N`, using the same truncation convention as above.
`ramanujan_radical_40_accuracy` certifies `0≤3−r_40<10^(-10)` using exact
inequalities in Lean, without floating-point evaluation of the radical.

For comparison, [Mukherjee, Example 4.3](https://arxiv.org/html/1303.4251v3#S4)
derives an error estimate of order `n³/2^n` with a different depth convention.
The logarithmic bound here is stronger than that displayed estimate; this
comparison does not establish priority over other convergence results.
The [follow-up record](verification/nested_radical_affine.json) and
[16-declaration audit](../scripts/audit/nested_radical_affine.lean) cover
the family, converse, and accuracy certificate.

### Supporting q-series infrastructure
Bailey pairs & the Bailey chain / transform (`MockTheta5Bailey*`), the classical and bilateral Jacobi
triple products (`MockTheta5JacobiTriple` / `…Bilateral` / `…ClassicalJTP`), Durfee-rectangle identities
(`MockTheta5Durfee*`), Cauchy/Euler sum=product identities, even/odd and distinct=odd partition theorems,
Gauss/alternating theta evaluations, and the fifth-order mock-theta definitions (`MockTheta5R1`, `MockTheta5Defs`;
Ramanujan's R1 itself is proved in `Watson/R1.lean`).

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
  kernel evaluation (`decide +kernel`).
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
`TauHeckeMaster` is now a theorem: `HeckeQExp` constructs the Hecke operators `T_p` and provides an
instance, so `TauMultiplicative` and `TauHeckeRecurrence` hold unconditionally (Mordell 1917). `TauMod691` is
also a theorem (`TauModular`). `DeligneBound` *is* Deligne's proof of the Weil conjectures (out of reach; the best proved exponent is Weil's
23/4, `StepanovAS.tau_isBigO_23_4_unconditional`), and `LehmerConjecture` is open (proved for
`n < 214,928,639,999 (Lehmer 1947)`, `LehmerSmall.lehmer_below_214928639999`).

- **`HeckeCore` / `HeckeForm` / `HeckeQExp`** — **the Hecke operators `T_p` on level-one cusp forms, and
  Mordell's theorem for `τ`**. For a prime `p`, `T_p f(z) = p^{k−1}f(pz) + p⁻¹Σ_{j<p} f((z+j)/p)`.
  * `HeckeCore`: `T_p f` is invariant under `T` and `S`. Under `S`, the `f(pz)` term trades places with the
    `j = 0` translate. For `1 ≤ j < p`, the matrix `(j −m; p −j')` with `j' ≡ −j⁻¹ (mod p)` and `jj'+1 = pm`
    sends `(z+j')/p` to `(−1/z+j)/p`, and the involution `j ↦ j'` permutes the other translates.
  * `HeckeForm`: `heckeCusp p : CuspForm 𝒮ℒ k → CuspForm 𝒮ℒ k` (modularity via
    `slash_action_generators_SL2Z`, holomorphy, vanishing at `i∞`).
  * `HeckeQExp`: `qExpansion_hecke : (T_p f)ₘ = f_{pm} + p^{k−1}[p ∣ m]f_{m/p}`, from the root-of-unity sum
    `Σ_{j<p} ζ^{jn} = p[p ∣ n]` and `qExpansion_coeff_unique`. Together with `dim S₁₂ = 1` and the Δ bridge,
    this gives `heckeData : HeckeData` and the unconditional theorems
    ```lean
    theorem tau_mul_coprime {m n : ℕ} (h : m.Coprime n) : τ (m * n) = τ m * τ n
    theorem tau_hecke_recurrence {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) :
        τ (p ^ (r + 1)) = τ p * τ (p ^ r) - (p : ℤ) ^ 11 * τ (p ^ (r - 1))
    ```
    The Euler-factor and Gegenbauer closed forms (`EulerFactor`, `Gegenbauer`) are therefore unconditional too.
- **`TauLSeries`** — **Ramanujan's L-function and its Euler product.**
  ```lean
  theorem tau_isBigO : tauC =O[atTop] fun n : ℕ => (n : ℝ) ^ (6 : ℝ)        -- Hecke's bound
  theorem LSeries_tau_eulerProduct {s : ℂ} (hs : 7 < s.re) :
      HasProd (fun p : Nat.Primes =>
        (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹) (LSeries tauC s)
  ```
  Hecke's bound is Mathlib's `CuspFormClass.qExpansion_isBigO` applied to `Δ` through the q-expansion bridge.
  The product uses Mathlib's `eulerProduct_hasProd` with `tau_mul_coprime`. The local factor
  `Σ τ(pᵉ)xᵉ = (1 − τ(p)x + p¹¹x²)⁻¹` follows from the Hecke recurrence.

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

- **`TauCongruences`** — Ramanujan's elementary congruences for `τ(n) := [qⁿ] q∏(1−qᵏ)²⁴` (`tauPS`), all
  unconditional:
  ```lean
  theorem tau_odd_iff (n : ℕ) : Odd (tauPS n) ↔ ∃ m, n = (2 * m + 1) ^ 2
  theorem tau_mod3 {n : ℕ} (hn : n % 3 ≠ 1) : (3 : ℤ) ∣ tauPS n
  theorem tau_mod5 {n : ℕ} (hn : n % 5 = 0) : (5 : ℤ) ∣ tauPS n
  theorem tau_mod7 {n : ℕ} (hn : n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : (7 : ℤ) ∣ tauPS n
  -- Wilton: 23 ∣ τ(n) whenever n is a quadratic non-residue mod 23
  theorem tau_mod23 {n : ℕ} (hn : n % 23 ∈ ({5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22} : Finset ℕ)) : (23 : ℤ) ∣ tauPS n
  ```
  All four use Frobenius, `(q;q)_∞^{pᵉ} ≡ (q^{pᵉ};q^{pᵉ})_∞ (mod p)` (`frob_qfacInf`), together with Jacobi's cube
  identity. For example, `q(q)²⁴ ≡ q(q⁸;q⁸)³ ≡ Σ q^{(2m+1)²} (mod 2)`. Mod 7, the identity
  `8(1+T_m) = (2m+1)² + 7` puts every exponent of `q(q⁷;q⁷)³(q)³` in a square class mod 7, and in the class `0` the
  coefficient `2m+1` is itself divisible by 7.
  Mod 23, `q(q)²⁴ ≡ q(q²³;q²³)(q;q)` and `24(1 + k(3k−1)/2) = (6k−1)² + 23`, so every exponent lies in a square class.
- **`TauBridge`** — `tau_eq_tauPS : RamanujanTau.tau n = [qⁿ] q∏(1−qᵏ)²⁴`. It identifies the computable list-based
  `τ` with the power-series coefficient: every list operation is the matching ring operation, and truncation
  agrees modulo `X^{d+1}`. Consequently the congruences above hold for the computable `τ` (`tau_odd_iff'`,
  `tau_mod7'`, `tau_mod23'`).
- **`DiscriminantQExpansion`** — **the analytic–formal bridge**: for every `n`,
  ```lean
  theorem qExpansion_discriminant_coeff (n : ℕ) : (qExpansion 1 Δmod).coeff n = (TauCong.tauPS n : ℂ)
  ```
  i.e. Mathlib's analytic `Δ = η²⁴` has q-expansion coefficients exactly `[qⁿ] q∏(1−qᵏ)²⁴`. The proof uses no
  analytic-product → `FormalMultilinearSeries` machinery. The polynomial partial products `q(∏_{k<N}(1−qᵏ⁺¹))²⁴`
  converge locally uniformly on the unit disc to `Δ`'s cusp function. Iterated Weierstrass
  (`TendstoLocallyUniformlyOn.deriv`) then carries their `n`-th Taylor coefficients to `Δ`'s, and those
  coefficients are eventually constant, equal to `τ(n)`.
- **`TauModular`** — consequences that tie the two halves of the `τ` arc together:
  * `tau_mod691`, `tau_computable_mod691`, `tau_prime_mod691`: Ramanujan's `τ(n) ≡ σ₁₁(n) (mod 691)` for the
    combinatorial and computable `τ`. This replaces the `TauMod691` hypothesis class with a theorem.
  * `discriminant_formal_identity`: `1728·q∏(1−qⁿ)²⁴ = (1+240Σσ₃qⁿ)³ − (1−504Σσ₅qⁿ)²` in `ℤ⟦q⟧`. This is a
    purely formal identity of integer power series, proved through modularity.
  * `qExpansion_discriminant_eq`: `qExpansion(Δ) = q(q;q)_∞²⁴` in `ℂ⟦q⟧`.

---


## References

- Ramanujan, S. (1916). "On certain arithmetical functions." *Trans. Cambridge Philos. Soc.* **22**.
- Ramanujan, S. (1919). "Some properties of p(n), the number of partitions of n." *Proc. Cambridge Philos. Soc.* **19** — the congruence `p(5n+4)≡0 (mod 5)`.
- Euler, L. — the pentagonal number theorem. · Jacobi, C. G. J. (1829). *Fundamenta Nova* — the triple product and cube identity.
- Andrews, G. E. *The Theory of Partitions* — Bailey chains, Durfee squares, the Jacobi triple product.
- Deligne, P. (1974). `|τ(p)| ≤ 2p^{11/2}` (Weil conjectures). · Lehmer, D. H. (1947), *Duke Math. J.* **14**.
- Apostol, T. M. *Modular Functions and Dirichlet Series in Number Theory*.
- OEIS [A000594](https://oeis.org/A000594) (τ), [A000041](https://oeis.org/A000041) (p(n)).
