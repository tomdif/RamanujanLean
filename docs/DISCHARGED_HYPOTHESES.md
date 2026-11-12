# Discharged hypotheses (audit, 2026-11-04)

New Lean files: `RamanujanTau/Discharge/{Congruences,Bridge,Kloosterman,AtkinInputs}.lean`.
Every declaration listed is axiom-clean (`#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound`). The original audit built these four targets separately. All four are now
included in the `RamanujanTau.lean` import graph and the current full build.

Evidence levels: (1) Lean, axiom-clean; (2) Lean, conditional on named hypotheses; (3) paper only; (4) numerics only.

## 1. Hypothesis classes now with instances

| Class (file) | Instance / theorem (new) | Discharged by | Notes |
|---|---|---|---|
| `TauMod7` (Congruences/Mod7) | `Discharge.tauMod7`, `tau_mod7_unconditional` | `LehmerSmall.tau_mod7_all` + `tau_eq_tauPS` + `sigma3_eq` | (1). Stronger than the class: holds for all `n ≥ 1`, with no `Coprime n 7` condition. |
| `TauMod25` (Congruences/Mod5) | `Discharge.tauMod25`, `tau_mod25_unconditional` | `LehmerSmall.tau_mod25_all` + bridges | (1). Holds for all `n ≥ 1`, with no `Coprime n 5` condition. |
| `TauMod23` (Congruences/Mod23) | `Discharge.tauMod23`, `tau_mod23_unconditional` | `TauCong.tau_mod23` (Wilton, Frobenius + pentagonal) via `TauBridge.tau_mod23'` | (1). Holds for every `n` that is a non-square mod 23, not just primes. Uses `decide` on `ZMod 23` to list the non-squares. |
| `TauMatchesDiscriminant` (MathlibBridge) | `Discharge.tauMatchesDiscriminant`, `discriminantQExpansion_eq_tau_unconditional` | `DiscriminantBridge.qExpansion_discriminant_coeff` + `tau_eq_tauPS` | (1). Previously had **no instance**. The `MathlibBridge` audit chain (Lehmer ⇔ nonvanishing of Δ's q-coefficients, …) is now unconditional. |
| `TauHeckeMaster` | already global: `HeckeQExp.tauHeckeMaster` | `heckeData` | (1). Re-exported as `tauHeckeMaster_holds`. |
| `TauHeckeRecurrence`, `TauMultiplicative` | already global: `instTauHeckeRecurrenceOfMaster`, `instTauMultiplicativeOfMaster` | the master identity | (1). Re-exported as `tauHeckeRecurrence_holds` and `tauMultiplicative_holds`. Files that only use `[TauHeckeRecurrence]` or `[TauMultiplicative]` (Gegenbauer, HeckePowers, EulerFactor, LehmerReduction, Multiplicativity) are discharged once `HeckeQExp` is imported. |
| `TauMod691` | already global: `TauModular.tauMod691` | — | (1) |
| `TauMod27`, `TauMod2_8`, `TauMod2_11` | — | handled by the LehmerSmall agent | not touched here |

## 2. Named Prop hypotheses: where used, discharged by, unconditional corollary

| Hypothesis | Used in | Discharged by | Unconditional corollary |
|---|---|---|---|
| `TauBound.PoincareFormula` | TauBound/Endgame, Main | `WeilKloosterman.poincareFormula` | `TauBound.tau_isBigO_47_8_unconditional` (existing) |
| `PoincareIsCuspForm`, `PoincareUnfolding`, `PoincareFirstCoeffNeZero` | TauBound/Poincare, Honest, Final | `TauBound.poincareIsCuspForm`, `poincareUnfolding`, `poincareFirstCoeffNeZero` | existing (above) |
| `HasPoincareCoeffs f` | TauBound/Reduction | not proved directly. The other route (`poincareFormula`) bypasses it | — |
| `KloostermanBound α` | TauBound/Endgame | `kloostermanBound_one`, `_three_quarters`, `_of_local` | **new** `Discharge.Kloosterman.kloostermanBound_half_unconditional δ` (Weil, `1/2+δ`) and `kloostermanBound_twoThirds_unconditional δ` (Salié) |
| `SaliePrimeBound` | WeilKloosterman/Main | `Stepanov.saliePrimeBound` | `Stepanov.tau_isBigO_35_6_unconditional` (existing) |
| `WeilPrimeBound` | WeilKloosterman/Main | `StepanovAS.weilPrimeBound` | `StepanovAS.tau_isBigO_23_4_unconditional` (existing) |
| `PrimeKlBound (1/2)` | WeilKloosterman/Main | Weil | **new** `primeKlBound_half_unconditional` |
| `LocalKlBound α C` | WeilKloosterman/Assembly | `localKlBound_half` + Weil | **new** `localKlBound_half_unconditional` |
| `StepanovKloostermanEventually` | KloostermanL/Main | `StepanovAS.stepanovKloostermanEventually` | existing |
| `StepanovKloosterman` (uniform C, all r ≥ 1) | KloostermanL/Main | **previously unproved** | **new** `stepanovKloosterman_unconditional` with C = 2: the eventual bound plus amplification give \|α\|,\|β\| ≤ √p, so \|K_r\| ≤ 2p^{r/2} |
| `XiKernelHyp` | GORZXi/XiMain, XiTaylor | `GORZXi.xiKernelHyp_holds` | `xi_gorz_unconditional` (existing) |
| `CVHyp` | GORZXiEff/Main | `cvHyp_holds` | `turan_gamma_unconditional`, `jensen2_gamma_unconditional` (existing) |
| `Andrews66.Hb`, `MockCusp.HbEven` | Andrews66/Final, Printed, OmegaB, Arc | `MockCusp.Hb_holds`, `HbSharp_holds`, `HbEven_holds` | `andrews_1966_unconditional`, `andrews_1966_isBigO_unconditional`, `andrews_1966_sqrt_log_unconditional` (existing) |
| `JensenTail d n₀` | JensenThreshold/Jensen6, Jensen7 | `jensen6_tail`, `jensen7_tail` | `jensen{6,7}_threshold_unconditional` (existing) |
| `NewtonId d` | JensenThreshold | `newton6`, `newton7`, `GORZ.newtonId` | existing |
| `EtaHeckeMod`, `EtaHecke` | AtkinSporadic/*, AtkinTwisted, OnoWeaverMore | `etaHeckeMod_{13,17,19,23}`, `GaussSign.etaHecke_all`, `AtkinTwisted.etaHeckeMod` | `atkin_13_unconditional`, `ono_*_unconditional`, `weaver_17_unconditional`, OnoWeaverMore/Instances* (existing) |
| `GaussSign Q k` | HalfHecke/EtaHecke | `gaussSign_of_even` (even k only) | `etaHecke_all` for all k ≥ 2: odd k is handled by vanishing of odd weight forms. **FALSE as stated for odd k with Q ≡ 3 (mod 4)** (already documented in GaussSign/EtaHeckeAll) |
| `DimOneProp` | AtkinSporadic, OnoWeaverMore | `dimOne_{13,17,19,23,29,31}` | existing |
| `HorocycleLimit L` | EisensteinReal/Asymptotic | `horocycleLimit_zagier`, `exists_horocycleLimit` | `rankinSelberg_asymptotic_unconditional`, `sum_tau_sq_asymptotic_unconditional`, `rankinSelberg_asymptotic_zagier_unconditional` (existing) |
| `KarHyp` | EisensteinReal/Karamata (generic Karamata lemma) | `karHyp_tau` | existing |
| `Atkin11.Inputs` | Atkin11Final, Atkin11Matrix (`variable`) | `Atkin11.inputs_proved` | `ramanujan_pow11_unconditional` (existing) |
| `RamanujanODE` | Igusa/Charts, Katz, Serre | `RamanujanODEProof.ramanujanODE` | Igusa/Unconditional (`igusa_chartT'`, `igusa_chartS'`, `exists_ss'`, `katz_iff_hasse'`) (existing) |
| `ThetaId` | MTC/Chi0Final | `Watson.thetaId` | `chi0_identity`, `rank_chi0` (existing) |
| `E817`, `E817₁` | MTC/Final0, Final1 | `E817_holds`, `E817₁_holds` | `mtc0`, `mtc1`, `mock_theta_conjecture_f1` (existing) |
| `AADModularity`, `AADRaisedModularity` | TheoremA/LiftReduction | `ThetaLift.aadModularity`, `aadRaisedModularity` | `theoremA_unconditional`, `X_injective_unconditional` (existing) |
| `GoodStep` | BLBound/SlopeCounts | `goodStep_of_prime` | existing |
| ErrorDynamics29/31 `Data` | FiniteArithmetic | `CertifyError31.data` (and the corresponding certificate for 29) | existing |
| **Atkin–O'Brien chain:** `UB`, `DB`, `HQ`, `HG`, `HConj`, `QuotBound`, `QuotEBound`, `QuotValBound`, `OrdEBound`, `OrdBound`, `ProdDelta` | ~40 conditional theorems: DBound/Final, VLayer/*, SharpHQ/Final, UBSharp/Final, QuotE/Combine, AtkinOBrienMain/*, AtkinOBrienFinal/Main, OrdQuot/Main, FiniteArithmetic/ExactAtkin | proofs scattered across OrdQuot/Prod, QuotE, UBSharp, ConjAlg/NoKer, SharpHQ, VLayer, `SmallThreshold.ub_db` | **new** `Discharge.AtkinInputs.{prodDelta, ordEBound, quotEBound, quotValBound, quotBound, ordBound, hConj, UB}_unconditional` (ℓ ≥ 5 prime, at `SharpHQ.φC ℓ`), `HQ_unconditional`, `DB_unconditional` (ℓ ≥ 11), `HG_unconditional`. Headlines: `OrdQuot.atkin_obrien_{13,17,19,23}` and `FiniteArithmetic.AtkinExact.bEll_{13,17,19,23}` (existing) |
| `TateKernels`, `ThetaLaw`, `EtaLaw`, `ZLaw`, `SSDetect`, `GB`, `AC` | various internal files | `TateAdd.tateKernels`, `thetaLaw`, `zLaw`, `ssDetect_of_support`, … | internal lemmas. Headlines are already unconditional |

## 3. Still open (genuinely unproved in the repo)

| Hypothesis | Used in | Status / reason |
|---|---|---|
| `DeligneBound` (Deligne.lean) | `HafnerFinal.tauL_positive_proportion_deligne` and its arithmetic inputs | Deligne’s theorem is not proved unconditionally here. The companion RamanujanWeil retains geometric inputs; see [HAFNER_PROPORTION](HAFNER_PROPORTION.md). |
| `LehmerConjecture` | LehmerReduction (iff with prime powers) | open problem. Proved here for `1 ≤ n < 214,928,639,999`; see [LEHMER_SMALL_N](LEHMER_SMALL_N.md) |
| `AndrewsDragonette.HKS n θ C` with θ < 1/2 | `adPartial_converges_of_HKS` | needs Kloosterman-type cancellation in the modulus aspect. Only `HKS_trivial` (θ = 1) is proved, which is too weak for convergence (needs θ < 1/2) |
| `GORZXiD3.DLHyp` | `hot_gamma`, `jensen3_gamma` | Dimitrov–Lucas-type Lipschitz bound for `Ξ`'s Taylor data. Only `dlHyp_of_mono` reduces it to monotonicity of the Turán defect. Numerics (4) for n ≤ 3000 |
| `DBound.HV`, `VLayer.HVQ`, `DBound.HW` | DBound/HW, DBound/Final, VLayer/Final (`atkin_obrien_ℓ'`, `''`) | **not proved**, only **bypassed** (`VLayer.DB_of_UB_HQ`). The theorems that take them are superseded by the unconditional `OrdQuot.atkin_obrien_{13,17,19,23}`. The corrected “No hidden hypotheses” section of [the proof record](ATKIN_OBRIEN_PROOF.md) distinguishes these bypassed inputs from discharged ones. No theorem here concludes `HV` or `HVQ`; the headline theorems are unaffected |
| `UBound.GeomU` | UBound/Reduce, Final, Cp (`atkin_obrien_ℓ_geom`, `_Cp`) | not proved. Bypassed: `UB` is proved via `UBSharp.UB_of_E_C` |
| `TauBound.HasPoincareCoeffs` | `poincareFormula_of_cuspForm` | not proved. Bypassed (see above) |
| `E8ThetaData` (structure) | E8Eisenstein (`eq_E4`, `root_count`) | needs modularity of the E₈ theta series (Poisson summation). Not in Mathlib |
| `FourWitnessLinearBound c` | MultiQuintupleFourWitnessBound | research conjecture. **FALSE for c ≤ 2/5** (`not_fourWitnessQuarterBound`, `not_fourWitnessTwoFifthsBound`), and any valid c satisfies c ≥ 7/17 (`fourWitnessLinearBound_ge`) |
| MultiQuintuple `*Mod3*Input` structures | MultiQuintuple{RootBranch, RootVanishingEquivalence, ThetaArithmetic} | data records for case analyses, not hypotheses. Not audited further |

## 4. False or vacuous as stated

* `HalfHecke.GaussSign Q k`: false for odd k when Q ≡ 3 (mod 4). Known and documented. `etaHecke_all` routes around it.
* `FourWitnessLinearBound c`: false for c ≤ 2/5, and the repo proves this. It is a conjecture only for c ≥ 7/17.
* No other hypothesis was found to be false or vacuous. The class hypotheses `TauMod7`/`TauMod25` were
  needlessly weak (coprimality is unnecessary), and `TauMod23` is stated only for primes although it holds for
  every n.
* Caveat: the `Discharge.AtkinInputs` statements are elaborated with `open Classical` (`DecidableEq ℂ_[ℓ]`).
  They are Props, so another instance can be used via `convert`/`Subsingleton.elim`.
