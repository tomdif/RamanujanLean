import RamanujanTau
/-! Axiom audit for the 2026-11-03 results: Kloosterman's τ bound, Jensen thresholds
N(6), N(7), Dragonette's asymptotic, the Ono–Weaver congruences, and the uniform
Boylan–Webb lower-bound results. Expected: only propext, Classical.choice, Quot.sound,
with no exceptions. -/
#print axioms RamanujanTau.TauBound.tau_isBigO_47_8_unconditional
#print axioms RamanujanTau.TauBound.poincareIsCuspForm
#print axioms RamanujanTau.WeilKloosterman.norm_kloosterman_primePow_le_sqrt
#print axioms RamanujanTau.WeilKloosterman.tau_isBigO_23_4_of_weil
#print axioms JensenThreshold.jensen6_threshold_unconditional
#print axioms JensenThreshold.jensen7_threshold_unconditional
#print axioms GORZ.jensen_eventually_hyperbolic
#print axioms GORZ.tendsto_coeff_Jhat
#print axioms GORZXi.gorz_thm3
#print axioms GORZXi.gammaMathlib_eq
#print axioms GORZXi.xi_gorz_mathlib
#print axioms GORZXi.xiKernelHyp_holds
#print axioms GORZXi.xi_gorz_unconditional
#print axioms Dragonette.dragonette
#print axioms Dragonette.dragonette_literal
#print axioms Dragonette.rank_parity_sign
#print axioms Andrews.alpha_sign
#print axioms Andrews.rank_parity_sign_all
#print axioms Andrews66.andrews_k1_isBigO
#print axioms Andrews66.andrews_1966_sqrt_log_of_Hb
#print axioms Andrews66.andrews_1966_printed_isBigO_of_Hb
#print axioms MockCusp.Hb_odd
#print axioms MockCusp.Hb_holds
#print axioms MockCusp.andrews_1966_unconditional
#print axioms MockCusp.andrews_1966_sqrt_log_unconditional
#print axioms AndrewsDragonette.not_Hb_of_neg
#print axioms AndrewsDragonette.adPartial_converges_of_HKS
#print axioms RamanujanTau.AtkinSporadic.Weaver.ono_13_unconditional
#print axioms RamanujanTau.AtkinSporadic.Weaver.weaver_17_unconditional
#print axioms RamanujanTau.AtkinSporadic.Atkin13.atkin_13_unconditional
#print axioms RamanujanTau.HalfHecke.etaHecke_11_168
#print axioms RamanujanTau.GaussSign.etaHecke_all
#print axioms RamanujanTau.GaussSign.gaussQuad_eval
#print axioms RamanujanTau.AtkinTwisted.eigen_all
#print axioms RamanujanTau.AtkinTwisted.G1.atkin_13_89
#print axioms RamanujanTau.OnoWeaverMore.L19.atkin_19_13_progression
#print axioms RamanujanTau.OnoWeaverMore.L29.atkin_29_17_progression
#print axioms RamanujanTau.OnoWeaverMore.L31.atkin_31_101_progression
#print axioms RamanujanTau.BWSharpAll.tendsto_bEll
#print axioms RamanujanTau.BWSharpAll.bEll_eq_all_of_int_dets
#print axioms RamanujanTau.KloostermanL.kloosterman_L_rational
#print axioms RamanujanTau.KloostermanL.tau_isBigO_23_4_of_stepanov
#print axioms RamanujanTau.Stepanov.hasseWeil_charSum_le
#print axioms RamanujanTau.Stepanov.hasse_elliptic
#print axioms RamanujanTau.Stepanov.tau_isBigO_35_6_unconditional
#print axioms RamanujanTau.StepanovAS.weilPrimeBound
#print axioms RamanujanTau.StepanovAS.tau_isBigO_23_4_unconditional
#print axioms RamanujanTau.RankinSelberg.rankinSelberg_two_sided
#print axioms GORZXiEff.gamma_eq_mom
#print axioms GORZXiEff.jensen2_gamma
#print axioms GORZXiD3.hyperbolic_cubic
#print axioms GORZXiD3.disc_jensen3
