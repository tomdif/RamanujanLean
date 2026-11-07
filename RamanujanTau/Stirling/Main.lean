/-
# `Stirling/`: Gamma ratios in vertical strips and the Rankin–Selberg error `δ < 1/3`

Build: `nice -n 10 lake build RamanujanTau.Stirling.Main`. See `docs/STIRLING_RANKIN.md`.
-/
import RamanujanTau.Stirling.Third
import RamanujanTau.Stirling.Absolute

#print axioms RamanujanTau.Stirling.norm_Gamma_mul_rpow_le
#print axioms RamanujanTau.Stirling.norm_Gamma_mul_rpow_le_add
#print axioms RamanujanTau.Stirling.norm_Gamma_add_le
#print axioms RamanujanTau.Stirling.norm_Gamma_ratio_le_of_le
#print axioms RamanujanTau.Stirling.norm_Gamma_ratio_le_of_ge
#print axioms RamanujanTau.Stirling.norm_Gamma_half_sq
#print axioms RamanujanTau.Stirling.norm_Gamma_le_stirling
#print axioms RamanujanTau.Stirling.stirling_le_norm_Gamma
#print axioms RamanujanTau.Stirling.integral_line_eq_rpow
#print axioms RamanujanTau.Stirling.rieszAsymp_of_continuation_rpow
#print axioms RamanujanTau.Stirling.ratioEps_le
#print axioms RamanujanTau.Stirling.fEps_bound
#print axioms RamanujanTau.Stirling.Efun_bound_eps
#print axioms RamanujanTau.Stirling.Fb_bound_eps
#print axioms RamanujanTau.Stirling.power_saving_third_of_RSDataM
#print axioms RamanujanTau.Stirling.power_saving_third_RSFn
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_third_general
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_67_100_general
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_third
#print axioms RamanujanTau.Stirling.rankinSelberg_power_saving_67_100
