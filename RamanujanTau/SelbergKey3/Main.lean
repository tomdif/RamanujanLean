/-
# Selberg's key lemma, third pass — entry point

M1(c) `LagDeriv`; M2 building block `IBP` (two-fold integration by parts).
M1(c) `LagDeriv`: all `u`-derivatives of the lag weight `u ↦ W̃_{u,u+v}(ξ)`, uniformly in `|v| ≤ 1`.
See `docs/SELBERG_KEY.md` (2026-11-06, third section).
-/
import RamanujanTau.SelbergKey3.LagDeriv
import RamanujanTau.SelbergKey3.IBP

open RamanujanTau.SelbergKey3

#print axioms iteratedDeriv_Rf_neg
#print axioms iteratedDeriv_Pf
#print axioms norm_Pd_le
#print axioms hasDerivAt_intPd
#print axioms iteratedDeriv_Wl
#print axioms norm_intPd_le
#print axioms Wsh_eq_Wl_pos
#print axioms Wsh_eq_one_add_Wl
#print axioms combine_r
#print axioms Wlag_iteratedDeriv_bound
#print axioms ibp_once
#print axioms ibp_twice
