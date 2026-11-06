/-
# Selberg's key lemma, fourth pass (M2 building blocks) — entry point

M2.0 `Phase` (the phase `U(u,u+v)` and its derivatives), M2.1 `Window` (smooth admissible
window `φ_T`), M2.2 `FarTerm` (one off-diagonal `t`-integral, two integrations by parts),
M2.3 `XiDeriv` (`ξ ∂_ξ W̃`), M2.5a `Term` (one windowed term of the expansion), M2.4 core `Line` (line partial sums = box sums, `scs2_general`,
Abel summation).  See `docs/SELBERG_KEY.md` (2026-11-06, fourth section).
-/
import RamanujanTau.SelbergKey4.FarTerm
import RamanujanTau.SelbergKey4.XiDeriv
import RamanujanTau.SelbergKey4.Term
import RamanujanTau.SelbergKey4.Line

open RamanujanTau.SelbergKey4

#print axioms Ush_eq
#print axioms hasDerivAt_eG
#print axioms hasDerivAt_Ulag
#print axioms hasDerivAt_Ulag1
#print axioms Ulag_bounds
#print axioms admissible_phiT
#print axioms phiT_zero_outside
#print axioms Wv_package
#print axioms FW_package
#print axioms R_le
#print axioms gT2_bound
#print axioms farTerm_bound
#print axioms lineSum_eq_shiftSum2
#print axioms abs_lineSum_le
#print axioms norm_sum_mul_le_abel
#print axioms hasDerivAt_Kf_xi
#print axioms norm_Vl_le
#print axioms hasDerivAt_Wl_xi
#print axioms Wxi_bound
#print axioms term_eq
#print axioms norm_kap4
#print axioms term_integral_eq
#print axioms term_integral_bound
