/-
# Selberg's key lemma, fifth pass — entry point

R1 `Inner` (windowed off-diagonal integral = sum of single-term integrals, dominated
convergence); R4 `Reduce` (`offLag_bound_of_quad`, `skSplitHyp'_of_diag`, on the named,
provable per-quadruple bound `QuadOffHyp`).  See `docs/SELBERG_KEY.md` (fifth pass).
-/
import RamanujanTau.SelbergKey5.Reduce

open RamanujanTau.SelbergKey5

#print axioms quadSum_eq
#print axioms norm_Fq_le
#print axioms hasSum_Fq
#print axioms phi_offLag_eq
#print axioms hasSum_integral_fR
#print axioms integral_fR
#print axioms summable_integral_Fq
#print axioms inner_offLag_eq
#print axioms abs_inner_offLag_le
#print axioms lagInt_le_of_inner
#print axioms abs_wc_le
#print axioms abs_inner_le_of_quad
#print axioms offLag_bound_of_quad
#print axioms skSplitHyp'_of_diag
