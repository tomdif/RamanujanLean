/-
# Selberg's key lemma, second pass — entry point

M1(a) `Cont`: joint continuity of `DiagLag` (removes the regularity clause of `SKSplitHyp`).
M1(b) `WBound`: uniform bounds for the lag weight `W̃_{u,u'}(ξ)` (shift, residue, decay, `≈ 1`).
See `docs/SELBERG_KEY.md` (2026-11-06, second section).
-/
import RamanujanTau.SelbergKey2.WBound

open RamanujanTau.SelbergKey2

#print axioms continuous_W2sh_line
#print axioms continuous_sTerm
#print axioms norm_sTerm_le
#print axioms continuous_diagS
#print axioms continuous_Ush
#print axioms continuous_DiagLag
#print axioms splitHyp_of_splitHyp'
#print axioms tauL_positive_proportion_of_QF_split'
#print axioms W2sh_shift
#print axioms W2sh_residue
#print axioms W2sh_line_bound
#print axioms Wsh_decay
#print axioms Wsh_sub_one
#print axioms Wsh_bound
