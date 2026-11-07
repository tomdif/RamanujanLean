/-
# `SubconvexityCond`: t-aspect subconvexity for `L(Δ,s)` conditional on a shifted-convolution bound

Hypothesis (`Defs.lean`): `ShiftedConvolutionBound η B` —
`|∑_{n ≤ N} λ(n) λ(n+h)| ≤ C (N+h)^{1−η} h^B` for all `h ≥ 1`, `N ≥ 0`, `λ(n) = τ(n) n^{−11/2}`.

Conclusion (`Final.lean`): `tauL_subconvex_of_SCS`: for `0 < η ≤ 1`, `B ≥ 0`,
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2 − η/(10B+24)}`.  See `docs/SUBCONVEXITY_COND.md`.
-/
import RamanujanTau.SubconvexityCond.Final

#print axioms RamanujanTau.SubconvexityCond.tauL_subconvex_of_SCS
#print axioms RamanujanTau.SubconvexityCond.exists_subconvex_of_SCS
#print axioms RamanujanTau.SubconvexityCond.rpoly_bound
#print axioms RamanujanTau.SubconvexityCond.shiftedConvolutionBound_trivial
#print axioms RamanujanTau.SubconvexityCond.ShiftedConvolutionBound.mono
#print axioms RamanujanTau.SubconvexityCond.subconvexDelta_zero
#print axioms RamanujanTau.SubconvexityCond.integral_gw_cos
#print axioms RamanujanTau.SubconvexityCond.integral_gw_normSq
#print axioms RamanujanTau.SubconvexityCond.integral_gw_normSq_le
#print axioms RamanujanTau.SubconvexityCond.reindex_symm
#print axioms RamanujanTau.SubconvexityCond.offS_bound
#print axioms RamanujanTau.SubconvexityCond.sum_offS_bound
#print axioms RamanujanTau.SubconvexityCond.mean_value_bound
#print axioms RamanujanTau.SubconvexityCond.norm_rpoly_le
#print axioms RamanujanTau.SubconvexityCond.norm_sq_le_window
#print axioms RamanujanTau.SubconvexityCond.gBound_gX
#print axioms RamanujanTau.SubconvexityCond.gBound_gX_log
#print axioms RamanujanTau.SubconvexityCond.dpoly_bsm_eq
