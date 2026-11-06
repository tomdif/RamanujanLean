/-
# `SubconvexGeneral2/Tau*`: Tauberian + unsmoothing + Abel half of the weight-`k` sharp SCS

`scsf_of_pointwise`: for `f ∈ S_k(SL₂(ℤ))`, `k ≥ 12`, real coefficients, the weight-`k` pointwise
bound `‖G^f_h(σ+iv)‖ ≤ K √h (|2v/σ|+3) σ^{−k+12/125}` (analogue of `SCSSharp.pointwise_G'`)
implies `SCS_f(1/22, 1/2)`.

Files: `TauBasic` (coefficients, Rankin short sums), `TauRiesz` (Riesz formula + `RmeanT_bound`),
`TauAsum` (unsmoothing), `TauFinal` (Cauchy–Schwarz, Abel summation, headline).
-/
import RamanujanTau.SubconvexGeneral2.TauFinal

#print axioms RamanujanTau.SubconvexGeneral2.scsf_of_pointwise
#print axioms RamanujanTau.SubconvexGeneral2.shS_bound_of_pointwise
#print axioms RamanujanTau.SubconvexGeneral2.AsumT_bound_large
#print axioms RamanujanTau.SubconvexGeneral2.AsumT_cs
#print axioms RamanujanTau.SubconvexGeneral2.RmeanT_bound
#print axioms RamanujanTau.SubconvexGeneral2.laplace_rieszT
#print axioms RamanujanTau.SubconvexGeneral2.rankin_shortT
