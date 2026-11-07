/-
# `HeckeConvex`: Rankin's absolute convergence and the convexity bound for `L(Δ,s)`

Unnormalized coordinates (weight 12, critical line `Re s = 6`).

* `LSeriesSummable_tau_of_gt_13_2`: `∑ τ(n) n^{−s}` converges absolutely for `Re s > 13/2`
  (Rankin 1939), from the unconditional Rankin–Selberg asymptotic.
* `tauL_convexity_strip`: `‖L(Δ,σ+it)‖ ≤ C_ε (1+|t|)^{13/2−σ+ε}` for `11/2 ≤ σ ≤ 13/2`.
* `tauL_convexity`: `‖L(Δ,6+it)‖ ≤ C_ε (1+|t|)^{1/2+ε}`.
-/
import RamanujanTau.HeckeConvex.Summable
import RamanujanTau.HeckeConvex.Convex

#print axioms RamanujanTau.HeckeConvex.exists_sum_abs_tau_le
#print axioms RamanujanTau.HeckeConvex.LSeriesSummable_tau_of_gt_13_2
#print axioms RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow
#print axioms RamanujanTau.HeckeConvex.tauL_eq_LSeries_of_gt
#print axioms RamanujanTau.HeckeConvex.tauL_bounded_of_gt
#print axioms RamanujanTau.HeckeConvex.fC_bound
#print axioms RamanujanTau.HeckeConvex.tauL_convexity_strip
#print axioms RamanujanTau.HeckeConvex.tauL_convexity
