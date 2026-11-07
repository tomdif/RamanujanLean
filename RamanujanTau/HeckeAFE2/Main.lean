/-
# HeckeAFE2 — `t`-derivative of the AFE weight (entry point)

See `docs/HECKE_AFE.md`, section "2026-11-06 (II)".

* `norm_digamma_diff_le` : `‖ψ(6+it+x+iy) − ψ(6+it)‖ ≤ C_x (1+|y|)²/(1+|t|)`, `x ≥ −1`;
* `hasDerivAt_Vline`, `norm_Dline_le` : differentiation under the line integral, `O(1/t)` bound;
* `V_deriv_bound` : `|∂_t V(6+it, ξ)| ≤ C_A (1+|t|)^{−1} (1+ξ/(1+|t|))^{−A}` (j = 1).
-/
import RamanujanTau.HeckeAFE2.Deriv

#print axioms RamanujanTau.HeckeAFE2.norm_digamma_sub_log_le
#print axioms RamanujanTau.HeckeAFE2.norm_digamma_diff_le
#print axioms RamanujanTau.HeckeAFE2.hasDerivAt_Phi
#print axioms RamanujanTau.HeckeAFE2.hasDerivAt_Vline
#print axioms RamanujanTau.HeckeAFE2.norm_Dline_le
#print axioms RamanujanTau.HeckeAFE2.V_deriv_bound
