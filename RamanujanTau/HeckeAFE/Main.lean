/-
# Smoothed approximate functional equation for `L(Δ, s)` — entry point

See `docs/HECKE_AFE.md`.  Weight `G(u) = e^{u²}`, line integrals `(1/2πi)∫_{(c)} du = (1/2π)∫ dy`.

Level 1 (axiom-clean, unconditional):

* `heckeLambda_afe`    : `Λ(s) = I_Λ(s;X) + I_Λ(12−s;1/X)`, every `s`, `X > 0`, `c > 0`;
* `ILam_eq_tsum`       : `I_Λ(s;X) = Σ τ(n)(2πn)^{−s} W_s(2πn/X)` for `Re s + c > 7`;
* `tauL_afe`           : `L(s) = Σ τ(n)n^{−s}V_s(2πn/X) + ε(s) Σ τ(n)n^{s−12}V_{12−s}(2πnX)`, `5<Re s<7`;
* `tauL_afe_line`, `norm_eps_line` : the line `s = 6+it`, `|ε(6+it)| = 1`;
* `V_decay`, `V_sub_one`, `V_bound` : `|V_t(ξ)| ≤ C_A((1+|t|)/ξ)^A`, `|V_t(ξ)−1| ≤ C_c(ξ/(1+|t|))^c`,
  `|V_t(ξ)| ≤ C_A(1+ξ/(1+|t|))^{−A}`, all uniform in `t ∈ ℝ`, `ξ > 0`;
* `tauL_afe_truncated_unbalanced`, `tauL_afe_truncated`, `norm_tauL_le_afe` : truncation.

Statement only (not used): `SCS2` (two-sided shifted convolution hypothesis, `Hyp.lean`).
-/
import RamanujanTau.HeckeAFE.Truncate
import RamanujanTau.HeckeAFE.Hyp

-- generic contour machinery
#print axioms RamanujanTau.HeckeAFE.vline_shift
#print axioms RamanujanTau.HeckeAFE.vline_gauss_div
#print axioms RamanujanTau.HeckeAFE.vline_residue
-- the exact AFE
#print axioms RamanujanTau.HeckeAFE.heckeLambda_afe
#print axioms RamanujanTau.HeckeAFE.ILam_eq_tsum
#print axioms RamanujanTau.HeckeAFE.tauL_afe
#print axioms RamanujanTau.HeckeAFE.tauL_afe_line
#print axioms RamanujanTau.HeckeAFE.norm_eps_line
-- the weights
#print axioms RamanujanTau.HeckeAFE.WGam_shift
#print axioms RamanujanTau.HeckeAFE.WGam_residue
#print axioms RamanujanTau.HeckeAFE.norm_Gamma_ratio_line
#print axioms RamanujanTau.HeckeAFE.V_decay
#print axioms RamanujanTau.HeckeAFE.V_sub_one
#print axioms RamanujanTau.HeckeAFE.V_bound
-- truncation and corollaries
#print axioms RamanujanTau.HeckeAFE.tail_bound
#print axioms RamanujanTau.HeckeAFE.tauL_afe_truncated_unbalanced
#print axioms RamanujanTau.HeckeAFE.tauL_afe_truncated
#print axioms RamanujanTau.HeckeAFE.norm_tauL_le_afe
-- hypothesis statement (sanity)
#print axioms RamanujanTau.HeckeAFE.SCS2.mono
