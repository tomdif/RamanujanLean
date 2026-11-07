/-
# `QFProof/` — the reduction of `HafnerBridge.QFHyp` (see `docs/QF_PROOF.md`)

Build: `nice -n 10 lake build RamanujanTau.QFProof.Main`.

* `J_bound` (level 1): `|Σ_{m≤x}(fR(m)/m)log(x/m)| ≤ K(1+log x)^{1/2}`.
* `smooth_two` (level 1): exact two-variable Selberg-smoothing identity.
* `Q0_diag`, `Q1_diag` (level 1, on the identity hypotheses): `Q⁰ = Σ_d W y_d²`, `Q¹ = Σ_d (W₁y_d² + 2W y_d z_d)`.
* `rhoP_one`, `rhoP_add_two` (level 1): `ρ_p(1) = λ(p)/(1+1/p)`, `ρ_p(a+2) = (λ_{a+2} − λ_a/p)/(1+1/p)`.
* `chol_loc`, `chol_rhoP` (level 1): the explicit local LDLᵀ of `K_p(a,b) = p^{−max}ρ_p(|a−b|)`.
* `Q0_bound_of`, `Q1_bound_of`, `qfHyp_of` (level 2 on the named hypotheses `QDecomp`, `QDecomp1`,
  `QFactor`, `QEuler`): `QFHyp`.
-/
import RamanujanTau.QFProof.Reduction
import RamanujanTau.QFProof.LocalChol

#print axioms RamanujanTau.QFProof.J_bound
#print axioms RamanujanTau.QFProof.smooth_two
#print axioms RamanujanTau.QFProof.yv_smooth
#print axioms RamanujanTau.QFProof.Q0_diag
#print axioms RamanujanTau.QFProof.Q1_diag
#print axioms RamanujanTau.QFProof.Q0_bound_of
#print axioms RamanujanTau.QFProof.Q1_bound_of
#print axioms RamanujanTau.QFProof.qfHyp_of
#print axioms RamanujanTau.QFProof.rhoP_one
#print axioms RamanujanTau.QFProof.rhoP_add_two
#print axioms RamanujanTau.QFProof.chol_loc
#print axioms RamanujanTau.QFProof.chol_rhoP
