/-
# Edge non-vanishing and the PNT for every normalized level-one Hecke eigenform

Build: `nice -n 10 lake build RamanujanTau.EigenformEdge.Main`. See `docs/EIGENFORM_EDGE.md`.

For `f ∈ S_k(SL₂(ℤ))` with `hf : IsNormalizedEigenform f` (real coefficients, `a(1) = 1`,
multiplicative, Hecke prime-power recursion — true properties of eigenforms, used as the
definition of which `f` is considered):

**Unconditional** (evidence level 1):
* `fL_ne_zero_of_gt`: `L(f,s) ≠ 0` for `Re s > (k+1)/2` (Euler product);
* `fL_ne_zero_edge_of_ne`: `L(f, (k+1)/2 + it) ≠ 0` for every `t ≠ 0`;
* `fL_real_ne_zero_of_imagAxis_nonneg`: if `f(iy) ≥ 0` for `y > 0`, then `L(f,σ) ≠ 0` for real
  `σ > 0`; `fL_discriminant_ne_zero_edge`: the Δ theorem recovered.

**Conditional on the real edge value `h0 : L(f,(k+1)/2) ≠ 0`** (level 2):
* `fL_ne_zero_edge`: `L(f, (k+1)/2 + it) ≠ 0` for all `t`;
* `fL_zeros_in_strip`: nontrivial zeros lie in `(k−1)/2 < Re s < (k+1)/2`;
* `eigen_PNT_smoothed`: `∑_p λ_f(p) log p · p^{−σ}` converges as `σ → 1⁺`.

**Conditional on `h0` and `[DeligneBoundF f]`** (level 2; Wiener–Ikehara is proved):
* `eigen_prime_sign_changes`: `a_f(p) > 0` and `a_f(p) < 0` for infinitely many primes;
* `eigen_PNT`: `∑_{p<N} a_f(p) log p = o(N^{(k+1)/2})`;
* `tau_PNT_recovered`: the Δ case, `∑_{p<N} τ(p) log p = o(N^{13/2})` (`[DeligneBound]` only).
-/
import RamanujanTau.EigenformEdge.PNTEigen

set_option autoImplicit false

#print axioms RamanujanTau.EigenformEdge.L_eulerProduct
#print axioms RamanujanTau.EigenformEdge.alpha_sq_le
#print axioms RamanujanTau.EigenformEdge.one_le_norm_Fval
#print axioms RamanujanTau.EigenformEdge.L_ne_zero_edge_of_ne
#print axioms RamanujanTau.EigenformEdge.eigenData
#print axioms RamanujanTau.EigenformEdge.fL_ne_zero_of_gt
#print axioms RamanujanTau.EigenformEdge.fL_ne_zero_edge_of_ne
#print axioms RamanujanTau.EigenformEdge.fL_ne_zero_edge
#print axioms RamanujanTau.EigenformEdge.fL_ne_zero_of_ge
#print axioms RamanujanTau.EigenformEdge.fL_ne_zero_of_le
#print axioms RamanujanTau.EigenformEdge.fL_zeros_in_strip
#print axioms RamanujanTau.EigenformEdge.fL_real_ne_zero_of_imagAxis_nonneg
#print axioms RamanujanTau.EigenformEdge.isNormalizedEigenform_discriminant
#print axioms RamanujanTau.EigenformEdge.fL_discriminant_ne_zero_edge
#print axioms RamanujanTau.EigenformEdge.primeSum_tendsto
#print axioms RamanujanTau.EigenformEdge.lam_prime_sign_changes
#print axioms RamanujanTau.EigenformEdge.lam_PNT
#print axioms RamanujanTau.EigenformEdge.eigen_PNT_smoothed
#print axioms RamanujanTau.EigenformEdge.eigen_negLogDeriv_continuousOn
#print axioms RamanujanTau.EigenformEdge.eigen_prime_sign_changes
#print axioms RamanujanTau.EigenformEdge.eigen_PNT_lam
#print axioms RamanujanTau.EigenformEdge.eigen_PNT
#print axioms RamanujanTau.EigenformEdge.tau_PNT_recovered
