/-
# `HeckeConvexGeneral`: Hecke theory and the convexity bound for every `f ∈ S_k(SL₂(ℤ))`

Unnormalized coordinates (weight `k`, critical line `Re s = k/2`).

* `exists_sum_norm_coef_le`: `∑_{n≤N} |a_f(n)| ≤ A N^{(k+1)/2}` (Rankin), `k ≥ 1`;
  `LSeriesSummable_coef`: absolute convergence for `Re s > (k+1)/2`.
* `heckeLambda_entire`, `heckeLambda_functional_equation` (`Λ(f,k−s) = i^k Λ(f,s)`),
  `heckeLambda_eq` (`Λ(f,s) = (2π)^{−s}Γ(s)L(f,s)` for `Re s > (k+1)/2`).
* `fL_convexity_strip`, `fL_convexity`: `‖L(f,k/2+it)‖ ≤ C_ε (1+|t|)^{1/2+ε}`.

Build: `nice -n 10 lake build RamanujanTau.HeckeConvexGeneral.Main`.
-/
import RamanujanTau.HeckeConvexGeneral.Convex
import RamanujanTau.HeckeL.Basic

set_option autoImplicit false

namespace RamanujanTau.HeckeConvexGeneral

open scoped MatrixGroups

/-- **Consistency with `Δ`:** the general coefficients of `Δ` are Ramanujan's `τ(n)`. -/
lemma coef_discriminant (n : ℕ) :
    coef (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n = tauC n :=
  RamanujanTau.heckeData.coeff_discriminant n

end RamanujanTau.HeckeConvexGeneral

#print axioms RamanujanTau.HeckeConvexGeneral.exists_sum_norm_coef_le
#print axioms RamanujanTau.HeckeConvexGeneral.LSeriesSummable_coef
#print axioms RamanujanTau.HeckeConvexGeneral.summable_norm_coef_div_rpow
#print axioms RamanujanTau.HeckeConvexGeneral.heckeLambda_entire
#print axioms RamanujanTau.HeckeConvexGeneral.heckeLambda_functional_equation
#print axioms RamanujanTau.HeckeConvexGeneral.heckeLambda_eq
#print axioms RamanujanTau.HeckeConvexGeneral.heckeLambda_bdd_strip
#print axioms RamanujanTau.HeckeConvexGeneral.fL_entire
#print axioms RamanujanTau.HeckeConvexGeneral.fL_eq_LSeries
#print axioms RamanujanTau.HeckeConvexGeneral.fL_functional_equation
#print axioms RamanujanTau.HeckeConvexGeneral.fL_bounded_of_gt
#print axioms RamanujanTau.HeckeConvexGeneral.fC_bound
#print axioms RamanujanTau.HeckeConvexGeneral.fL_convexity_strip
#print axioms RamanujanTau.HeckeConvexGeneral.fL_convexity
#print axioms RamanujanTau.HeckeConvexGeneral.fL_convexity_and_continuation
#print axioms RamanujanTau.HeckeConvexGeneral.coef_discriminant
