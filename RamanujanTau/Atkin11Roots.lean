/-
# Constant coefficient of a polynomial with enough distinct roots

Over an integral domain, if `deg R ≤ n` and `R` has `n` distinct roots `r₀, …, r_{n−1}`, then
`R = lc·∏(X − r_k)`. In particular `R(0) = R_n · ∏(−r_k)`. This is used for the norm of `φ` over its
eleven conjugates.
-/
import Mathlib

set_option autoImplicit false

namespace Atkin11Roots
open Polynomial Finset

variable {K : Type*} [CommRing K] [IsDomain K]

theorem coeff_zero_of_roots {n : ℕ} (hn : 1 ≤ n) (R : K[X]) (hdeg : R.natDegree ≤ n) (r : Fin n → K)
    (hr : Function.Injective r) (hroot : ∀ k, R.eval (r k) = 0) :
    R.coeff 0 = R.coeff n * ∏ k, (-r k) := by
  set S : K[X] := ∏ k, (X - C (r k)) with hSdef
  have hmon : ∀ k ∈ (univ : Finset (Fin n)), (X - C (r k)).Monic := fun k _ => monic_X_sub_C (r k)
  have hSm : S.Monic := monic_prod_of_monic _ _ hmon
  have hSdeg : S.natDegree = n := by
    rw [hSdef, natDegree_prod_of_monic _ _ hmon]; simp
  set D : K[X] := R - C (R.coeff n) * S with hDdef
  have hDdeg : D.natDegree < n := by
    have : D.natDegree ≤ n - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hDdef, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge n N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (p := R) (n := N) (lt_of_le_of_lt hdeg h),
          coeff_eq_zero_of_natDegree_lt (p := S) (n := N) (by rw [hSdeg]; exact h), mul_zero, sub_zero]
      · have hNn : N = n := by omega
        subst hNn
        rw [← hSdeg, hSm.coeff_natDegree, hSdeg, mul_one, sub_self]
    omega
  have hD0 : D = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero D hr (fun k => ?_) (by simpa using hDdeg)
    rw [hDdef, eval_sub, eval_mul, eval_C, hroot k, hSdef, eval_prod,
      prod_eq_zero (mem_univ k) (by simp), mul_zero, sub_zero]
  have h0 := congrArg (fun p : K[X] => p.coeff 0) hD0
  simp only [hDdef, coeff_sub, coeff_C_mul, coeff_zero, sub_eq_zero] at h0
  rw [h0, coeff_zero_eq_eval_zero, hSdef, eval_prod]
  simp

end Atkin11Roots
