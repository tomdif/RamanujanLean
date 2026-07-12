/-
# Quintuple product, stone 3 (capstone infrastructure): z-shift lemmas

The final identity `thetaA · thetaB = qfac2InfL · quintTheta` is a z-convolution of two theta series. The
general z-convolution law (infinite z-support) is the crux the repo never built — but we sidestep it: each
`thetaBTerm m = X^{(m+1)²}·C(g_m)` is localized at a *single* q-degree with *finite* z-support, so multiplying
`thetaA` by it is a finite shift-and-add, handled by stabilization.

This file provides the two foundational shifts:
* `zProj_Xpow_mul` — a pure `q`-power `X^e` commutes out of any z-projection;
* `zProj_mul_CT` — multiplying by the Laurent monomial `C(T d)` shifts the z-degree: `zProj n (A·C(T d)) = zProj (n−d) A`.
No `sorry`.
-/
import RamanujanTau.MockTheta5ZProj

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- a pure `q`-power factors out of a z-projection. -/
lemma zProj_Xpow_mul (e : ℕ) (A : PowerSeries (LaurentPolynomial ℤ)) (n : ℤ) :
    zProj n (X ^ e * A) = X ^ e * zProj n A := by
  ext k
  rw [coeff_zProj, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
      apply_ite (fun g : LaurentPolynomial ℤ => g n)]
  split_ifs with h
  · rw [coeff_zProj]
  · exact Finsupp.zero_apply

/-- multiplying by the Laurent monomial `z^d = C(T d)` shifts the z-degree down by `d`. -/
lemma zProj_mul_CT (A : PowerSeries (LaurentPolynomial ℤ)) (d n : ℤ) :
    zProj n (A * PowerSeries.C (LaurentPolynomial.T d)) = zProj (n - d) A := by
  ext k
  rw [coeff_zProj, PowerSeries.coeff_mul_C, coeff_zProj]
  have hT : (LaurentPolynomial.T d : LaurentPolynomial ℤ) = AddMonoidAlgebra.single d 1 := rfl
  rw [hT, AddMonoidAlgebra.mul_single_apply, mul_one, sub_eq_add_neg]

end MockTheta5.JTP
