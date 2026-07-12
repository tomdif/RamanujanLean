/-
# Quintuple product, stone 3 (capstone): the per-term shift formula

Using the z-shift lemmas, each `thetaA · thetaBTerm m` is a finite shift-and-add of `thetaA`:

  `zProj N (thetaA · thetaBTerm m) = q^{(m+1)²} · (−1)^{m+1} · (zProj (N−2(m+1)) thetaA + zProj (N+2(m+1)) thetaA)`.

This is the structural heart of the final identity `thetaA·thetaB = qfac2InfL·quintTheta`: summed over `m`
(stabilizing, since `thetaBTerm m` lives at q-degree `(m+1)²`), the right side becomes the pentagonal-type
theta-A sum that collapses to `(q²;q²)_∞ · [quintTheta coeff]` by Euler's pentagonal theorem. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintConv
import RamanujanTau.MockTheta5QuintBrackets
import RamanujanTau.MockTheta5QuintBracket1

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- multiplying by a Laurent monomial `C(single d c) = c·z^d` shifts the z-degree and scales. -/
lemma zProj_mul_C_single (A : PowerSeries (LaurentPolynomial ℤ)) (d c n : ℤ) :
    zProj n (A * PowerSeries.C (AddMonoidAlgebra.single d c)) = PowerSeries.C c * zProj (n - d) A := by
  ext k
  rw [coeff_zProj, PowerSeries.coeff_mul_C, AddMonoidAlgebra.mul_single_apply,
      PowerSeries.coeff_C_mul, coeff_zProj, sub_eq_add_neg, mul_comm]

/-- **the per-term shift formula.** -/
lemma zProj_thetaA_mul_thetaBTerm (m : ℕ) (N : ℤ) :
    zProj N (thetaA * thetaBTerm m)
      = X ^ ((m + 1) ^ 2) * (PowerSeries.C ((-1 : ℤ) ^ (m + 1))
          * (zProj (N - 2 * ((m : ℤ) + 1)) thetaA + zProj (N + 2 * ((m : ℤ) + 1)) thetaA)) := by
  have hg : (LaurentPolynomial.C ((-1 : ℤ) ^ (m + 1))
        * (LaurentPolynomial.T (2 * ((m : ℤ) + 1)) + LaurentPolynomial.T (-(2 * ((m : ℤ) + 1)))) :
        LaurentPolynomial ℤ)
      = AddMonoidAlgebra.single (2 * ((m : ℤ) + 1)) ((-1 : ℤ) ^ (m + 1))
        + AddMonoidAlgebra.single (-(2 * ((m : ℤ) + 1))) ((-1 : ℤ) ^ (m + 1)) := by
    rw [mul_add, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
  rw [thetaBTerm, hg, map_add,
      show thetaA * (X ^ ((m + 1) ^ 2)
            * (PowerSeries.C (AddMonoidAlgebra.single (2 * ((m : ℤ) + 1)) ((-1 : ℤ) ^ (m + 1)))
              + PowerSeries.C (AddMonoidAlgebra.single (-(2 * ((m : ℤ) + 1))) ((-1 : ℤ) ^ (m + 1)))))
        = X ^ ((m + 1) ^ 2)
            * (thetaA * PowerSeries.C (AddMonoidAlgebra.single (2 * ((m : ℤ) + 1)) ((-1 : ℤ) ^ (m + 1)))
              + thetaA * PowerSeries.C (AddMonoidAlgebra.single (-(2 * ((m : ℤ) + 1))) ((-1 : ℤ) ^ (m + 1))))
        from by ring,
      zProj_Xpow_mul, zProj_add, zProj_mul_C_single, zProj_mul_C_single, sub_neg_eq_add]
  ring

end MockTheta5.JTP
