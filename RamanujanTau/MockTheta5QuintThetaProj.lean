/-
# Quintuple product, stone 3 (capstone): the `quintTheta`-side projections

`zProj κ` of the pieces of `quintTheta = quintBase + Σ_m quintTermP m`. Each Laurent monomial `C(T p)`
projects to `if p = κ then 1 else 0`; `quintTermP m` carries four such (at z-degrees `−3m−3, 3m+2, 3m+3,
−3m−4`). These feed the final matching `zProj N (quintTheta)` against the pentagonal collapse. No `sorry`.
-/
import RamanujanTau.MockTheta5QuintConv
import RamanujanTau.MockTheta5QuintTheta

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- `zProj κ` is additive over subtraction. -/
lemma zProj_sub (n : ℤ) (a b : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (a - b) = zProj n a - zProj n b := by
  ext m
  rw [coeff_zProj, map_sub, map_sub, coeff_zProj, coeff_zProj]
  exact Finsupp.sub_apply _ _ _

/-- the projection of a constant series `C g` is the constant `g κ`. -/
lemma zProj_C (g : LaurentPolynomial ℤ) (κ : ℤ) :
    zProj κ (PowerSeries.C g) = PowerSeries.C (g κ) := by
  ext k
  rw [coeff_zProj, PowerSeries.coeff_C, PowerSeries.coeff_C,
      apply_ite (fun h : LaurentPolynomial ℤ => h κ)]
  split_ifs with hk
  · rfl
  · exact Finsupp.zero_apply

/-- the projection of a single Laurent monomial `z^p = C(T p)`. -/
lemma zProj_C_T (p κ : ℤ) :
    zProj κ (PowerSeries.C (LaurentPolynomial.T p)) = if p = κ then 1 else 0 := by
  rw [zProj_C, LaurentPolynomial.T_apply, apply_ite (PowerSeries.C : ℤ → PowerSeries ℤ), map_one,
      map_zero]

/-- the four-monomial projection of `quintTermP m`. -/
lemma zProj_quintTermP (m : ℕ) (κ : ℤ) :
    zProj κ (quintTermP m)
      = ((if -3 * (m : ℤ) - 3 = κ then X ^ ((m + 1) * (3 * m + 2) / 2) else 0)
          - (if 3 * (m : ℤ) + 2 = κ then X ^ ((m + 1) * (3 * m + 2) / 2) else 0))
        + ((if 3 * (m : ℤ) + 3 = κ then X ^ ((m + 1) * (3 * m + 4) / 2) else 0)
          - (if -3 * (m : ℤ) - 4 = κ then X ^ ((m + 1) * (3 * m + 4) / 2) else 0)) := by
  rw [quintTermP, zProj_add, zProj_Xpow_mul, zProj_Xpow_mul, zProj_sub, zProj_sub,
      zProj_C_T, zProj_C_T, zProj_C_T, zProj_C_T]
  simp only [mul_sub, mul_ite, mul_one, mul_zero]

/-- the projection of the `n=0` base term `1 − z⁻¹`. -/
lemma zProj_quintBase (κ : ℤ) :
    zProj κ quintBase = (if (0 : ℤ) = κ then 1 else 0) - (if (-1 : ℤ) = κ then 1 else 0) := by
  rw [quintBase, zProj_sub, zProj_C_T, zProj_C_T]

end MockTheta5.JTP
