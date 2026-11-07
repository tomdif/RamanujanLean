import RamanujanTau.TheoremA.WeightTwoQExpansion

/-!
# Integral q-expansions of certified eta quotients

For any exponent vector with nonnegative order at infinity, the certified
eta quotient has an integral formal expansion q^s times a unit with constant
term one. Negative Euler-product exponents are handled by inversion of
formal units, after an analytic multiplication identity.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm Realize PowerSeries RankProof
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

lemma realizes_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (F : ι → PowerSeries ℤ) (h : ∀ i ∈ s, Realizes (f i) (F i)) :
    Realizes (fun z => ∏ i ∈ s, f i z) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realizes_const 1
  | insert i s hi ih =>
    simpa [hi] using (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

noncomputable def eulerPowerProduct (e : Fin 4 → ℕ) : PowerSeries ℤ :=
  ∏ j : Fin 4, Pinf (dilation j) (dilation j) ^ e j

noncomputable def eulerPowerFunction (e : Fin 4 → ℕ) (q : ℂ) : ℂ :=
  ∏ j : Fin 4, Pfun (dilation j) (dilation j) q ^ e j

lemma eulerPower_realizes (e : Fin 4 → ℕ) :
    Realizes (eulerPowerFunction e) (eulerPowerProduct e) :=
  realizes_finsetProd Finset.univ _ _ (fun j _ =>
    (realizes_Pinf _ _ (dilation_pos j) (dilation_pos j)).pow (e j))

lemma Pinf_constantCoeff (d : ℕ) (hd : 0 < d) : constantCoeff (Pinf d d) = 1 := by
  have h := (X_pow_dvd_iff.mp (X_pow_dvd_Pinf_sub d d hd hd 0)) 0 (by omega)
  simpa [Pfin, coeff_zero_eq_constantCoeff_apply] using sub_eq_zero.mp h

lemma eulerPower_constantCoeff (e : Fin 4 → ℕ) : constantCoeff (eulerPowerProduct e) = 1 := by
  simp [eulerPowerProduct, Pinf_constantCoeff _ (dilation_pos _)]

lemma eulerPower_isUnit (e : Fin 4 → ℕ) : IsUnit (eulerPowerProduct e) := by
  rw [isUnit_iff_constantCoeff, eulerPower_constantCoeff]
  exact isUnit_one

def positiveExponent (r : Fin 4 → ℤ) (j : Fin 4) : ℕ := (2 * r j).toNat
def negativeExponent (r : Fin 4 → ℤ) (j : Fin 4) : ℕ := (-(2 * r j)).toNat

noncomputable def quotientUnitSeries (r : Fin 4 → ℤ) : PowerSeries ℤ :=
  eulerPowerProduct (positiveExponent r) * Ring.inverse (eulerPowerProduct (negativeExponent r))

noncomputable def quotientSeries (r : Fin 4 → ℤ) (s : ℕ) : PowerSeries ℤ :=
  X ^ s * quotientUnitSeries r

lemma quotientUnitSeries_mul (r : Fin 4 → ℤ) :
    quotientUnitSeries r * eulerPowerProduct (negativeExponent r) =
      eulerPowerProduct (positiveExponent r) := by
  rw [quotientUnitSeries, mul_assoc, Ring.inverse_mul_cancel _ (eulerPower_isUnit _), mul_one]

lemma quotientUnitSeries_constantCoeff (r : Fin 4 → ℤ) :
    constantCoeff (quotientUnitSeries r) = 1 := by
  have h := congrArg constantCoeff (quotientUnitSeries_mul r)
  simpa only [map_mul, eulerPower_constantCoeff, mul_one] using h

lemma quotientSeries_mul (r : Fin 4 → ℤ) (s : ℕ) :
    quotientSeries r s * eulerPowerProduct (negativeExponent r) =
      X ^ s * eulerPowerProduct (positiveExponent r) := by
  rw [quotientSeries, mul_assoc, quotientUnitSeries_mul]

lemma quotientSeries_coeff_lt (r : Fin 4 → ℤ) (s n : ℕ) (h : n < s) :
    (quotientSeries r s).coeff n = 0 :=
  X_pow_dvd_iff.mp ⟨quotientUnitSeries r, rfl⟩ n h

lemma quotientSeries_coeff_self (r : Fin 4 → ℤ) (s : ℕ) :
    (quotientSeries r s).coeff s = 1 := by
  simpa only [quotientSeries, zero_add, coeff_zero_eq_constantCoeff_apply,
    quotientUnitSeries_constantCoeff] using coeff_X_pow_mul (quotientUnitSeries r) s 0

lemma zpow_mul_negativePart (z : ℂ) (hz : z ≠ 0) (e : ℤ) :
    z ^ e * z ^ (-e).toNat = z ^ e.toNat := by
  rw [← zpow_natCast, ← zpow_add₀ hz, ← zpow_natCast]
  congr 1
  omega

lemma quotientFunction_qProduct_relation (r : Fin 4 → ℤ) (s : ℕ)
    (hs : ∑ j : Fin 4, (dilation j : ℤ) * r j = 12 * (s : ℤ)) (z : ℍ) :
    quotientFunction r z * eulerPowerFunction (negativeExponent r) (𝕢 1 z) =
      𝕢 1 z ^ s * eulerPowerFunction (positiveExponent r) (𝕢 1 z) := by
  rw [quotientFunction_qProduct r s hs, mul_assoc]
  congr 1
  simp only [eulerPowerFunction, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact zpow_mul_negativePart _ (Pfun_qParam_ne_zero _ (dilation_pos j) z) _

/-- The entire expansion, not merely a finite list of its coefficients. -/
theorem qExpansion_quotientModularForm (r : Fin 4 → ℤ) {k : ℤ} (s : ℕ)
    (hk : ∑ j, r j = k) (hp : PhaseCertificate r) (hc : CuspCertificate r)
    (hs : ∑ j : Fin 4, (dilation j : ℤ) * r j = 12 * (s : ℤ)) :
    qExpansion 1 (quotientModularForm r hk hp hc) =
      PowerSeries.map (Int.castRingHom ℂ) (quotientSeries r s) := by
  let f := quotientModularForm r hk hp hc
  have hf : (f : ℍ → ℂ) * qLift (eulerPowerFunction (negativeExponent r)) =
      qLift (fun q => q ^ s * eulerPowerFunction (positiveExponent r) q) :=
    funext (quotientFunction_qProduct_relation r s hs)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f
    (one_pos : (0 : ℝ) < 1) (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
  have hn := (realizes_X.pow s).mul (eulerPower_realizes (positiveExponent r))
  have hd := eulerPower_realizes (negativeExponent r)
  have hq := congrArg (qExpansion 1) hf
  rw [qExpansion_mul ha (qLift_analytic hd), qExpansion_qLift hd, qExpansion_qLift hn] at hq
  apply ((eulerPower_isUnit (negativeExponent r)).map
    (PowerSeries.map (Int.castRingHom ℂ))).mul_right_cancel
  rw [← map_mul, quotientSeries_mul]
  exact hq

end RamanujanTau.TheoremA.EtaSquared
