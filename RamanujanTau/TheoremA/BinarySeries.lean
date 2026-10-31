import RamanujanTau.TheoremA.EvenWeightProducts

/-!
# Integral binary coordinates for the level-six ring

Two explicit integer series x, y satisfy x²=A, xy=B, y²=C. Their
homogeneous monomials of even degree are exactly the proved eta basis.
No odd-weight modularity statement or choice of analytic square root is
used: both series are explicit products of formal Euler-product units.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries RankProof
open EtaSquared

noncomputable def eulerUnit (j : Fin 4) : (PowerSeries ℤ)ˣ :=
  (isUnit_Pinf _ _ (dilation_pos j) (dilation_pos j)).unit

@[simp] theorem eulerUnit_coe (j : Fin 4) :
    (eulerUnit j : PowerSeries ℤ) = Pinf (dilation j) (dilation j) := IsUnit.unit_spec _

noncomputable def eulerUnitProduct (e : Fin 4 → ℤ) : (PowerSeries ℤ)ˣ :=
  ∏ j : Fin 4, eulerUnit j ^ e j

theorem eulerUnitProduct_add (e f : Fin 4 → ℤ) :
    eulerUnitProduct (e + f) = eulerUnitProduct e * eulerUnitProduct f := by
  simp [eulerUnitProduct, zpow_add, Finset.prod_mul_distrib]

theorem eulerUnitProduct_natMul (e : Fin 4 → ℤ) (n : ℕ) :
    eulerUnitProduct (fun j => (n : ℤ) * e j) = eulerUnitProduct e ^ n := by
  simp only [eulerUnitProduct, mul_comm (n : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]

lemma eulerUnitProduct_parts (e : Fin 4 → ℤ) :
    (eulerUnitProduct e : PowerSeries ℤ) * eulerPowerProduct (fun j => (-e j).toNat) =
      eulerPowerProduct (fun j => (e j).toNat) := by
  have h : eulerUnitProduct e * (∏ j : Fin 4, eulerUnit j ^ (-e j).toNat) =
      ∏ j : Fin 4, eulerUnit j ^ (e j).toNat := by
    rw [eulerUnitProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [← zpow_natCast, ← zpow_add, ← zpow_natCast]
    congr 1
    omega
  have he := congrArg (fun u : (PowerSeries ℤ)ˣ => (u : PowerSeries ℤ)) h
  simpa only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val, eulerUnit_coe,
    eulerPowerProduct] using he

theorem quotientUnitSeries_eq_eulerUnitProduct (r : Fin 4 → ℤ) :
    quotientUnitSeries r = (eulerUnitProduct (fun j => 2 * r j) : PowerSeries ℤ) := by
  apply (eulerPower_isUnit (negativeExponent r)).mul_right_cancel
  rw [quotientUnitSeries_mul]
  exact (eulerUnitProduct_parts (fun j => 2 * r j)).symm

noncomputable def binaryX : PowerSeries ℤ := eulerUnitProduct (weightTwoExponent 0)
noncomputable def binaryY : PowerSeries ℤ := X * (eulerUnitProduct (weightTwoExponent 2) : PowerSeries ℤ)

/-- Every even-degree binary monomial is the corresponding actual modular-form expansion. -/
theorem binary_monomial_even (n i : ℕ) (hi : i ≤ 2 * n) :
    binaryX ^ (2 * n - i) * binaryY ^ i = evenSeries n i := by
  have he : (fun j => ((2 * n - i : ℕ) : ℤ) * weightTwoExponent 0 j) +
      (fun j => (i : ℤ) * weightTwoExponent 2 j) = (fun j => 2 * evenExponent n i j) := by
    ext j
    simp only [Pi.add_apply, Nat.cast_sub hi, Nat.cast_mul, Nat.cast_ofNat]
    exact (evenExponent_twice n i j).symm
  have hu : eulerUnitProduct (weightTwoExponent 0) ^ (2 * n - i) *
      eulerUnitProduct (weightTwoExponent 2) ^ i =
      eulerUnitProduct (fun j => 2 * evenExponent n i j) := by
    rw [← eulerUnitProduct_natMul, ← eulerUnitProduct_natMul, ← eulerUnitProduct_add, he]
  rw [binaryX, binaryY, mul_pow]
  calc
    _ = X ^ i * ((eulerUnitProduct (weightTwoExponent 0) ^ (2 * n - i) *
        eulerUnitProduct (weightTwoExponent 2) ^ i : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    _ = _ := by rw [hu, ← quotientUnitSeries_eq_eulerUnitProduct]; rfl

theorem binaryX_sq : binaryX ^ 2 = weightTwoSeries 0 := by
  have h := binary_monomial_even 1 0 (by omega)
  simpa only [Nat.mul_one, Nat.sub_zero, pow_zero, mul_one] using h.trans (evenSeries_one 0)

theorem binaryX_mul_binaryY : binaryX * binaryY = weightTwoSeries 1 := by
  have h := binary_monomial_even 1 1 (by omega)
  simpa only [Nat.mul_one, Nat.reduceSub, pow_one] using h.trans (evenSeries_one 1)

theorem binaryY_sq : binaryY ^ 2 = weightTwoSeries 2 := by
  have h := binary_monomial_even 1 2 (by omega)
  simpa only [Nat.mul_one, Nat.sub_self, pow_zero, one_mul] using h.trans (evenSeries_one 2)

end RamanujanTau.TheoremA
