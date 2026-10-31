import RamanujanTau.FiniteArithmetic.Bernoulli30
import RamanujanTau.FiniteArithmetic.Partition31
import RamanujanTau.AtkinOBrienFinal.Katz

/-! The actual weight-30 Hasse lift at precision 31². -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.Precision31
open PowerSeries AtkinOBrienFinal

noncomputable def Eint : PowerSeries ℤ := PowerSeries.mk fun n =>
  (if n = 0 then 1 else 0) + 899 * (ArithmeticFunction.sigma 29 n : ℤ)

lemma coeff_Eint (n : ℕ) : coeff n Eint =
    (if n = 0 then 1 else 0) + 899 * (ArithmeticFunction.sigma 29 n : ℤ) := coeff_mk _ _

lemma E_scalar (n : ℕ) : (8615841276005 : ℤ_[31]) * coeff n (E 31 (by norm_num)) =
    (if n = 0 then 8615841276005 else 0) + (-859320) * (ArithmeticFunction.sigma 29 n : ℤ_[31]) := by
  have h : (8615841276005 : ℚ) * coeff n (TateCurve.Eis 30) =
      (if n = 0 then 8615841276005 else 0) + (-859320) * (ArithmeticFunction.sigma 29 n : ℚ) := by
    rw [TateCurve.coeff_Eis, TateCurve.kappa, Bernoulli30.value]
    split_ifs <;> norm_num <;> ring
  have he : ((coeff n (E 31 (by norm_num)) : ℤ_[31]) : ℚ_[31]) =
      ((coeff n (TateCurve.Eis 30) : ℚ) : ℚ_[31]) := by
    simp only [E, TateCurve.EhasseZp, coeff_mk]
  have hq := congrArg (Rat.castHom ℚ_[31]) h
  apply PadicInt.ext
  rw [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_mul, he]
  split_ifs at hq ⊢ <;> push_cast at hq ⊢ <;> exact_mod_cast hq

theorem map_E_square : PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (E 31 (by norm_num)) =
    BoylanWebb.Ψ 961 Eint := by
  ext n
  have h := congrArg (PadicInt.toZModPow (p := 31) 2) (E_scalar n)
  rw [coeff_map]
  change _ = (Int.castRingHom (ZMod 961)) (coeff n Eint)
  rw [coeff_Eint]
  have hb : (8615841276005 : ZMod 961) = 561 := by decide +kernel
  have ha : (-859320 : ZMod 961) = 775 := by decide +kernel
  have hi : (579 : ZMod 961) * 561 = 1 := by decide +kernel
  have hs : (579 : ZMod 961) * 775 = 899 := by decide +kernel
  by_cases hn : n = 0
  · subst n
    simp only [if_pos rfl, ite_true, ArithmeticFunction.map_zero, Nat.cast_zero, mul_zero, add_zero,
      map_mul, map_ofNat] at h ⊢
    rw [hb] at h
    have hh := congrArg (fun x : ZMod 961 => 579 * x) h
    dsimp only at hh
    rw [← mul_assoc, hi, one_mul] at hh
    exact hh
  · simp only [if_neg hn, map_add, map_mul, map_neg, map_natCast, map_ofNat, map_zero, zero_add,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] at h ⊢
    rw [hb, ha] at h
    have hh := congrArg (fun x : ZMod 961 => 579 * x) h
    dsimp only at hh
    rw [← mul_assoc, hi, one_mul, ← mul_assoc, hs] at hh
    exact hh

lemma Eint_unit : IsUnit Eint := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Eint]
  norm_num

noncomputable def EintInv : PowerSeries ℤ := Ring.inverse Eint

lemma Eint_mul_inv : Eint * EintInv = 1 := Ring.mul_inverse_cancel _ Eint_unit

theorem map_Einv_square : PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Einv 31 (by norm_num)) =
    BoylanWebb.Ψ 961 EintInv := by
  have h := congrArg (PowerSeries.map (PadicInt.toZModPow (p := 31) 2)) (E_mul_Einv 31 (by norm_num))
  rw [map_mul, map_one, map_E_square] at h
  have h' := congrArg (BoylanWebb.Ψ 961) Eint_mul_inv
  rw [map_mul, map_one] at h'
  calc _ = BoylanWebb.Ψ 961 EintInv * (BoylanWebb.Ψ 961 Eint *
        PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Einv 31 (by norm_num))) := by
          rw [← mul_assoc, mul_comm (BoylanWebb.Ψ 961 EintInv), h', one_mul]
    _ = _ := by rw [h, mul_one]

end RamanujanTau.FiniteArithmetic.Precision31
