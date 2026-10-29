import RamanujanTau.FiniteArithmetic.Bernoulli28
import RamanujanTau.FiniteArithmetic.Partition29
import RamanujanTau.AtkinOBrienFinal.Katz

/-! The actual weight-28 Hasse lift at precision 29². -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.Precision29
open PowerSeries AtkinOBrienFinal

noncomputable def Eint : PowerSeries ℤ := PowerSeries.mk fun n =>
  (if n = 0 then 1 else 0) + 783 * (ArithmeticFunction.sigma 27 n : ℤ)

lemma coeff_Eint (n : ℕ) : coeff n Eint =
    (if n = 0 then 1 else 0) + 783 * (ArithmeticFunction.sigma 27 n : ℤ) := coeff_mk _ _

lemma E_scalar (n : ℕ) : (23749461029 : ℤ_[29]) * coeff n (E 29 (by norm_num)) =
    (if n = 0 then 23749461029 else 0) + 48720 * (ArithmeticFunction.sigma 27 n : ℤ_[29]) := by
  have h : (23749461029 : ℚ) * coeff n (TateCurve.Eis 28) =
      (if n = 0 then 23749461029 else 0) + 48720 * (ArithmeticFunction.sigma 27 n : ℚ) := by
    rw [TateCurve.coeff_Eis, TateCurve.kappa, Bernoulli28.value]
    split_ifs <;> norm_num <;> ring
  have he : ((coeff n (E 29 (by norm_num)) : ℤ_[29]) : ℚ_[29]) =
      ((coeff n (TateCurve.Eis 28) : ℚ) : ℚ_[29]) := by
    simp only [E, TateCurve.EhasseZp, coeff_mk]
  have hq := congrArg (Rat.castHom ℚ_[29]) h
  apply PadicInt.ext
  rw [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_mul, he]
  split_ifs at hq ⊢ <;> push_cast at hq ⊢ <;> exact_mod_cast hq

theorem map_E_square : PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (E 29 (by norm_num)) =
    BoylanWebb.Ψ 841 Eint := by
  ext n
  have h := congrArg (PadicInt.toZModPow (p := 29) 2) (E_scalar n)
  rw [coeff_map]
  change _ = (Int.castRingHom (ZMod 841)) (coeff n Eint)
  rw [coeff_Eint]
  have hb : (23749461029 : ZMod 841) = 320 := by decide +kernel
  have ha : (48720 : ZMod 841) = 783 := by decide +kernel
  have hi : (523 : ZMod 841) * 320 = 1 := by decide +kernel
  have hs : (523 : ZMod 841) * 783 = 783 := by decide +kernel
  by_cases hn : n = 0
  · subst n
    simp only [if_pos rfl, ite_true, ArithmeticFunction.map_zero, Nat.cast_zero, mul_zero, add_zero,
      map_mul, map_ofNat] at h ⊢
    rw [hb] at h
    have hh := congrArg (fun x : ZMod 841 => 523 * x) h
    dsimp only at hh
    rw [← mul_assoc, hi, one_mul] at hh
    exact hh
  · simp only [if_neg hn, map_add, map_mul, map_natCast, map_ofNat, map_zero, zero_add,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] at h ⊢
    rw [hb, ha] at h
    have hh := congrArg (fun x : ZMod 841 => 523 * x) h
    dsimp only at hh
    rw [← mul_assoc, hi, one_mul, ← mul_assoc, hs] at hh
    exact hh

lemma Eint_unit : IsUnit Eint := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Eint]
  norm_num

noncomputable def EintInv : PowerSeries ℤ := Ring.inverse Eint

lemma Eint_mul_inv : Eint * EintInv = 1 := Ring.mul_inverse_cancel _ Eint_unit

theorem map_Einv_square : PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Einv 29 (by norm_num)) =
    BoylanWebb.Ψ 841 EintInv := by
  have h := congrArg (PowerSeries.map (PadicInt.toZModPow (p := 29) 2)) (E_mul_Einv 29 (by norm_num))
  rw [map_mul, map_one, map_E_square] at h
  have h' := congrArg (BoylanWebb.Ψ 841) Eint_mul_inv
  rw [map_mul, map_one] at h'
  calc _ = BoylanWebb.Ψ 841 EintInv * (BoylanWebb.Ψ 841 Eint *
        PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Einv 29 (by norm_num))) := by
          rw [← mul_assoc, mul_comm (BoylanWebb.Ψ 841 EintInv), h', one_mul]
    _ = _ := by rw [h, mul_one]

end RamanujanTau.FiniteArithmetic.Precision29
