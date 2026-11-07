import RamanujanTau.AtkinOBrienFinal.Katz
import RamanujanTau.FiniteArithmetic.PadicDivision

/-! The Hasse denominator at precision p², uniformly in the prime.
This identifies the denominator used by the exact reconstruction at 607. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open PowerSeries AtkinOBrienFinal
variable {p : ℕ} [Fact p.Prime]

lemma padicNorm_kappa_add_two_p (hp : 3 ≤ p) :
    padicNorm p (TateCurve.kappa (p-1)+2*(p : ℚ)) ≤ ((p : ℚ)⁻¹)^2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hB0 := TateCurve.bernoulli_sub_one_ne_zero (p := p) hp
  have hB := TateCurve.padicNorm_p_mul_bernoulli_eq_one (p := p) hp
  have hplus := TateCurve.padicNorm_p_mul_bernoulli_add_one (p := p) hp
  have hsub : padicNorm p (((p : ℚ)*bernoulli (p-1)+1)-p) ≤ (p : ℚ)⁻¹ := by
    rw [sub_eq_add_neg]
    exact padicNorm.nonarchimedean.trans (max_le hplus (by
      rw [padicNorm.neg,padicNorm.padicNorm_p_of_prime]))
  have h2 : padicNorm p (2 : ℚ)=1 := by
    change padicNorm p ((2 : ℕ) : ℚ) = 1
    rw [padicNorm.nat_eq_one_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have he : TateCurve.kappa (p-1)+2*(p : ℚ) =
      2*(p : ℚ)*(((p : ℚ)*bernoulli (p-1)+1)-p)/((p : ℚ)*bernoulli (p-1)) := by
    rw [TateCurve.kappa,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    field_simp
    <;> ring
  rw [he,padicNorm.div,padicNorm.mul,padicNorm.mul,h2,hB,
    padicNorm.padicNorm_p_of_prime,one_mul,div_one]
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ (p : ℚ)⁻¹)

noncomputable def sigmaSeriesSquare (p : ℕ) : PowerSeries (ZMod (p^2)) :=
  PowerSeries.mk fun n => (ArithmeticFunction.sigma (p-2) n : ZMod (p^2))

/-- The full Hasse series modulo p² is 1 - 2p times its divisor-sum series. -/
theorem map_E_square_general (hp : 5 ≤ p) :
    PowerSeries.map (PadicInt.toZModPow (p := p) 2) (E p hp) =
      1-C (2*(p : ZMod (p^2)))*sigmaSeriesSquare p := by
  ext n
  let a : ℤ_[p] := (if n=0 then 1 else 0)-2*p*(ArithmeticFunction.sigma (p-2) n : ℤ_[p])
  have hval : ((coeff n (E p hp)-a : ℤ_[p]) : ℚ_[p]) =
      (((TateCurve.kappa (p-1)+2*(p : ℚ))*(ArithmeticFunction.sigma (p-2) n : ℚ) : ℚ) : ℚ_[p]) := by
    simp only [E,TateCurve.EhasseZp,coeff_mk,PadicInt.coe_sub]
    change ((coeff n (TateCurve.Eis (p-1)) : ℚ) : ℚ_[p])-(a : ℚ_[p]) = _
    rw [TateCurve.coeff_Eis]
    dsimp [a]
    simp only [Nat.sub_sub,Nat.reduceAdd]
    have htwo : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := rfl
    split_ifs <;> push_cast <;> simp only [htwo] <;> ring
  have hnorm : ‖coeff n (E p hp)-a‖ ≤ (p : ℝ)^(-(2 : ℤ)) := by
    rw [PadicInt.norm_def,hval,Padic.eq_padicNorm]
    have hq : padicNorm p ((TateCurve.kappa (p-1)+2*(p : ℚ))*
        (ArithmeticFunction.sigma (p-2) n : ℚ)) ≤ ((p : ℚ)⁻¹)^2 := by
      rw [padicNorm.mul]
      exact (mul_le_of_le_one_right (padicNorm.nonneg _) (TateCurve.padicNorm_natCast_le _)).trans
        (padicNorm_kappa_add_two_p (by omega))
    have hR := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hR
    simpa only [zpow_neg,zpow_ofNat,inv_pow] using hR
  have hd : (p : ℤ_[p])^2 ∣ coeff n (E p hp)-a := by
    rw [← Ideal.mem_span_singleton]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ 2).mp hnorm
  have hmap := (PadicDivision.mod_pow_eq_iff_dvd 2 (coeff n (E p hp)) a).mpr hd
  rw [coeff_map, hmap]
  simp only [map_sub,coeff_one,coeff_C_mul]
  simp only [a,map_sub,map_mul,map_natCast,map_ofNat,
    sigmaSeriesSquare,coeff_mk]
  split_ifs <;> simp

/-- The denominator inverse squared used by finite reconstruction is exact at p². -/
theorem map_Einv_square_squared_general (hp : 5 ≤ p) :
    (PowerSeries.map (PadicInt.toZModPow (p := p) 2) (Einv p hp))^2 =
      1+C (4*(p : ZMod (p^2)))*sigmaSeriesSquare p := by
  let z := C (p : ZMod (p^2))*sigmaSeriesSquare p
  have hz : z^2=0 := by
    dsimp [z]
    rw [mul_pow,← map_pow,← Nat.cast_pow,ZMod.natCast_self,map_zero,zero_mul]
  have he : PowerSeries.map (PadicInt.toZModPow (p := p) 2) (E p hp)=1-2*z := by
    rw [map_E_square_general hp]
    dsimp [z]
    simp only [map_mul,map_ofNat]
    ring
  have hprod : (1-2*z)*(1+2*z)=1 := by linear_combination -4*hz
  have h := congrArg (PowerSeries.map (PadicInt.toZModPow (p := p) 2)) (E_mul_Einv p hp)
  rw [map_mul,map_one,he] at h
  have hinv : PowerSeries.map (PadicInt.toZModPow (p := p) 2) (Einv p hp)=1+2*z := by
    calc
      _ = (1+2*z)*((1-2*z)*PowerSeries.map (PadicInt.toZModPow (p := p) 2) (Einv p hp)) := by
        rw [← mul_assoc,mul_comm (1+2*z),hprod,one_mul]
      _ = _ := by rw [h,mul_one]
  rw [hinv]
  change (1+2*z)^2 = 1+C (4*(p : ZMod (p^2)))*sigmaSeriesSquare p
  have ht : C (4*(p : ZMod (p^2)))*sigmaSeriesSquare p=4*z := by
    dsimp [z]; simp only [map_mul,map_ofNat]; ring
  rw [ht]
  linear_combination 4*hz

end RamanujanTau.FiniteArithmetic
