import RamanujanTau.FiniteArithmetic.Error31
import RamanujanTau.FiniteArithmetic.PadicDivision

/-! A scalar law for every normalized contracting error, given three finite
precision-31² observations. No finite truncation is assumed invariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.ErrorDynamics31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Error31 AllPowers31 PadicDivision

structure Data : Prop where
  f : PadicInt.toZModPow 2 (obs (Yop fLift)) = 217
  g : PadicInt.toZModPow 2 (obs (Yop gLift)) = 651
  initial : PadicInt.toZModPow 2 (obs (Ll 31 2)) = 0

lemma thirtyOne_series : (31 : PowerSeries (ZMod 31)) = 0 := by
  rw [← map_ofNat C 31, show (31 : ZMod 31) = 0 from rfl, map_zero]

lemma reduce_decomposition (F R : PS 31) (c d : ℤ_[31])
    (h : F = c • gLift + d • fLift + (31 : ℤ_[31]) • R) :
    PowerSeries.map (PadicInt.toZMod (p := 31)) F =
      PadicInt.toZMod c • Ψ 31 Cert31.g + PadicInt.toZMod d • Ψ 31 Cert31.f := by
  rw [h]
  simp only [PowerSeries.smul_eq_C_mul, map_add, map_mul, PowerSeries.map_C,
    gLift_reduce, fLift_reduce, map_ofNat, thirtyOne_series,
    map_zero, zero_mul, add_zero]

lemma obs_decomposition (F R : PS 31) (c d : ℤ_[31])
    (h : F = c • gLift + d • fLift + (31 : ℤ_[31]) • R) :
    PadicInt.toZMod (obs F) = 29 * PadicInt.toZMod d := by
  rw [obs_reduce, reduce_decomposition F R c d h, map_add, map_smul, map_smul,
    obs_g, obs_f, smul_zero, zero_add, smul_eq_mul, mul_comm]

lemma square_observation (data : Data) (F R : PS 31) (c d : ℤ_[31])
    (hR : Env 31 (by norm_num) 2 (α 31) R)
    (h : F = c • gLift + d • fLift + (31 : ℤ_[31]) • R) :
    PadicInt.toZModPow 2 (obs (Yop F)) =
      PadicInt.toZModPow 2 ((31 : ℤ_[31]) * (21 * c + 7 * d)) := by
  have hr := (cancel_mod_square (obs (Yop R)) 0).mpr (by simpa using tail_killed R hR)
  simp only [map_mul, map_natCast, Nat.cast_ofNat, map_ofNat, mul_zero, map_zero] at hr
  rw [h]
  simp only [map_add, map_smul, smul_eq_mul, map_mul, map_ofNat, data.f, data.g]
  rw [hr, add_zero]
  have hg : (651 : ZMod 961) = 31 * 21 := by decide +kernel
  have hf : (217 : ZMod 961) = 31 * 7 := by decide +kernel
  rw [hg, hf]
  ring

lemma divided_observation (data : Data) (F G R : PS 31) (c d : ℤ_[31])
    (hR : Env 31 (by norm_num) 2 (α 31) R)
    (h : F = c • gLift + d • fLift + (31 : ℤ_[31]) • R)
    (hG : Yop F = (31 : ℤ_[31]) • G) :
    PadicInt.toZMod (obs G) = 21 * PadicInt.toZMod c + 7 * PadicInt.toZMod d := by
  have hh := square_observation data F R c d hR h
  rw [hG, map_smul, smul_eq_mul] at hh
  have h' := (cancel_mod_square (obs G) (21 * c + 7 * d)).mp hh
  simpa only [map_add, map_mul, map_ofNat] using h'

/-- The observable error is multiplied by the nonzero residue 2 at each cycle. -/
theorem divided_step (data : Data) (H E : PS 31)
    (hH : H ∈ envSub (by norm_num : 5 ≤ 31) 1 (α 31))
    (hE : Dlin 31 H = (31 : ℤ_[31]) • E) :
    PadicInt.toZMod (obs (Ulin 31 E)) = 2 * PadicInt.toZMod (obs H) := by
  obtain ⟨c, d, R, hR, he⟩ := decompose H hH
  have hY : Yop H = (31 : ℤ_[31]) • Ulin 31 E := by
    change Ulin 31 (Dlin 31 H) = _
    rw [hE, map_smul]
  rw [divided_observation data H (Ulin 31 E) R c d hR he hY,
    obs_decomposition H R c d he]
  have hz : PowerSeries.map (PadicInt.toZMod (p := 31)) (Dlin 31 H) = 0 := by
    rw [hE, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_ofNat]
    rw [map_ofNat, thirtyOne_series, zero_mul]
  rw [Image31.reduce_D, reduce_decomposition H R c d he,
    PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul] at hz
  rw [mul_add, mul_left_comm _ (C _), mul_left_comm _ (C _), U_add, U_C_mul, U_C_mul,
    Cert31.odd_step, Cert31Image.D_f] at hz
  have hc := congrArg (coeff 2) hz
  simp only [map_add, coeff_C_mul, Image31.f_coeff 2 (by decide), ite_true, mul_one,
    map_zero] at hc
  have h31 : (31 : ZMod 31) = 0 := rfl
  linear_combination 10 * hc + (-9 * PadicInt.toZMod c - 11 * PadicInt.toZMod d) * h31

end RamanujanTau.FiniteArithmetic.ErrorDynamics31
