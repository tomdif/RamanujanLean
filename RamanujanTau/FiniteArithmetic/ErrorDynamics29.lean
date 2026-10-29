import RamanujanTau.FiniteArithmetic.Error29
import RamanujanTau.FiniteArithmetic.PadicDivision

/-! A scalar law for every normalized contracting error, given three finite
precision-29² observations. No finite truncation is assumed invariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.ErrorDynamics29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Error29 AllPowers29 PadicDivision

structure Data : Prop where
  f : PadicInt.toZModPow 2 (obs (Yop fLift)) = 348
  g : PadicInt.toZModPow 2 (obs (Yop gLift)) = 725
  initial : PadicInt.toZModPow 2 (obs (Ll 29 2)) = 696

lemma twentyNine_series : (29 : PowerSeries (ZMod 29)) = 0 := by
  rw [← map_ofNat C 29, show (29 : ZMod 29) = 0 from rfl, map_zero]

lemma reduce_decomposition (F R : PS 29) (c d : ℤ_[29])
    (h : F = c • gLift + d • fLift + (29 : ℤ_[29]) • R) :
    PowerSeries.map (PadicInt.toZMod (p := 29)) F =
      PadicInt.toZMod c • Ψ 29 Cert29.g + PadicInt.toZMod d • Ψ 29 Cert29.f := by
  rw [h]
  simp only [PowerSeries.smul_eq_C_mul, map_add, map_mul, PowerSeries.map_C,
    gLift_reduce, fLift_reduce, map_ofNat, twentyNine_series,
    map_zero, zero_mul, add_zero]

lemma obs_decomposition (F R : PS 29) (c d : ℤ_[29])
    (h : F = c • gLift + d • fLift + (29 : ℤ_[29]) • R) :
    PadicInt.toZMod (obs F) = 3 * PadicInt.toZMod d := by
  rw [obs_reduce, reduce_decomposition F R c d h, map_add, map_smul, map_smul,
    obs_g, obs_f, smul_zero, zero_add, smul_eq_mul, mul_comm]

lemma square_observation (data : Data) (F R : PS 29) (c d : ℤ_[29])
    (hR : Env 29 (by norm_num) 2 (α 29) R)
    (h : F = c • gLift + d • fLift + (29 : ℤ_[29]) • R) :
    PadicInt.toZModPow 2 (obs (Yop F)) =
      PadicInt.toZModPow 2 ((29 : ℤ_[29]) * (25 * c + 12 * d)) := by
  have hr := (cancel_mod_square (obs (Yop R)) 0).mpr (by simpa using tail_killed R hR)
  simp only [map_mul, map_natCast, Nat.cast_ofNat, map_ofNat, mul_zero, map_zero] at hr
  rw [h]
  simp only [map_add, map_smul, smul_eq_mul, map_mul, map_ofNat, data.f, data.g]
  rw [hr, add_zero]
  have hg : (725 : ZMod 841) = 29 * 25 := by decide +kernel
  have hf : (348 : ZMod 841) = 29 * 12 := by decide +kernel
  rw [hg, hf]
  ring

lemma divided_observation (data : Data) (F G R : PS 29) (c d : ℤ_[29])
    (hR : Env 29 (by norm_num) 2 (α 29) R)
    (h : F = c • gLift + d • fLift + (29 : ℤ_[29]) • R)
    (hG : Yop F = (29 : ℤ_[29]) • G) :
    PadicInt.toZMod (obs G) = 25 * PadicInt.toZMod c + 12 * PadicInt.toZMod d := by
  have hh := square_observation data F R c d hR h
  rw [hG, map_smul, smul_eq_mul] at hh
  have h' := (cancel_mod_square (obs G) (25 * c + 12 * d)).mp hh
  simpa only [map_add, map_mul, map_ofNat] using h'

/-- The observable error is multiplied by the nonzero residue 23 at each cycle. -/
theorem divided_step (data : Data) (H E : PS 29)
    (hH : H ∈ envSub (by norm_num : 5 ≤ 29) 1 (α 29))
    (hE : Dlin 29 H = (29 : ℤ_[29]) • E) :
    PadicInt.toZMod (obs (Ulin 29 E)) = 23 * PadicInt.toZMod (obs H) := by
  obtain ⟨c, d, R, hR, he⟩ := decompose H hH
  have hY : Yop H = (29 : ℤ_[29]) • Ulin 29 E := by
    change Ulin 29 (Dlin 29 H) = _
    rw [hE, map_smul]
  rw [divided_observation data H (Ulin 29 E) R c d hR he hY,
    obs_decomposition H R c d he]
  have hz : PowerSeries.map (PadicInt.toZMod (p := 29)) (Dlin 29 H) = 0 := by
    rw [hE, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_ofNat]
    rw [map_ofNat, twentyNine_series, zero_mul]
  rw [Image29.reduce_D, reduce_decomposition H R c d he,
    PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul] at hz
  rw [mul_add, mul_left_comm _ (C _), mul_left_comm _ (C _), U_add, U_C_mul, U_C_mul,
    Cert29.odd_step, Cert29Image.D_f] at hz
  have hc := congrArg (coeff 2) hz
  simp only [map_add, coeff_C_mul, Image29.f_coeff 2 (by decide), ite_true, mul_one,
    map_zero] at hc
  linear_combination (norm := ring_nf) (18 : ZMod 29) * hc
  rw [show (29 : ZMod 29) = 0 from rfl, show (435 : ZMod 29) = 0 from rfl]
  simp

end RamanujanTau.FiniteArithmetic.ErrorDynamics29
