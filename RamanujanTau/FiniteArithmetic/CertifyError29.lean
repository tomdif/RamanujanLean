import RamanujanTau.FiniteArithmetic.Cert29Error
import RamanujanTau.FiniteArithmetic.ErrorDynamics29

/-! Identify the finite precision-841 certificates with the actual p-adic
operator and its low-coefficient observation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.CertifyError29
open PowerSeries BoylanWebb AtkinOBrienFinal Error29 ErrorDynamics29 Precision29

lemma map_int_square (F : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZModPow (p := 29) 2)
      (PowerSeries.map (Int.castRingHom ℤ_[29]) F) = Ψ 841 F := by
  ext n
  simp only [coeff_map, Int.coe_castRingHom, map_intCast]
  change ((coeff n F : ℤ) : ZMod 841) = coeff n (PowerSeries.map (Int.castRingHom (ZMod 841)) F)
  rw [coeff_map]
  rfl

lemma square_obs_Y (F : PS 29) :
    PadicInt.toZModPow 2 (obs (Yop F)) =
      3 * coeff 1682 (PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Φl 29 * F)) -
        coeff 841 (PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Φl 29 * F)) := by
  rw [coeff_map, coeff_map]
  simp only [obs, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    Yop, LinearMap.comp_apply, Ulin_apply, Dlin_apply, coeff_U,
    map_sub, map_mul, map_ofNat]

lemma square_f : PadicInt.toZModPow 2 (obs (Yop fLift)) = 348 := by
  have he : PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Φl 29 * fLift) =
      Ψ 841 (Φ 29 * EintInv * Cert29.f) := by
    rw [fLift, Φl, map_mul, map_mul, map_int_square, map_int_square, map_Einv_square]
    simp only [map_mul]
    ring
  rw [square_obs_Y, he]
  exact Cert29Error.obs_YF

lemma square_g : PadicInt.toZModPow 2 (obs (Yop gLift)) = 725 := by
  have he : PowerSeries.map (PadicInt.toZModPow (p := 29) 2) (Φl 29 * gLift) =
      Ψ 841 (Φ 29 * EintInv * Cert29.g) := by
    rw [gLift, Φl, map_mul, map_mul, map_int_square, map_int_square, map_Einv_square]
    simp only [map_mul]
    ring
  rw [square_obs_Y, he]
  exact Cert29Error.obs_YG

lemma square_initial : PadicInt.toZModPow 2 (obs (Ll 29 2)) = 696 := by
  have he : Ll 29 2 = Yop 1 := by
    rw [show 2 = 2 * 0 + 2 from rfl, AllPowers29.even_U, AllPowers29.odd_D]
    change Ulin 29 (Dlin 29 (Ll 29 0)) = Yop 1
    simp [Ll, L, Yop]
  rw [he, square_obs_Y, mul_one, Φl, map_int_square]
  exact Cert29Error.obs_Phi

theorem data : Data := ⟨square_f, square_g, square_initial⟩

end RamanujanTau.FiniteArithmetic.CertifyError29
