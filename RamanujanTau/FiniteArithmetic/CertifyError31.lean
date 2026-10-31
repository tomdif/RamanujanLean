import RamanujanTau.FiniteArithmetic.Cert31Error
import RamanujanTau.FiniteArithmetic.ErrorDynamics31

/-! Identify the finite precision-961 certificates with the actual p-adic
operator and its low-coefficient observation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.CertifyError31
open PowerSeries BoylanWebb AtkinOBrienFinal Error31 ErrorDynamics31 Precision31

lemma map_int_square (F : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZModPow (p := 31) 2)
      (PowerSeries.map (Int.castRingHom ℤ_[31]) F) = Ψ 961 F := by
  ext n
  simp only [coeff_map, Int.coe_castRingHom, map_intCast]
  change ((coeff n F : ℤ) : ZMod 961) = coeff n (PowerSeries.map (Int.castRingHom (ZMod 961)) F)
  rw [coeff_map]
  rfl

lemma square_obs_Y (F : PS 31) :
    PadicInt.toZModPow 2 (obs (Yop F)) =
      29 * coeff 1922 (PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Φl 31 * F)) -
        2 * coeff 961 (PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Φl 31 * F)) := by
  rw [coeff_map, coeff_map]
  simp only [obs, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    Yop, LinearMap.comp_apply, Ulin_apply, Dlin_apply, coeff_U,
    map_sub, map_mul, map_ofNat]

lemma square_f : PadicInt.toZModPow 2 (obs (Yop fLift)) = 217 := by
  have he : PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Φl 31 * fLift) =
      Ψ 961 (Φ 31 * EintInv * Cert31.f) := by
    rw [fLift, Φl, map_mul, map_mul, map_int_square, map_int_square, map_Einv_square]
    simp only [map_mul]
    ring
  rw [square_obs_Y, he]
  exact Cert31Error.obs_YF

lemma square_g : PadicInt.toZModPow 2 (obs (Yop gLift)) = 651 := by
  have he : PowerSeries.map (PadicInt.toZModPow (p := 31) 2) (Φl 31 * gLift) =
      Ψ 961 (Φ 31 * EintInv * Cert31.g) := by
    rw [gLift, Φl, map_mul, map_mul, map_int_square, map_int_square, map_Einv_square]
    simp only [map_mul]
    ring
  rw [square_obs_Y, he]
  exact Cert31Error.obs_YG

lemma square_initial : PadicInt.toZModPow 2 (obs (Ll 31 2)) = 0 := by
  have he : Ll 31 2 = Yop 1 := by
    rw [show 2 = 2 * 0 + 2 from rfl, AllPowers31.even_U, AllPowers31.odd_D]
    change Ulin 31 (Dlin 31 (Ll 31 0)) = Yop 1
    simp [Ll, L, Yop]
  rw [he, square_obs_Y, mul_one, Φl, map_int_square]
  exact Cert31Error.obs_Phi

theorem data : Data := ⟨square_f, square_g, square_initial⟩

end RamanujanTau.FiniteArithmetic.CertifyError31
