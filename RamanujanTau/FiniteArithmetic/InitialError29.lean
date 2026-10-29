import RamanujanTau.FiniteArithmetic.ErrorDynamics29

/-! Initialize the scalar error law from the actual partition orbit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.InitialError29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Error29 AllPowers29 ErrorDynamics29 PadicDivision

lemma L2_mem : Ll 29 2 ∈ envSub (by norm_num : 5 ≤ 29) 1 (α 29) := by
  refine ⟨?_, ?_⟩
  · rw [show 2 = 2 * 0 + 2 from rfl, even_U]
    change coeff 0 (U 29 (Ll 29 1)) = 0
    rw [coeff_U, mul_zero]
    exact (odd_mem 0).1.1
  · simpa [γ] using L_env 2

lemma L2_reduce : PowerSeries.map (PadicInt.toZMod (p := 29)) (Ll 29 2) =
    (8 : ZMod 29) • Ψ 29 Cert29.g := by
  rw [show 2 = 2 * 0 + 2 from rfl, even_U]
  change PowerSeries.map (PadicInt.toZMod (p := 29)) (U 29 (Ll 29 1)) = _
  rw [map_U, show 1 = 2 * 0 + 1 from rfl, odd_reduction, pow_zero, mul_one,
    U_C_mul, Cert29.even_step, PowerSeries.smul_eq_C_mul]

lemma square_YL2 (data : Data) : PadicInt.toZModPow 2 (obs (Yop (Ll 29 2))) = 754 := by
  obtain ⟨c, d, R, hR, he⟩ := decompose (Ll 29 2) L2_mem
  have hm := reduce_decomposition (Ll 29 2) R c d he
  rw [L2_reduce] at hm
  have hc := congrArg (coeff 1) hm
  have hd := congrArg obsBar hm
  simp only [map_add, map_smul, coeff_smul, Image29.g_coeff 1 (by decide),
    Image29.f_coeff 1 (by decide), ite_true, ite_false, smul_eq_mul, mul_zero, add_zero] at hc
  simp only [map_add, map_smul, obs_g, obs_f, smul_zero, zero_add, smul_eq_mul] at hd
  norm_num at hc hd
  have hc' : PadicInt.toZMod c = 8 := by
    linear_combination (norm := ring_nf) -(10 : ZMod 29) * hc
    rw [show (29 : ZMod 29) = 0 from rfl, show (232 : ZMod 29) = 0 from rfl]
    simp
  have hd' : PadicInt.toZMod d = 0 := by
    exact hd.resolve_right (by decide)
  have hh := (cancel_mod_square (25 * c + 12 * d) 200).mpr (by
    simp only [map_add, map_mul, map_ofNat, hc', hd']
    decide +kernel)
  norm_num only [Nat.cast_ofNat] at hh
  rw [square_observation data (Ll 29 2) R c d hR he, hh]
  simp only [map_mul, map_ofNat]
  decide +kernel

lemma initial_observation (data : Data) (κ : ℤ_[29]) (H : PS 29)
    (hκ : PadicInt.toZMod κ = 3)
    (hH : Ll 29 4 - κ • Ll 29 2 = (29 : ℤ_[29]) • H) :
    PadicInt.toZMod (obs H) = 12 := by
  have he : Ll 29 4 = Yop (Ll 29 2) := by
    rw [show 4 = 2 * 1 + 2 from rfl, even_U, odd_D]
    rfl
  have h := congrArg (fun F => PadicInt.toZModPow 2 (obs F)) hH
  rw [he] at h
  simp only [map_sub, map_smul, smul_eq_mul, map_mul, map_ofNat, square_YL2 data, data.initial] at h
  have hk := (cancel_mod_square κ 3).mpr (by simpa only [map_ofNat] using hκ)
  simp only [map_mul, map_natCast, Nat.cast_ofNat, map_ofNat] at hk
  have hi : (696 : ZMod 841) = 24 * 29 := by decide +kernel
  have hh : PadicInt.toZModPow 2 ((29 : ℤ_[29]) * obs H) =
      PadicInt.toZModPow 2 ((29 : ℤ_[29]) * 12) := by
    simp only [map_mul, map_ofNat]
    rw [← h, hi, ← mul_assoc, mul_comm _ (24 : ZMod 841), mul_assoc,
      mul_comm _ (29 : ZMod 841), hk]
    decide +kernel
  have h' := (cancel_mod_square (obs H) 12).mp hh
  simpa only [map_ofNat] using h'

end RamanujanTau.FiniteArithmetic.InitialError29
