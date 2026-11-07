import RamanujanTau.FiniteArithmetic.ErrorDynamics31

/-! Initialize the scalar error law from the actual partition orbit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.InitialError31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Error31 AllPowers31 ErrorDynamics31 PadicDivision

lemma L2_mem : Ll 31 2 ∈ envSub (by norm_num : 5 ≤ 31) 1 (α 31) := by
  refine ⟨?_, ?_⟩
  · rw [show 2 = 2 * 0 + 2 from rfl, even_U]
    change coeff 0 (U 31 (Ll 31 1)) = 0
    rw [coeff_U, mul_zero]
    exact (odd_mem 0).1.1
  · simpa [γ] using L_env 2

lemma L2_reduce : PowerSeries.map (PadicInt.toZMod (p := 31)) (Ll 31 2) =
    (10 : ZMod 31) • Ψ 31 Cert31.g := by
  rw [show 2 = 2 * 0 + 2 from rfl, even_U]
  change PowerSeries.map (PadicInt.toZMod (p := 31)) (U 31 (Ll 31 1)) = _
  rw [map_U, show 1 = 2 * 0 + 1 from rfl, odd_reduction, pow_zero, mul_one,
    U_C_mul, Cert31.even_step, PowerSeries.smul_eq_C_mul]

lemma square_YL2 (data : Data) : PadicInt.toZModPow 2 (obs (Yop (Ll 31 2))) = 744 := by
  obtain ⟨c, d, R, hR, he⟩ := decompose (Ll 31 2) L2_mem
  have hm := reduce_decomposition (Ll 31 2) R c d he
  rw [L2_reduce] at hm
  have hc := congrArg (coeff 1) hm
  have hd := congrArg obsBar hm
  simp only [map_add, map_smul, coeff_smul, Image31.g_coeff 1 (by decide),
    Image31.f_coeff 1 (by decide), ite_true, ite_false, smul_eq_mul, mul_zero, add_zero] at hc
  simp only [map_add, map_smul, obs_g, obs_f, smul_zero, zero_add, smul_eq_mul] at hd
  norm_num at hc hd
  have hc' : PadicInt.toZMod c = 10 := by
    have h31 : (31 : ZMod 31) = 0 := rfl
    linear_combination (-15 : ZMod 31) * hc + (140 - 14 * PadicInt.toZMod c) * h31
  have hd' : PadicInt.toZMod d = 0 := by
    exact hd.resolve_right (by decide)
  have hh := (cancel_mod_square (21 * c + 7 * d) 210).mpr (by
    simp only [map_add, map_mul, map_ofNat, hc', hd']
    decide +kernel)
  norm_num only [Nat.cast_ofNat] at hh
  rw [square_observation data (Ll 31 2) R c d hR he, hh]
  simp only [map_mul, map_ofNat]
  decide +kernel

lemma initial_observation (data : Data) (κ : ℤ_[31]) (H : PS 31)
    (hH : Ll 31 4 - κ • Ll 31 2 = (31 : ℤ_[31]) • H) :
    PadicInt.toZMod (obs H) = 24 := by
  have he : Ll 31 4 = Yop (Ll 31 2) := by
    rw [show 4 = 2 * 1 + 2 from rfl, even_U, odd_D]
    rfl
  have h := congrArg (fun F => PadicInt.toZModPow 2 (obs F)) hH
  rw [he] at h
  simp only [map_sub, map_smul, smul_eq_mul, map_mul, map_ofNat, square_YL2 data, data.initial,
    mul_zero, sub_zero] at h
  have hh : PadicInt.toZModPow 2 ((31 : ℤ_[31]) * obs H) =
      PadicInt.toZModPow 2 ((31 : ℤ_[31]) * 24) := by
    simp only [map_mul, map_ofNat]
    rw [← h]
    decide +kernel
  have h' := (cancel_mod_square (obs H) 24).mp hh
  simpa only [map_ofNat] using h'

end RamanujanTau.FiniteArithmetic.InitialError31
