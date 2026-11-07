import RamanujanTau.FiniteArithmetic.AllPowers31

/-! A scalar observation of the contracting error. The functional
`29 a₂ - 2 a₁` kills the unit-root line g modulo 31. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RamanujanTau.FiniteArithmetic.Error31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

noncomputable def obs : PS 31 →ₗ[ℤ_[31]] ℤ_[31] := (29 : ℤ_[31]) • coeff 2 - (2 : ℤ_[31]) • coeff 1

noncomputable def Yop : Module.End ℤ_[31] (PS 31) := (Ulin 31).comp (Dlin 31)

noncomputable def obsBar : PowerSeries (ZMod 31) →ₗ[ZMod 31] ZMod 31 := (29 : ZMod 31) • coeff 2 - (2 : ZMod 31) • coeff 1

lemma obs_reduce (F : PS 31) : PadicInt.toZMod (obs F) =
    obsBar (PowerSeries.map (PadicInt.toZMod (p := 31)) F) := by
  change PadicInt.toZMod (29 * coeff 2 F - 2 * coeff 1 F) =
    29 * coeff 2 (PowerSeries.map (PadicInt.toZMod (p := 31)) F) -
      2 * coeff 1 (PowerSeries.map (PadicInt.toZMod (p := 31)) F)
  rw [map_sub, map_mul, map_mul, map_ofNat, map_ofNat, coeff_map, coeff_map]

lemma obs_f : obsBar (Ψ 31 Cert31.f) = 29 := by
  change 29 * coeff 2 (Ψ 31 Cert31.f) - 2 * coeff 1 (Ψ 31 Cert31.f) = 29
  rw [Image31.f_coeff 2 (by decide), Image31.f_coeff 1 (by decide)]
  norm_num

lemma obs_g : obsBar (Ψ 31 Cert31.g) = 0 := by
  change 29 * coeff 2 (Ψ 31 Cert31.g) - 2 * coeff 1 (Ψ 31 Cert31.g) = 0
  rw [Image31.g_coeff 2 (by decide), Image31.g_coeff 1 (by decide)]
  norm_num

/-- A precision lost by division is recovered by D and U; its contribution
to the scalar observation vanishes modulo 31. -/
theorem tail_killed (F : PS 31) (hF : Env 31 (by norm_num) 2 (α 31) F) :
    PadicInt.toZMod (obs (Yop F)) = 0 := by
  have hD := D_env (by norm_num : 5 ≤ 31) (by norm_num) AllPowers31.bounds.2 2 le_rfl F hF
  obtain ⟨a, ha, he⟩ := envelope_reduction (by norm_num : 5 ≤ 31) (β 31)
    (fun i hi => (envelopes_ge_two (by norm_num : 13 ≤ 31) i hi).2) _ hD
  obtain ⟨c, hc⟩ := Image31.double_cusp_line a ha
    (by rw [he, coeff_map, AllPowers31.D_coeff_low _ 0 (by decide), map_zero])
    (by rw [he, coeff_map, AllPowers31.D_coeff_low _ 1 (by decide), map_zero])
  rw [obs_reduce]
  change obsBar (PowerSeries.map (PadicInt.toZMod (p := 31)) (U 31 (Dlin 31 F))) = 0
  rw [map_U, ← he, hc, U_C_mul, Cert31.even_step, ← PowerSeries.smul_eq_C_mul, map_smul, obs_g, smul_zero]

/-- A classical weight-30 numerator divided by E₂₈ belongs to the first
envelope, irrespective of the chosen Katz complement. -/
theorem fraction_env (P : Poly 31) (hP : ModP.Iso P 30) :
    Env 31 (by norm_num) 1 (α 31) (ModP.ev ℤ_[31] P * Einv 31 (by norm_num)) := by
  intro N
  obtain ⟨c, hc, hc0, hD⟩ := DBound.decompN (by norm_num : 5 ≤ 31) N 1 P (by simpa using hP)
  refine ⟨2, c, hc, by simpa only [pow_one] using hD, fun i => ?_⟩
  by_cases hi : i ≤ 1
  · have hα : α 31 i ≤ 1 := by
      interval_cases i <;> norm_num [α]
    have he : (max 0 (α 31 i - 1)).toNat = 0 := by omega
    rw [he]
    exact ⟨c i, by simp⟩
  · rw [hc0 i (by omega)]
    exact Dvd_zero _

noncomputable def fLift : PS 31 :=
  PowerSeries.map (Int.castRingHom ℤ_[31]) Cert31.f * Einv 31 (by norm_num)

noncomputable def gLift : PS 31 :=
  PowerSeries.map (Int.castRingHom ℤ_[31]) Cert31.g * Einv 31 (by norm_num)

lemma fLift_reduce : PowerSeries.map (PadicInt.toZMod (p := 31)) fLift = Ψ 31 Cert31.f := by
  rw [fLift, map_mul, map_map_int, map_Einv, mul_one]

lemma gLift_reduce : PowerSeries.map (PadicInt.toZMod (p := 31)) gLift = Ψ 31 Cert31.g := by
  rw [gLift, map_mul, map_map_int, map_Einv, mul_one]

private noncomputable def Pf : Poly 31 := DBound.Pdisc (by norm_num : 5 ≤ 31) ^ 2 * MvPolynomial.X 1
private noncomputable def Ph : Poly 31 := DBound.Pdisc (by norm_num : 5 ≤ 31) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)

private lemma iso_X : ModP.Iso (MvPolynomial.X 0 : Poly 31) 4 := by
  simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[31] ModP.wt (0 : Fin 2)

private lemma iso_Y : ModP.Iso (MvPolynomial.X 1 : Poly 31) 6 := by
  simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[31] ModP.wt (1 : Fin 2)

private lemma iso_Pf : ModP.Iso Pf 30 :=
  ModP.iso_of_eq (((DBound.iso_Pdisc (by norm_num : 5 ≤ 31)).pow 2).mul iso_Y) (by decide)

private lemma iso_Ph : ModP.Iso Ph 30 :=
  ModP.iso_of_eq ((DBound.iso_Pdisc (by norm_num : 5 ≤ 31)).mul ((iso_X.pow 3).mul iso_Y)) (by decide)

private lemma ev_Pf : ModP.ev ℤ_[31] Pf = PowerSeries.map (Int.castRingHom ℤ_[31]) Cert31.f := by
  simp only [Pf, map_mul, map_pow, DBound.ev_Pdisc, ModP.ev_X1, Cert31.f]
  simp only [DBound.Dl, ModP.Dq, ModP.E6, map_mul, map_pow]

private lemma ev_Ph : ModP.ev ℤ_[31] Ph = PowerSeries.map (Int.castRingHom ℤ_[31]) Cert31.h := by
  simp only [Ph, map_mul, map_pow, DBound.ev_Pdisc, ModP.ev_X0, ModP.ev_X1, Cert31.h]
  simp only [DBound.Dl, ModP.Dq, ModP.E4, ModP.E6, map_mul, map_pow]

theorem fLift_env : Env 31 (by norm_num) 1 (α 31) fLift := by
  have h := fraction_env Pf iso_Pf
  rwa [ev_Pf] at h

theorem gLift_env : Env 31 (by norm_num) 1 (α 31) gLift := by
  have h := fraction_env (MvPolynomial.C 29 * Ph + MvPolynomial.C 14 * Pf)
    ((iso_Ph.C_mul 29).add (iso_Pf.C_mul 14))
  simpa only [map_add, map_mul, ModP.ev_C, ev_Ph, ev_Pf, gLift, Cert31.g, PowerSeries.map_C,
    map_ofNat] using h

lemma fLift_cusp : coeff 0 fLift = 0 := by
  simp [fLift, Cert31.f, Dz, coeff_zero_eq_constantCoeff]

lemma gLift_cusp : coeff 0 gLift = 0 := by
  simp [gLift, Cert31.g, Cert31.h, Cert31.f, Dz, coeff_zero_eq_constantCoeff]

/-- Every cusp in the first envelope has two coordinates and a divided tail. -/
theorem decompose (F : PS 31) (hF : F ∈ envSub (by norm_num : 5 ≤ 31) 1 (α 31)) :
    ∃ c d : ℤ_[31], ∃ R : PS 31, Env 31 (by norm_num) 2 (α 31) R ∧
      F = c • gLift + d • fLift + (31 : ℤ_[31]) • R := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (by norm_num : 5 ≤ 31) (α 31)
    (fun i hi => (envelopes_ge_two (by norm_num : 13 ≤ 31) i hi).1) F hF.2
  obtain ⟨c₀, c₁, c₂, hc⟩ := Image31.span a ha
  have h0 := congrArg (coeff 0) hc
  rw [he, coeff_map, hF.1, map_zero] at h0
  simp only [map_add, coeff_C_mul, Image31.f_coeff 0 (by decide),
    Image31.g_coeff 0 (by decide)] at h0
  norm_num at h0
  have hbar : PowerSeries.map (PadicInt.toZMod (p := 31)) F =
      c₁ • Ψ 31 Cert31.g + c₂ • Ψ 31 Cert31.f := by
    rw [← he, hc, ← h0, map_zero, zero_add]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
  let c : ℤ_[31] := c₁.val
  let d : ℤ_[31] := c₂.val
  have hc' : PadicInt.toZMod c = c₁ := by simp [c]
  have hd' : PadicInt.toZMod d = c₂ := by simp [d]
  obtain ⟨R, hR⟩ := PS_dvd_of_map (F - (c • gLift + d • fLift)) (by
    rw [map_sub, map_add, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
      map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C,
      hc', hd', gLift_reduce, fLift_reduce, hbar]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, sub_self])
  norm_num only [Nat.cast_ofNat] at hR
  have hm : F - (c • gLift + d • fLift) ∈ envSub (by norm_num : 5 ≤ 31) 1 (α 31) :=
    (envSub _ _ _).sub_mem hF ((envSub _ _ _).add_mem
      ((envSub _ _ _).smul_mem c ⟨gLift_cusp, gLift_env⟩)
      ((envSub _ _ _).smul_mem d ⟨fLift_cusp, fLift_env⟩))
  refine ⟨c, d, R, ?_, ?_⟩
  · simpa using env_div (by norm_num : 5 ≤ 31) 1 (α 31) hm.2 hR
  · rw [← hR]; abel

end RamanujanTau.FiniteArithmetic.Error31
