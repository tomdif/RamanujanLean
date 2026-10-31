import RamanujanTau.TheoremA.HalfIntegral

/-!
# The Boylan–Webb dictionary: `X̄ = D̄Ū` on `V` is `U_{ℓ²}`

Let `Δ = q(q;q)_∞²⁴`, `t = ⌊ℓ/24⌋`, `j = ℓ mod 24`. For `F = Δ^t G`, Frobenius and the identity
`U(g(q^ℓ) f) = g U(f)` give `X̄ F = Δ^t (q;q)_∞^j Ξ(G)`, where `Ξ(G)` has `m`-th coefficient
`A[ℓ²m - jδ]` and `A = G·(q;q)_∞^{-j}`. These are the half-integral coefficients `b(ℓ²n)`.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.HalfIntegral
open ModularForm UpperHalfPlane PowerSeries MockTheta5.JTP BoylanWebb
open scoped MatrixGroups
open RankProof (Ea Ea_X)

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `t = ⌊ℓ/24⌋`. -/
def tt (ℓ : ℕ) : ℕ := ℓ / 24

/-- `ρ = (jℓ-1)/24`. -/
def rho (ℓ : ℕ) : ℕ := (jj ℓ * ℓ - 1) / 24

lemma ell_mod (h13 : 13 ≤ ℓ) : jj ℓ = 1 ∨ jj ℓ = 5 ∨ jj ℓ = 7 ∨ jj ℓ = 11 ∨ jj ℓ = 13 ∨
    jj ℓ = 17 ∨ jj ℓ = 19 ∨ jj ℓ = 23 := by
  obtain ⟨h2, h3⟩ := SignLattice.prime_ge h13
  unfold jj
  omega

lemma ell_decomp : ℓ = 24 * tt ℓ + jj ℓ := (Nat.div_add_mod ℓ 24).symm

lemma h24 (h13 : 13 ≤ ℓ) : 24 * δ ℓ + 1 = ℓ ^ 2 := by
  have hdvd : 24 ∣ ℓ ^ 2 - 1 := by
    have hd := ell_decomp (ℓ := ℓ)
    have hj := ell_mod h13
    set t := tt ℓ
    rw [hd]
    apply (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp
    rcases hj with h | h | h | h | h | h | h | h <;> rw [h] <;>
      · apply Nat.ModEq.symm
        simp [Nat.ModEq, Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
  have hone : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ.out.pos
  unfold δ
  omega

lemma h24rho (h13 : 13 ≤ ℓ) : 24 * rho ℓ + 1 = jj ℓ * ℓ := by
  have hdvd : 24 ∣ jj ℓ * ℓ - 1 := by
    have hd := ell_decomp (ℓ := ℓ)
    have hj := ell_mod h13
    rcases hj with h | h | h | h | h | h | h | h <;> rw [h] <;> omega
  have hone : 1 ≤ jj ℓ * ℓ := by
    have hj := ell_mod h13
    have hp := hℓ.out.pos
    rcases hj with h | h | h | h | h | h | h | h <;> rw [h] <;> omega
  unfold rho
  omega

lemma delta_eq (h13 : 13 ≤ ℓ) : δ ℓ = ℓ * tt ℓ + rho ℓ := by
  have h1 := h24 h13
  have h2 := h24rho h13
  have hd := ell_decomp (ℓ := ℓ)
  have : 24 * δ ℓ = 24 * (ℓ * tt ℓ + rho ℓ) := by
    have e : ℓ ^ 2 = ℓ * (24 * tt ℓ + jj ℓ) := by rw [sq, ← hd]
    nlinarith
  omega

lemma jdelta_eq (h13 : 13 ≤ ℓ) : jj ℓ * δ ℓ = ℓ * rho ℓ + tt ℓ := by
  have h1 := h24 h13
  have h2 := h24rho h13
  have hd := ell_decomp (ℓ := ℓ)
  have : 24 * (jj ℓ * δ ℓ) = 24 * (ℓ * rho ℓ + tt ℓ) := by
    have e1 : 24 * δ ℓ = ℓ ^ 2 - 1 := by omega
    have e3 : (24 : ℤ) * δ ℓ = (ℓ : ℤ) ^ 2 - 1 := by
      have : ((24 * δ ℓ + 1 : ℕ) : ℤ) = ((ℓ ^ 2 : ℕ) : ℤ) := by rw [h1]
      push_cast at this
      linarith
    have e4 : (24 : ℤ) * rho ℓ = (jj ℓ : ℤ) * ℓ - 1 := by
      have : ((24 * rho ℓ + 1 : ℕ) : ℤ) = ((jj ℓ * ℓ : ℕ) : ℤ) := by rw [h2]
      push_cast at this
      linarith
    have e5 : (ℓ : ℤ) = 24 * tt ℓ + jj ℓ := by exact_mod_cast hd
    zify
    linear_combination (jj ℓ : ℤ) * e3 - (ℓ : ℤ) * e4 + e5
  omega

lemma Ea_congr {a b : ℕ} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (g : PowerSeries ℤ) :
    Ea a ha g = Ea b hb g := by
  subst h
  rfl

/-- Frobenius for `Δ`: `Δ^(ℓ s) ≡ Δ^s(q^ℓ)`. -/
lemma frob_Dz (s : ℕ) : Ψ ℓ (Dz ^ (ℓ * s)) = Ψ ℓ (Ea ℓ (hℓ0 ℓ) (Dz ^ s)) := by
  have hF : (Ψ ℓ qfacInf) ^ ℓ = Ψ ℓ (Ea ℓ (hℓ0 ℓ) qfacInf) := by
    calc (Ψ ℓ qfacInf) ^ ℓ = (Ψ ℓ qfacInf) ^ (ℓ ^ 1) := by rw [pow_one]
      _ = Ψ ℓ (Ea (ℓ ^ 1) (TauCong.ppow_ne ℓ 1) qfacInf) := TauCong.frob_qfacInf ℓ 1
      _ = Ψ ℓ (Ea ℓ (hℓ0 ℓ) qfacInf) := congrArg _ (Ea_congr (pow_one ℓ) _ _ _)
  have hEa : Ea ℓ (hℓ0 ℓ) (Dz ^ s) = (X ^ ℓ * (Ea ℓ (hℓ0 ℓ) qfacInf) ^ 24) ^ s := by
    rw [map_pow, Dz, map_mul, map_pow, Ea_X]
  rw [hEa, Dz]
  simp only [map_pow, map_mul]
  rw [← hF]
  ring

lemma coordOf_int (a : PowerSeries ℤ) : coordOf ℓ a = a * partitionGF ^ jj ℓ := by
  have h : PowerSeries.map (Int.castRingHom ℤ) partitionGF = partitionGF := by
    ext n
    simp
  rw [coordOf, h]

lemma U_U (f : PowerSeries ℤ) : U ℓ (U ℓ f) = U (ℓ ^ 2) f := by
  ext n
  simp only [coeff_U, sq, mul_assoc]

lemma Dz_jdelta (h13 : 13 ≤ ℓ) (a : PowerSeries ℤ) :
    Ψ ℓ (Dz ^ (jj ℓ * δ ℓ) * a) =
      Ψ ℓ (Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2) (qfacInf ^ jj ℓ) * (X ^ (jj ℓ * δ ℓ) * coordOf ℓ a)) := by
  have h1 := h24 h13
  have hF : (Ψ ℓ qfacInf) ^ (ℓ ^ 2) = Ψ ℓ (Ea (ℓ ^ 2) (TauCong.ppow_ne ℓ 2) qfacInf) :=
    TauCong.frob_qfacInf ℓ 2
  have hP : qfacInf * partitionGF = (1 : PowerSeries ℤ) := qfac_mul_pgf
  have hexp : (qfacInf : PowerSeries ℤ) ^ (24 * (jj ℓ * δ ℓ)) =
      (qfacInf ^ ℓ ^ 2) ^ jj ℓ * partitionGF ^ jj ℓ := by
    have : (qfacInf : PowerSeries ℤ) ^ (ℓ ^ 2 * jj ℓ) =
        qfacInf ^ (24 * (jj ℓ * δ ℓ)) * qfacInf ^ jj ℓ := by
      rw [← pow_add, ← h1]
      congr 1
      ring
    rw [← pow_mul, this, mul_assoc, ← mul_pow, hP, one_pow, mul_one]
  have hy := congrArg (Ψ ℓ) hexp
  simp only [map_mul, map_pow] at hy
  rw [coordOf_int, Dz]
  simp only [map_mul, map_pow]
  rw [← hF, mul_pow, ← pow_mul, hy]
  ring

/-- **The dictionary.** -/
theorem X_on_V (h13 : 13 ≤ ℓ) (a : PowerSeries ℤ) (h0 : a.coeff 0 = 0) :
    Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) =
      Ψ ℓ (Dz ^ tt ℓ * qfacInf ^ jj ℓ *
        PowerSeries.mk fun m => (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) := by
  have h1 := h24 h13
  set D := Dz ^ tt ℓ * a with hD
  have hA : Ψ ℓ (U ℓ (Φ ℓ * U ℓ D)) = Ψ ℓ (U ℓ (Dz ^ δ ℓ * U ℓ D)) := by
    rw [map_U, map_U, map_mul, map_mul, Ψ_Φ ℓ h1]
  have hB : Ψ ℓ (U ℓ (Dz ^ δ ℓ * U ℓ D)) = Ψ ℓ (Dz ^ tt ℓ * U ℓ (Dz ^ rho ℓ * U ℓ D)) := by
    have hpow : (Dz : PowerSeries ℤ) ^ δ ℓ * U ℓ D =
        Dz ^ (ℓ * tt ℓ) * (Dz ^ rho ℓ * U ℓ D) := by
      rw [delta_eq h13, pow_add, mul_assoc]
    rw [hpow, ← U_Ea_mul ℓ (hℓ0 ℓ) (Dz ^ tt ℓ), map_U, map_U, map_mul, map_mul (Ψ ℓ) (Ea _ _ _),
      frob_Dz]
  have hC : Ψ ℓ (U ℓ (Dz ^ rho ℓ * U ℓ D)) = Ψ ℓ (U (ℓ ^ 2) (Dz ^ (jj ℓ * δ ℓ) * a)) := by
    have hpow : (Dz : PowerSeries ℤ) ^ (ℓ * rho ℓ) * D = Dz ^ (jj ℓ * δ ℓ) * a := by
      rw [hD, ← mul_assoc, ← pow_add, jdelta_eq h13]
    rw [← U_Ea_mul ℓ (hℓ0 ℓ) (Dz ^ rho ℓ), ← U_U, ← hpow]
    simp only [map_U]
    rw [map_mul, map_mul (Ψ ℓ) (Dz ^ (ℓ * rho ℓ)), frob_Dz]
  have hE : U (ℓ ^ 2) (X ^ (jj ℓ * δ ℓ) * coordOf ℓ a) =
      PowerSeries.mk fun m => (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ) := by
    ext m
    rw [coeff_U, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    by_cases hm : m = 0
    · subst hm
      have hδ : 0 < δ ℓ := by nlinarith [hℓ.out.pos]
      have hj : 0 < jj ℓ := by
        rcases ell_mod h13 with h | h | h | h | h | h | h | h <;> omega
      have hpos : 0 < jj ℓ * δ ℓ := Nat.mul_pos hj hδ
      rw [if_neg (by rw [mul_zero]; exact Nat.not_le.mpr hpos)]
      have hc0 : (coordOf ℓ a).coeff 0 = 0 := by
        rw [coordOf_int, PowerSeries.coeff_mul]
        simp [h0]
      simp [hc0]
    · have hj : jj ℓ < 24 := Nat.mod_lt _ (by norm_num)
      have hle : jj ℓ * δ ℓ ≤ ℓ ^ 2 * m := by
        have h3 : jj ℓ * δ ℓ ≤ 24 * δ ℓ := Nat.mul_le_mul_right _ hj.le
        have h4 : ℓ ^ 2 ≤ ℓ ^ 2 * m := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
        omega
      rw [if_pos hle]
  have hF : Ψ ℓ (U (ℓ ^ 2) (Dz ^ (jj ℓ * δ ℓ) * a)) =
      Ψ ℓ (qfacInf ^ jj ℓ * PowerSeries.mk fun m => (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) := by
    rw [map_U, Dz_jdelta h13, ← map_U, U_Ea_mul (ℓ ^ 2) (TauCong.ppow_ne ℓ 2), hE]
  rw [hA, hB, map_mul, hC, hF, ← map_mul, mul_assoc]

/-- Injectivity of `U_{ℓ²}` in half-integral coordinates gives injectivity of `X̄ = D̄Ū` on `V`. -/
theorem X_injective_of_U_injective (h13 : 13 ≤ ℓ)
    (hT : ∀ a ∈ intLattice ℓ,
      (∀ m, (ℓ : ℤ) ∣ (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) → ∀ m, (ℓ : ℤ) ∣ a.coeff m)
    {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (hX : Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) = 0) :
    Ψ ℓ a = 0 := by
  have h0 : a.coeff 0 = 0 := by
    obtain ⟨G, hG⟩ := ha
    have hc : (qExpansion 1 G).coeff 0 = 0 := by
      rw [qExpansion_coeff_zero one_pos
        (analyticAt_cuspFunction_zero one_pos
          (SlashInvariantFormClass.periodic_comp_ofComplex G one_mem_strictPeriods_SL)
          (ModularFormClass.holo G) (ModularFormClass.bdd_at_infty G))
        (SlashInvariantFormClass.periodic_comp_ofComplex G one_mem_strictPeriods_SL)]
      exact (CuspFormClass.zero_at_infty G).valueAtInfty_eq_zero
    rw [← hG, PowerSeries.coeff_map] at hc
    exact RingHom.injective_int (Int.castRingHom ℂ) (by rw [hc, map_zero])
  rw [X_on_V h13 a h0, map_mul, map_mul] at hX
  have hQ0 : Ψ ℓ qfacInf ≠ 0 := by
    intro h
    have h' := congrArg (Ψ ℓ) (qfac_mul_pgf : qfacInf * partitionGF = (1 : PowerSeries ℤ))
    rw [map_mul, h, zero_mul, map_one] at h'
    exact zero_ne_one h'
  have hQ : Ψ ℓ (qfacInf ^ jj ℓ) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hQ0
  have hDz : Ψ ℓ (Dz ^ tt ℓ) ≠ 0 := by
    rw [map_pow, Dz, map_mul, map_pow]
    refine pow_ne_zero _ (mul_ne_zero ?_ (pow_ne_zero _ hQ0))
    rw [Ψ, PowerSeries.map_X]
    exact PowerSeries.X_ne_zero
  have hM := (mul_eq_zero.mp hX).resolve_left (mul_ne_zero hDz hQ)
  have hdvd := hT a ha (by
    intro m
    have := congrArg (PowerSeries.coeff m) hM
    rw [Ψ, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this)
  ext m
  rw [Ψ, PowerSeries.coeff_map, map_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hdvd m)

/-- **Theorem A for Boylan–Webb's operator.** Given Yang's correspondence, `X̄ = D̄Ū` is injective
on `V = Δ^t S_{k'}`, for every prime `ℓ ≥ 13`. -/
theorem X_injective_on_V (h13 : 13 ≤ ℓ) (Y : YangCorrespondence ℓ h13) {a : PowerSeries ℤ}
    (ha : a ∈ intLattice ℓ) (hX : Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) = 0) :
    Ψ ℓ a = 0 :=
  X_injective_of_U_injective h13 (fun _ hb hU => theoremA h13 Y hb hU) ha hX

end RamanujanTau.TheoremA.HalfIntegral
