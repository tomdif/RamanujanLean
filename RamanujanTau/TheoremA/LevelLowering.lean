import RamanujanTau.TheoremA.GoodHecke

/-!
# Level lowering for forms in `q^t`

If `g` is a modular form on Γ₀(Mt) with `gcd(M,t)=1` and its expansion lies in powers of `q^t`,
then `g(z/t)` is a modular form on Γ₀(M). The subgroup of Γ₀(M) with upper-right entry divisible by
`t`, together with the translation, generates Γ₀(M), by an explicit double-coset reduction.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelLowering
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Complex
open scoped MatrixGroups ModularForm
open BadPrime
local notation "𝕢" => Function.Periodic.qParam

/-- There is a shift of `a` by a multiple of `c` prime to `t`, when `a, c` are coprime. -/
lemma exists_shift_coprime (a c : ℤ) (h : IsCoprime a c) (t : ℕ) (ht : t ≠ 0) :
    ∃ m : ℤ, IsCoprime (a + m * c) (t : ℤ) := by
  classical
  let P : Finset ℕ := t.primeFactors.filter fun p => ¬ (p : ℤ) ∣ a
  let m : ℤ := ∏ p ∈ P, (p : ℤ)
  refine ⟨m, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  have hg : Int.gcd (a + m * c) t ≠ 1 := hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  have hp1 : (p : ℤ) ∣ a + m * c := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left ..)
  have hp2 : p ∣ t := by
    have := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right (a + m * c) t)
    exact_mod_cast this
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpa : (p : ℤ) ∣ a
  · have hmc : (p : ℤ) ∣ m * c := (dvd_add_right hpa).mp hp1
    rcases hpr.dvd_or_dvd hmc with hm | hc
    · obtain ⟨q, hq, hpq⟩ := (Prime.exists_mem_finset_dvd hpr hm)
      have hqmem := Finset.mem_filter.mp hq
      have hqp : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors hqmem.1
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (by exact_mod_cast hpq)
      exact hqmem.2 (heq ▸ hpa)
    · exact hpr.not_unit (h.isUnit_of_dvd' hpa hc)
  · have hmem : p ∈ P := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hp2, ht⟩, hpa⟩
    have hm : (p : ℤ) ∣ m := Finset.dvd_prod_of_mem _ hmem
    exact hpa ((dvd_add_left (hm.mul_right c)).mp hp1)

/-- The translation in `SL₂(ℤ)`. -/
def tr (n : ℤ) : SL(2, ℤ) := ⟨!![1, n; 0, 1], by simp [det_fin_two_of]⟩

lemma tr_mem (M : ℕ) (n : ℤ) : tr n ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [tr]

/-- **Double-coset reduction.** Every element of Γ₀(M) is `T^u δ T^v`, with `t` dividing the upper
right entry of `δ`. -/
theorem exists_decomposition (M t : ℕ) (ht : t ≠ 0) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ u v : ℤ, ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧ (t : ℤ) ∣ δ 0 1 ∧ γ = tr u * δ * tr v := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [det_fin_two] at h
  have hcop : IsCoprime (γ 0 0) (γ 1 0) := ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
  obtain ⟨m, hm⟩ := exists_shift_coprime _ _ hcop t ht
  obtain ⟨x, y, hxy⟩ := hm
  let a' := γ 0 0 + m * γ 1 0
  let b' := γ 0 1 + m * γ 1 1
  let n := -(b' * x)
  let δ : SL(2, ℤ) := tr m * γ * tr n
  have hmat : (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![a', b' + a' * n; γ 1 0, γ 1 1 + γ 1 0 * n] := by
    have hη := Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    change !![1, m; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, n; 0, 1] = _
    rw [hη]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a', b'] <;> ring
  have he01 : δ 0 1 = b' + a' * n := by rw [hmat]; rfl
  have he10 : δ 1 0 = γ 1 0 := by rw [hmat]; rfl
  refine ⟨-m, -n, δ, ?_, ?_, ?_⟩
  · rw [Gamma0_mem, he10]
    exact hγ
  · rw [he01]
    refine ⟨b' * y, ?_⟩
    simp only [n]
    change x * a' + y * (t : ℤ) = 1 at hxy
    linear_combination -b' * hxy
  · have h1 : ∀ s : ℤ, tr (-s) * tr s = 1 := by
      intro s
      ext i j
      fin_cases i <;> fin_cases j <;> simp [tr, Matrix.mul_apply, Fin.sum_univ_two]
    have h2 : ∀ s : ℤ, tr s * tr (-s) = 1 := fun s => by simpa using h1 (-s)
    simp only [δ]
    calc γ = (tr (-m) * tr m) * γ * (tr n * tr (-n)) := by rw [h1, h2]; simp
      _ = _ := by simp only [mul_assoc]

variable {M t : ℕ} [NeZero M] [NeZero t] {k : ℤ}

/-- The rational matrix `[1 0; 0 t]`. -/
noncomputable def ratLow (t : ℕ) [NeZero t] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' !![(1 : ℚ), 0; 0, (t : ℚ)] (by
    have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne t
    simp [Matrix.det_fin_two_of, ht0])

/-- The matrix `[1 0; 0 t]` acting through Mathlib's slash action. -/
noncomputable def lowGL (t : ℕ) [NeZero t] : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratLow t)

lemma lowGL_val : (lowGL t).val = !![(1 : ℝ), 0; 0, (t : ℝ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowGL, ratLow]

lemma low_slash (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] lowGL t) z = (t : ℂ)⁻¹ * f (ofComplex ((z : ℂ) / t)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hdet : (lowGL t).det.val = (t : ℝ) := by
    change (lowGL t).val.det = _
    rw [lowGL_val, det_fin_two_of]
    simp
  have him : 0 < ((z : ℂ) / t).im := by
    have := div_pos z.im_pos htR
    simpa [Complex.div_natCast_im] using this
  have hden : denom (lowGL t) z = (t : ℂ) := by simp [denom, lowGL_val]
  have hsm : lowGL t • z = ofComplex ((z : ℂ) / t) := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by rw [hdet]; exact htR), ofComplex_apply_of_im_pos him, hden]
    simp [num, lowGL_val]
  rw [slash_apply, hsm, hden]
  simp only [σ, hdet, if_pos htR, ContinuousAlgEquiv.refl_apply, abs_of_pos htR, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ htC]
  have he : k - 1 + -k = (-1 : ℤ) := by ring
  rw [he, _root_.zpow_neg_one, mul_comm]

/-- Conjugation by `[1 0; 0 t]`. -/
def conjLow (t : ℕ) (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 0 1) : SL(2, ℤ) :=
  ⟨!![δ 0 0, δ 0 1 / t; t * δ 1 0, δ 1 1], by
    have hd := δ.property
    rw [det_fin_two] at hd
    rw [det_fin_two_of]
    have he : (δ 0 1 / (t : ℤ)) * t = δ 0 1 := Int.ediv_mul_cancel h
    linear_combination hd - δ 1 0 * he⟩

lemma low_mul (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 0 1) :
    lowGL t * SpecialLinearGroup.mapGL ℝ δ =
      SpecialLinearGroup.mapGL ℝ (conjLow t δ h) * lowGL t := by
  apply Units.ext
  have he : ((δ 0 1 / (t : ℤ) : ℤ) : ℝ) * t = (δ 0 1 : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel h
  change (lowGL t).val * (SpecialLinearGroup.mapGL ℝ δ).val =
    (SpecialLinearGroup.mapGL ℝ (conjLow t δ h)).val * (lowGL t).val
  rw [lowGL_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conjLow, Matrix.mul_apply, Fin.sum_univ_two, he]
  all_goals ring

/-- Fourier expansion of `g(z/t)` when the expansion of `g` is in powers of `q^t`. -/
lemma hasSum_low [NeZero (M * t)] (g : ModularForm (Gamma0 (M * t) : Subgroup (GL (Fin 2) ℝ)) k)
    (b : PowerSeries ℂ) (hb : qExpansion 1 g = PowerSeries.expand t (NeZero.ne t) b) (z : ℍ) :
    HasSum (fun m => b.coeff m * 𝕢 1 z ^ m) (g (ofComplex ((z : ℂ) / t))) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have him : 0 < ((z : ℂ) / t).im := by
    have := div_pos z.im_pos htR
    simpa [Complex.div_natCast_im] using this
  have h0 := hasSum_modular_Gamma0 g him
  rw [hb] at h0
  have hinj : Function.Injective (fun n : ℕ => t * n) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne t)) h
  have hoff : ∀ n ∉ Set.range (fun n : ℕ => t * n),
      (PowerSeries.expand t (NeZero.ne t) b).coeff n * 𝕢 1 ((z : ℂ) / t) ^ n = 0 := by
    intro n hn
    have hnd : ¬ t ∣ n := fun ⟨c, hc⟩ => hn ⟨c, hc.symm⟩
    rw [PowerSeries.coeff_expand, if_neg hnd, zero_mul]
  have := (hinj.hasSum_iff hoff).mpr h0
  convert this using 2 with m
  simp only [Function.comp, PowerSeries.coeff_expand, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne t))]
  congr 1
  rw [pow_mul, ← RamanujanTau.Hecke.qP_mul t, mul_div_cancel₀ _ htC]

/-- The expansion identifies the slash of `g` by `[1 0; 0 t]`, and it is periodic. -/
lemma low_translate [NeZero (M * t)] (g : ModularForm (Gamma0 (M * t) : Subgroup (GL (Fin 2) ℝ)) k)
    (b : PowerSeries ℂ) (hb : qExpansion 1 g = PowerSeries.expand t (NeZero.ne t) b) (n : ℤ) :
    ((g : ℍ → ℂ) ∣[k] lowGL t) ∣[k] SpecialLinearGroup.mapGL ℝ (tr n) = (g : ℍ → ℂ) ∣[k] lowGL t := by
  funext z
  have hden : denom (SpecialLinearGroup.mapGL ℝ (tr n)) z = 1 := by simp [denom, tr]
  have hdet : (SpecialLinearGroup.mapGL ℝ (tr n) : GL (Fin 2) ℝ).det.val = 1 := by simp
  have hsm : (SpecialLinearGroup.mapGL ℝ (tr n) : GL (Fin 2) ℝ) • z = ofComplex ((z : ℂ) + n) := by
    apply UpperHalfPlane.ext
    have him : 0 < ((z : ℂ) + n).im := by simpa using z.im_pos
    rw [coe_smul_of_det_pos (by rw [hdet]; norm_num), ofComplex_apply_of_im_pos him, hden]
    simp [num, tr]
  rw [slash_apply, hden, hsm]
  simp only [σ, hdet, one_pos, if_true, ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
    _root_.one_zpow, mul_one]
  have him : 0 < ((z : ℂ) + n).im := by simpa using z.im_pos
  rw [low_slash, low_slash]
  congr 1
  have h1 := hasSum_low g b hb z
  have h2 := hasSum_low g b hb (ofComplex ((z : ℂ) + n))
  have hco : ((ofComplex ((z : ℂ) + n) : ℍ) : ℂ) = (z : ℂ) + n := by
    rw [ofComplex_apply_of_im_pos him]
  rw [hco] at h2
  have hq : 𝕢 1 ((z : ℂ) + n) = 𝕢 1 (z : ℂ) := by
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    rw [mul_add, Complex.exp_add]
    have : (2 * (Real.pi : ℂ) * Complex.I * n) = n * (2 * Real.pi * Complex.I) := by ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hq] at h2
  rw [hco]
  exact h2.unique h1

/-- **Level lowering.** A form on Γ₀(Mt) with expansion in powers of `q^t` comes from Γ₀(M). -/
theorem exists_lowered [NeZero (M * t)]
    (g : ModularForm (Gamma0 (M * t) : Subgroup (GL (Fin 2) ℝ)) k)
    (b : PowerSeries ℂ) (hb : qExpansion 1 g = PowerSeries.expand t (NeZero.ne t) b) :
    ∃ f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k, qExpansion 1 f = b := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  let f0 : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := (g : ℍ → ℂ) ∣[k] lowGL t
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        obtain ⟨u, v, δ, hδ, hdvd, rfl⟩ := exists_decomposition M t (NeZero.ne t) γ hγ
        have hc : conjLow t δ hdvd ∈ Gamma0 (M * t) := by
          rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
          change ((M * t : ℕ) : ℤ) ∣ (t : ℤ) * δ 1 0
          have hM : (M : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
          push_cast
          rw [mul_comm (M : ℤ)]
          exact mul_dvd_mul_left _ hM
        have hδs : ((g : ℍ → ℂ) ∣[k] lowGL t) ∣[k] SpecialLinearGroup.mapGL ℝ δ =
            (g : ℍ → ℂ) ∣[k] lowGL t := by
          rw [← SlashAction.slash_mul, low_mul δ hdvd, SlashAction.slash_mul,
            SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map.mpr ⟨_, hc, rfl⟩)]
        rw [map_mul, map_mul, SlashAction.slash_mul, SlashAction.slash_mul,
          low_translate g b hb, hδs, low_translate g b hb]
      holo' := (ModularFormClass.holo g).slash k (lowGL t)
      bdd_at_cusps' := by
        intro c hc γ hγ
        have hc' : IsCusp c (Gamma0 (M * t) : Subgroup (GL (Fin 2) ℝ)) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact hc
        have hbdd : OnePoint.IsBoundedAt c ((g : ℍ → ℂ) ∣[k] lowGL t) k := by
          apply OnePoint.IsBoundedAt.smul_iff.mp
          exact ModularFormClass.bdd_at_cusps g (isCusp_rational_smul hc' (ratLow t))
        exact hbdd γ hγ }
  refine ⟨(t : ℂ) • f0, ?_⟩
  ext m
  refine (ModularFormClass.qExpansion_coeff_unique (f := (t : ℂ) • f0)
    (c := fun m => b.coeff m) one_pos one_period (fun z => ?_) m).symm
  have hz := hasSum_low g b hb z
  have hf : ((t : ℂ) • f0) z = g (ofComplex ((z : ℂ) / t)) := by
    change (t : ℂ) * ((g : ℍ → ℂ) ∣[k] lowGL t) z = _
    rw [low_slash, ← mul_assoc, mul_inv_cancel₀ htC, one_mul]
  rw [hf]
  simpa [smul_eq_mul] using hz

end RamanujanTau.TheoremA.LevelLowering
