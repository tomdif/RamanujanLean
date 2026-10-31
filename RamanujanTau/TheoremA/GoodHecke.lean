import RamanujanTau.TheoremA.AtkinLehner
import RamanujanTau.HeckeQExp.Tq

/-!
# The Hecke operator `T_ℓ` on Γ₀(M) for a prime not dividing the level

The form `f ∣ [ℓ 0; 0 1]` has level Mℓ. Mathlib's actual trace of that form to
level M is `T_ℓ f`, so modularity and every cusp condition come from the trace
construction. The explicit cosets from `TraceCosets` identify its q-expansion
with the classical coefficient formula.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.GoodHecke
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Complex Finset
open scoped MatrixGroups ModularForm
open TraceCosets BadPrime
local notation "𝕢" => Function.Periodic.qParam

variable {p M : ℕ} [hp : Fact p.Prime] {k : ℤ}

/-- The rational matrix `[p 0; 0 1]`. -/
noncomputable def ratDiag (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' !![(p : ℚ), 0; 0, 1] (by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simp [Matrix.det_fin_two_of, hp0])

/-- The matrix `[p 0; 0 1]` acting through Mathlib's slash action. -/
noncomputable def diagGL (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratDiag p)

lemma diagGL_val : (diagGL p).val = !![(p : ℝ), 0; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagGL, ratDiag]

/-- Conjugating by the diagonal matrix sends Γ₀(Mp) into Γ₀(M). -/
noncomputable def conj (γ : SL(2, ℤ)) (hγ : (p : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (p : ℤ) * γ 0 1; γ 1 0 / p, γ 1 1], by
    have h := γ.property
    rw [det_fin_two] at h
    rw [det_fin_two_of]
    have he : (p : ℤ) * (γ 1 0 / p) = γ 1 0 := Int.mul_ediv_cancel' hγ
    linear_combination h - γ 0 1 * he⟩

lemma diag_mul (γ : SL(2, ℤ)) (hγ : (p : ℤ) ∣ γ 1 0) :
    diagGL p * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ (conj (p := p) γ hγ) * diagGL p := by
  apply Units.ext
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : ((γ 1 0 / (p : ℤ) : ℤ) : ℝ) * p = (γ 1 0 : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hγ
  change (diagGL p).val * (SpecialLinearGroup.mapGL ℝ γ).val =
    (SpecialLinearGroup.mapGL ℝ (conj (p := p) γ hγ)).val * (diagGL p).val
  rw [diagGL_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conj, Matrix.mul_apply, Fin.sum_univ_two, he]
  ring

/-- The level-raised form `f ∣ [p 0; 0 1]`, of level Mp. -/
noncomputable def raise [NeZero M]
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := (f : ℍ → ℂ) ∣[k] diagGL p
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    have hdiv : ((M * p : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
    have hpd : (p : ℤ) ∣ γ 1 0 := dvd_trans (by push_cast; exact dvd_mul_left _ _) hdiv
    rw [← SlashAction.slash_mul, diag_mul γ hpd, SlashAction.slash_mul]
    have hc : conj (p := p) γ hpd ∈ Gamma0 M := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      change (M : ℤ) ∣ γ 1 0 / p
      obtain ⟨t, ht⟩ := hdiv
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      refine ⟨t, ?_⟩
      rw [ht, show ((M * p : ℕ) : ℤ) * t = (p : ℤ) * ((M : ℤ) * t) by push_cast; ring,
        Int.mul_ediv_cancel_left _ hp0]
    rw [SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map.mpr ⟨_, hc, rfl⟩)]
  holo' := (ModularFormClass.holo f).slash k (diagGL p)
  bdd_at_cusps' {c} hc γ hγ := by
    have hc' : IsCusp c (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    have hb : OnePoint.IsBoundedAt c ((f : ℍ → ℂ) ∣[k] diagGL p) k := by
      apply OnePoint.IsBoundedAt.smul_iff.mp
      exact ModularFormClass.bdd_at_cusps f (isCusp_rational_smul hc' (ratDiag p))
    exact hb γ hγ

@[simp] lemma coe_raise [NeZero M]
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    (raise (p := p) f : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] diagGL p := rfl

/-- `T_p`, as Mathlib's actual trace of the level-raised form. -/
noncomputable def heckeT [NeZero M] [NeZero (M * p)]
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k :=
  ModularForm.trace (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) (raise (p := p) f)

/-- The diagonal matrix times a coset matrix factors through `[1 j; 0 p]`. -/
lemma diag_mul_gam (D : CosetData p M) (j : ZMod p) :
    diagGL p * SpecialLinearGroup.mapGL ℝ (D.gam j) =
      SpecialLinearGroup.mapGL ℝ
        (⟨!![(p : ℤ) * D.x, D.y; M * D.z, D.w], by
          rw [det_fin_two_of]; linear_combination D.det_eq⟩ : SL(2, ℤ)) * realRep p j := by
  apply Units.ext
  change (diagGL p).val * (SpecialLinearGroup.mapGL ℝ (D.gam j)).val = _ * (realRep p j).val
  rw [diagGL_val, realRep_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [CosetData.gam, representative, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The trace of the raised form is `f ∣ [p 0; 0 1] + U_p f`. -/
theorem coe_heckeT [NeZero M] [NeZero (M * p)] (D : CosetData p M)
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeT (p := p) f : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] diagGL p + slashU p k f := by
  rw [heckeT, D.trace_eq, coe_raise, slashU]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, diag_mul_gam, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩)]
  rw [Gamma0_mem]
  simp

lemma diag_slash (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] diagGL p) z =
      ((p : ℂ) ^ (k - 1)) * f (ofComplex ((p : ℂ) * z)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hdet : (diagGL p).det.val = (p : ℝ) := by
    change (diagGL p).val.det = _
    rw [diagGL_val, det_fin_two_of]
    simp
  have him : 0 < ((p : ℂ) * z).im := by
    simpa using mul_pos hpR z.im_pos
  have hsm : diagGL p • z = ofComplex ((p : ℂ) * z) := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by rw [hdet]; exact hpR), ofComplex_apply_of_im_pos him]
    simp [num, denom, diagGL_val]
  have hden : denom (diagGL p) z = 1 := by simp [denom, diagGL_val]
  rw [slash_apply, hsm, hden]
  simp only [σ, hdet, if_pos hpR, ContinuousAlgEquiv.refl_apply, abs_of_pos hpR]
  simp [mul_comm]

/-- Fourier expansion of the translate sum, valid for any prime. -/
theorem hasSum_slashU [NeZero M]
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    HasSum (fun m => (qExpansion 1 f).coeff (p * m) * 𝕢 1 z ^ m) (slashU p k f z) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h0 := hasSum_sum (s := range p) fun j _ => hasSum_modular_Gamma0 f
    (RamanujanTau.Hecke.im_div_nat (j := j) z.im_pos hp.out.pos)
  have he : ∀ n, ∑ j ∈ range p, (qExpansion 1 f).coeff n * 𝕢 1 (((z : ℂ) + j) / p) ^ n =
      (qExpansion 1 f).coeff n * 𝕢 1 ((z : ℂ) / p) ^ n * (if p ∣ n then (p : ℂ) else 0) := by
    intro n
    simp_rw [RamanujanTau.Hecke.qP_shift, mul_pow, ← mul_sum, RamanujanTau.Hecke.root_sum]
    ring
  simp_rw [he] at h0
  rw [← RamanujanTau.Hecke.hasSum_mul_reindex p (fun n hn => by simp [hn])] at h0
  have hpow : ∀ m, 𝕢 1 ((z : ℂ) / p) ^ (p * m) = 𝕢 1 z ^ m := by
    intro m
    rw [pow_mul, ← RamanujanTau.Hecke.qP_mul, mul_div_cancel₀ _ hpC]
  simp_rw [hpow, if_pos (dvd_mul_right p _)] at h0
  have hs : slashU p k f z = (p : ℂ)⁻¹ * ∑ j ∈ range p, f (ofComplex (((z : ℂ) + j) / p)) := by
    simp only [slashU, Finset.sum_apply, realRep_slash]
    rw [← mul_sum, sum_zmod_val (fun j => f (ofComplex (((z : ℂ) + j) / p)))]
  rw [hs]
  convert h0.mul_left (p : ℂ)⁻¹ using 1
  funext m
  field_simp

/-- **`T_p` has the classical coefficient formula.** -/
theorem qExpansion_heckeT [NeZero M] [NeZero (M * p)] (D : CosetData p M)
    (f : ModularForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (heckeT (p := p) f) =
      HeckeQExp.Tq p ((p : ℂ) ^ (k - 1)) (qExpansion 1 f) := by
  have hpne := hp.out.ne_zero
  ext m
  rw [HeckeQExp.coeff_Tq]
  refine (ModularFormClass.qExpansion_coeff_unique (f := heckeT (p := p) f)
    (c := fun m => (qExpansion 1 f).coeff (p * m) +
      (p : ℂ) ^ (k - 1) * if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0)
    one_pos one_period (fun z => ?_) m).symm
  have hU := hasSum_slashU (p := p) f z
  have hw : 0 < ((p : ℂ) * z).im := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    simpa using mul_pos hpR z.im_pos
  have hV := (hasSum_modular_Gamma0 f hw).mul_left ((p : ℂ) ^ (k - 1))
  have hV' : HasSum (fun m => ((p : ℂ) ^ (k - 1) *
      if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0) * 𝕢 1 z ^ m)
      (((f : ℍ → ℂ) ∣[k] diagGL p) z) := by
    rw [diag_slash]
    have hinj : Function.Injective (fun n : ℕ => p * n) :=
      fun a b h => Nat.eq_of_mul_eq_mul_left hp.out.pos h
    rw [← hinj.hasSum_iff]
    · convert hV using 2 with n
      simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hp.out.pos]
      rw [mul_assoc]
      congr 2
      rw [pow_mul, ← RamanujanTau.Hecke.qP_mul]
    · intro m hm
      have : ¬ p ∣ m := fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩
      simp [this]
  have hsum := hU.add hV'
  simp only [smul_eq_mul]
  rw [coe_heckeT D, Pi.add_apply, add_comm]
  convert hsum using 2 with n
  ring

end RamanujanTau.TheoremA.GoodHecke
