import RamanujanTau.TheoremA.BadPrimeQExpansion

/-!
# Bad-prime operators on the full modular-form space

The same rational cosets preserve boundedness at every cusp. This extends
coefficient extraction from cusp forms to actual modular forms, for every
integral weight and every prime dividing the level. It is needed for the
weight-six obstruction on the full integral model.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.BadPrime
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Finset Complex Filter
open scoped MatrixGroups ModularForm Manifold
local notation "𝕢" => Function.Periodic.qParam

variable {p N : ℕ} [hp : Fact p.Prime] {k : ℤ}

theorem slashU_modular_invariant (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    slashU p k f ∣[k] SpecialLinearGroup.mapGL ℝ γ = slashU p k f := by
  classical
  unfold slashU
  rw [SlashAction.sum_slash]
  have he : ∀ j : ZMod p,
      ((f : ℍ → ℂ) ∣[k] realRep p j) ∣[k] SpecialLinearGroup.mapGL ℝ γ =
        (f : ℍ → ℂ) ∣[k] realRep p (perm hN γ hγ j) := by
    intro j
    rw [← SlashAction.slash_mul, realRep_mul hN γ hγ]
    have hc : SpecialLinearGroup.mapGL ℝ (correction hN γ hγ j) ∈
        (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := ⟨_, correction_mem hN γ hγ j, rfl⟩
    rw [SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ hc]
  simp_rw [he]
  exact Equiv.sum_comp (perm hN γ hγ) (fun j : ZMod p => (f : ℍ → ℂ) ∣[k] realRep p j)

/-- The actual bad-prime operator preserves the full modular-form space. -/
noncomputable def modularU [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := slashU p k f
  slash_action_eq' γ hγ := by
    obtain ⟨γ, hγ, rfl⟩ := hγ
    exact slashU_modular_invariant hN f γ hγ
  holo' := .sum fun j _ => (ModularFormClass.holo f).slash k (realRep p j)
  bdd_at_cusps' {c} hc γ hγ := by
    have hj : ∀ j : ZMod p, OnePoint.IsBoundedAt c ((f : ℍ → ℂ) ∣[k] realRep p j) k := by
      intro j
      apply OnePoint.IsBoundedAt.smul_iff.mp
      exact ModularFormClass.bdd_at_cusps f (isCusp_rational_smul hc (rationalRep p j))
    change IsBoundedAtImInfty ((∑ j : ZMod p, (f : ℍ → ℂ) ∣[k] realRep p j) ∣[k] γ)
    rw [SlashAction.sum_slash]
    simpa [Finset.sum_fn] using Asymptotics.IsBigO.sum (s := Finset.univ) (fun j _ => hj j γ hγ)

@[simp] theorem modularU_apply [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    modularU hN f z = slashU p k f z := rfl

theorem modularU_eq_average [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    modularU hN f z = (p : ℂ)⁻¹ * ∑ j ∈ range p, f (ofComplex (((z : ℂ) + j) / p)) := by
  simp only [modularU_apply, slashU, Finset.sum_apply, realRep_slash]
  rw [← mul_sum, sum_zmod_val (fun j => f (ofComplex (((z : ℂ) + j) / p)))]

lemma hasSum_modular_Gamma0 [NeZero N]
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 w ^ n) (f (ofComplex w)) := by
  have h := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_period)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (ofComplex w)
  rw [ofComplex_apply_of_im_pos hw] at h ⊢
  simpa [smul_eq_mul] using h

/-- Fourier summation for the actual operator; no modularity or truncation input is assumed. -/
theorem hasSum_modularU [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    HasSum (fun m => (qExpansion 1 f).coeff (p * m) * 𝕢 1 z ^ m) (modularU hN f z) := by
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
  rw [modularU_eq_average]
  convert h0.mul_left (p : ℂ)⁻¹ using 1
  funext m
  field_simp

/-- **The analytic bad-prime Hecke operator is coefficient extraction.** -/
theorem qExpansion_modularU [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (modularU hN f) = BoylanWebb.U p (qExpansion 1 f) := by
  ext m
  rw [BoylanWebb.coeff_U]
  exact (ModularFormClass.qExpansion_coeff_unique (f := modularU hN f)
    (c := fun m => (qExpansion 1 f).coeff (p * m)) one_pos one_period
    (fun z => by simpa [smul_eq_mul] using hasSum_modularU hN f z) m).symm

/-- The bad-prime operator as a complex-linear endomorphism of the actual modular space. -/
noncomputable def modularULinear [NeZero N] (hN : p ∣ N) :
    Module.End ℂ (ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) where
  toFun := modularU hN
  map_add' f g := by
    ext z
    change modularU hN (f + g) z = modularU hN f z + modularU hN g z
    simp only [modularU_eq_average, ModularForm.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext z
    change modularU hN (c • f) z = c • modularU hN f z
    rw [modularU_eq_average, modularU_eq_average]
    simp [← Finset.mul_sum, mul_left_comm]

@[simp] theorem modularULinear_apply [NeZero N] (hN : p ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    modularULinear hN f = modularU hN f := rfl

/-- q-expansion is a linear map on the actual modular space. -/
noncomputable def modularExpansionLinear (N : ℕ) (k : ℤ) :
    ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 f
  map_add' f g := by
    exact ModularFormClass.qExpansion_add one_pos one_period f g
  map_smul' c f := by
    exact ModularFormClass.qExpansion_smul one_pos one_period c f

/-- The analytic and formal operators intertwine without a missing identification hypothesis. -/
theorem modularU_intertwines [NeZero N] (hN : p ∣ N) :
    (modularExpansionLinear N k).comp (modularULinear hN) =
      (uOperator p).comp (modularExpansionLinear N k) := by
  ext f n
  exact congrArg (PowerSeries.coeff n) (qExpansion_modularU hN f)

/-- Equality of the full q-expansions detects equality of actual modular forms. -/
theorem modularExpansionLinear_injective [NeZero N] :
    Function.Injective (modularExpansionLinear N k) := by
  intro f g hfg
  ext z
  have hf := hasSum_modular_Gamma0 f z.im_pos
  have hg := hasSum_modular_Gamma0 g z.im_pos
  change qExpansion 1 f = qExpansion 1 g at hfg
  rw [hfg] at hf
  simpa only [ofComplex_apply] using hf.unique hg

/-- The actual operators at primes dividing the level commute. -/
theorem modularU_commute {q : ℕ} [Fact q.Prime] [NeZero N]
    (hpN : p ∣ N) (hqN : q ∣ N)
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    modularU hpN (modularU hqN f) = modularU hqN (modularU hpN f) := by
  apply modularExpansionLinear_injective
  change qExpansion 1 _ = qExpansion 1 _
  simp only [qExpansion_modularU]
  ext n
  simp only [BoylanWebb.coeff_U]
  rw [Nat.mul_left_comm q p n]


end RamanujanTau.TheoremA.BadPrime
