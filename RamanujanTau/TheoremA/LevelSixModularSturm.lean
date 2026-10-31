import RamanujanTau.TheoremA.LevelSixSturm

/-!
# Finite determination of all level-six modular forms

The first k+1 coefficients determine a modular form of nonnegative integral
weight k on Γ₀(6). Unlike the cusp-form bound, this result includes nonzero
constant terms and requires only boundedness at the other cusps.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelSix
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm Manifold Real

theorem modular_norm_decay {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (m : ℕ) (hc : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    normFunction k f =O[atImInfty] (fun z : ℍ => Real.exp (-2 * π * z.im) ^ m) := by
  let r : Fin 12 → ℝ := fun i => if i = 0 then (m : ℝ) else 0
  have hi : ∀ i : Fin 12, ((f : ℍ → ℂ) ∣[k] rep i) =O[atImInfty]
      (fun z : ℍ => Real.exp ((-2 * π * z.im) * r i)) := by
    intro i
    by_cases hi : i = 0
    · subst i
      have he := decay_of_coeff_eq_zero (f := (f : ℍ → ℂ)) one_pos
        (SlashInvariantFormClass.periodic_comp_ofComplex f infinity_period)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) m hc
      simpa [r, rep, ← Real.exp_nat_mul, mul_comm] using he
    · simpa only [r, if_neg hi, mul_zero, Real.exp_zero] using translate_bdd f (rep i)
  have hp := IsBigO.finsetProd (s := Finset.univ) (fun i _ => hi i)
  have hr : ∑ i : Fin 12, r i = m := by simp [r]
  have he : (fun z : ℍ => ∏ i : Fin 12, Real.exp ((-2 * π * z.im) * r i)) =
      (fun z : ℍ => Real.exp (-2 * π * z.im) ^ m) := by
    funext z
    rw [← Real.exp_sum, ← Finset.mul_sum, hr, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hp
  exact hp

/-- A level-six modular form of weight k cannot vanish to order greater than k. -/
theorem modular_eq_zero_of_coeff_eq_zero {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (m : ℕ) (hk : k < m) (hc : ∀ n < m, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  let F := norm f
  let G := discriminantPower m
  have hG : ∀ z, G z ≠ 0 := by
    intro z
    change discriminantPower m z ≠ 0
    rw [discriminantPower_apply]
    exact pow_ne_zero _ (discriminant_ne_zero z)
  have hFG : (F : ℍ → ℂ) =O[atImInfty] (G : ℍ → ℂ) := by
    simpa only [G, show (discriminantPower m : ℍ → ℂ) =
      (fun z => discriminant z ^ m) from funext (discriminantPower_apply _)]
      using (modular_norm_decay f m hc).trans (exp_isBigO_discriminant.pow m)
  have hzero : quotientOfBound F G hG hFG = 0 :=
    ModularForm.isZero_of_neg_weight (by omega) _
  have hF : F = 0 := by
    ext z
    have he := congrArg (fun H => H z) hzero
    simpa only [quotientOfBound_apply, ModularForm.zero_apply,
      div_eq_zero_iff, or_iff_left (hG z)] using he
  exact (norm_eq_zero_iff f).mp hF

/-- The complete q-expansion of an actual level-six modular form. -/
noncomputable def modularExpansionLinear (k : ℤ) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 f
  map_add' f g := by
    rw [ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos infinity_period]
  map_smul' c f := by
    rw [ModularForm.IsGLPos.coe_smul, ModularFormClass.qExpansion_smul one_pos infinity_period]
    rfl

/-- All coefficients through degree k, including the constant term. -/
noncomputable def firstCoefficients (k : ℕ) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun f n := (qExpansion 1 f).coeff n.val
  map_add' f g := by
    funext n
    rw [ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos infinity_period]
    rfl
  map_smul' c f := by
    funext n
    rw [ModularForm.IsGLPos.coe_smul, ModularFormClass.qExpansion_smul one_pos infinity_period]
    rfl

theorem firstCoefficients_injective (k : ℕ) : Function.Injective (firstCoefficients k) := by
  intro f g he
  have hz : f - g = 0 := modular_eq_zero_of_coeff_eq_zero (f - g) (k + 1)
    (by omega) (by
      intro n hn
      change firstCoefficients k (f - g) ⟨n, hn⟩ = 0
      rw [map_sub, he]
      simp)
  exact sub_eq_zero.mp hz

instance (k : ℕ) : FiniteDimensional ℂ
    (ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :=
  FiniteDimensional.of_injective (firstCoefficients k) (firstCoefficients_injective k)

theorem modular_finrank_le (k : ℕ) :
    Module.finrank ℂ (ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) ≤ k + 1 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (firstCoefficients_injective k)

end RamanujanTau.TheoremA.LevelSix
