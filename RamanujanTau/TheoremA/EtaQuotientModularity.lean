import RamanujanTau.TheoremA.EtaGeneratorData

/-!
# Weight-six eta quotients on Γ₀(6)

Exact transformation laws for the three functions
η(z)^6η(3z)^6, η(2z)^6η(6z)^6, and
η(z)^4η(6z)^14 / (η(2z)^2η(3z)^4).
The finite word certificates imply invariance on the entire group.
Cuspidality and the required Fourier coefficients are separate obligations.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

lemma phase_mul (n r : ℤ) : phase (n * r) = phase n ^ r := by
  unfold phase
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma phase_sum {ι : Type*} (s : Finset ι) (n : ι → ℤ) :
    phase (∑ j ∈ s, n j) = ∏ j ∈ s, phase (n j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase_zero]
  | insert j s hj ih => simp [hj, phase_add, ih]

lemma zpow_sum_of_ne_zero {ι : Type*} (s : Finset ι) (r : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : z ^ (∑ j ∈ s, r j) = ∏ j ∈ s, z ^ r j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, zpow_add₀ hz, ih]

noncomputable def basisFunction (a : Fin 3) (z : ℍ) : ℂ :=
  ∏ j : Fin 4, scaledEta (dilation j) (dilation_pos j) z ^ basisExponent a j

theorem scaledEta_generator (b : Bool) (i : Fin 12) (j : Fin 4) :
    scaledEta (dilation j) (dilation_pos j) ∣[(1 : ℤ)] LevelSix.generator (b, i) =
      phase (wordExponent (generatorWord b i j)) •
        scaledEta (dilation j) (dilation_pos j) := by
  apply scaled_slash_of_rescale _ _ _ (dilation_dvd_generator b i j)
  rw [← generatorWord_matrix]
  exact slash_word _

theorem scaledEta_generator_apply (b : Bool) (i : Fin 12) (j : Fin 4) (z : ℍ) :
    scaledEta (dilation j) (dilation_pos j) (LevelSix.generator (b, i) • z) =
      phase (wordExponent (generatorWord b i j)) *
        scaledEta (dilation j) (dilation_pos j) z * denom (LevelSix.generator (b, i)) z := by
  have he := congrFun (scaledEta_generator b i j) z
  rw [SL_slash_apply] at he
  simpa only [neg_mul, mul_one, zpow_neg_one, Pi.smul_apply, smul_eq_mul,
    mul_inv_eq_iff_eq_mul₀ (denom_ne_zero _ _)] using he

theorem basisFunction_generator (a : Fin 3) (b : Bool) (i : Fin 12) :
    basisFunction a ∣[(6 : ℤ)] LevelSix.generator (b, i) = basisFunction a := by
  ext z
  rw [SL_slash_apply]
  simp only [basisFunction, scaledEta_generator_apply, mul_zpow, Finset.prod_mul_distrib]
  have hp : (∏ j : Fin 4, phase (wordExponent (generatorWord b i j)) ^ basisExponent a j) = 1 := by
    simp_rw [← phase_mul]
    rw [← phase_sum]
    exact phase_eq_one_of_dvd (generator_phase_dvd a b i)
  have hd := denom_ne_zero (LevelSix.generator (b, i)) z
  rw [hp, one_mul, ← zpow_sum_of_ne_zero _ _ hd, basisExponent_sum]
  rw [mul_assoc, ← zpow_add₀ hd]
  simp

/-- All three proposed basis functions have the actual weight-six Γ₀(6) transformation law. -/
theorem basisFunction_slash (a : Fin 3) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 6) :
    basisFunction a ∣[(6 : ℤ)] γ = basisFunction a :=
  LevelSix.slash_invariant_of_generators (basisFunction_generator a) γ hγ

theorem scaledEta_ne_zero (d : ℕ) (hd : 0 < d) (z : ℍ) : scaledEta d hd z ≠ 0 :=
  pow_ne_zero _ (eta_ne_zero (scale d hd z).im_pos)

theorem basisFunction_ne_zero (a : Fin 3) (z : ℍ) : basisFunction a z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact zpow_ne_zero _ (scaledEta_ne_zero _ _ _)

/-- These eta quotients are holomorphic everywhere in the upper half-plane. -/
theorem basisFunction_holo (a : Fin 3) : MDiff (basisFunction a) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  let F : ℂ → ℂ := fun z => ∏ j : Fin 4,
    (eta ((dilation j : ℂ) * z) ^ 2) ^ basisExponent a j
  have hF : DifferentiableOn ℂ F upperHalfPlaneSet := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.fun_finsetProd
    intro j _
    have hd : (dilation j : ℝ) > 0 := by exact_mod_cast dilation_pos j
    have hp : (dilation j : ℂ) * z ∈ upperHalfPlaneSet := by
      simpa using mul_pos hd hz
    exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hp).comp z
      (by fun_prop)).pow 2).zpow (Or.inl (pow_ne_zero _ (eta_ne_zero hp)))
  refine hF.congr fun z hz => ?_
  simp [F, basisFunction, scaledEta, etaSquared, scale, ofComplex_apply_of_im_pos hz]

noncomputable def basisSlashInvariant (a : Fin 3) :
    SlashInvariantForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6 where
  toFun := basisFunction a
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact basisFunction_slash a γ hγ

end RamanujanTau.TheoremA.EtaSquared
