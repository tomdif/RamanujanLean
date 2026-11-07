import RamanujanTau.TheoremA.LevelSixDecay
import RamanujanTau.TheoremA.BadPrimeQExpansion
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite determination of actual level-six cusp forms

A cusp form of integral weight k on Γ₀(6) vanishes if its q-expansion
vanishes below m and k < m+3. In particular, the first three positive
coefficients determine every weight-six cusp form.

The proof uses the twelve-translate norm, all four cusp contributions, and
division by a power of the nonvanishing discriminant. It assumes neither
a dimension formula nor an eta-product basis.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelSix
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm Manifold

noncomputable def discriminantPower (n : ℕ) : ModularForm 𝒮ℒ (12 * n) :=
  ModularForm.prod (s := (Finset.univ : Finset (Fin n))) (12 * n)
    (k := fun _ => 12) (by simp [mul_comm])
    (fun _ => ModularFormClass.modularForm CuspForm.discriminant)

@[simp] theorem discriminantPower_apply (n : ℕ) (z : ℍ) :
    discriminantPower n z = discriminant z ^ n := by
  change (∏ _i : Fin n, (discriminant : ℍ → ℂ)) z = _
  simp

/-- A quotient with no interior poles and a bounded quotient at infinity
is a genuine level-one modular form of the difference of the weights. -/
noncomputable def quotientOfBound {k l : ℤ} (f : ModularForm 𝒮ℒ k)
    (g : ModularForm 𝒮ℒ l) (hg : ∀ z, g z ≠ 0)
    (hfg : (f : ℍ → ℂ) =O[atImInfty] (g : ℍ → ℂ)) : ModularForm 𝒮ℒ (k - l) := by
  have hinv : ∀ γ : SL(2, ℤ), (⇑f / ⇑g) ∣[k - l] γ = ⇑f / ⇑g := by
    intro γ
    have hfγ : (f : ℍ → ℂ) ∣[k] γ = f :=
      SlashInvariantFormClass.slash_action_eq f (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
    have hgγ : (g : ℍ → ℂ) ∣[l] γ = g :=
      SlashInvariantFormClass.slash_action_eq g (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
    rw [div_slash_SL2, hfγ, hgγ]
  exact
    { toFun := fun z => f z / g z
      slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ hinv γ
      holo' := (ModularFormClass.holo f).div (ModularFormClass.holo g) hg
      bdd_at_cusps' := by
        intro c hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        change IsBoundedAtImInfty ((⇑f / ⇑g) ∣[k - l] γ)
        rw [hinv]
        exact (div_isBoundedUnder_of_isBigO hfg).isBigO_one ℝ }

@[simp] theorem quotientOfBound_apply {k l : ℤ} (f : ModularForm 𝒮ℒ k)
    (g : ModularForm 𝒮ℒ l) (hg : ∀ z, g z ≠ 0)
    (hfg : (f : ℍ → ℂ) =O[atImInfty] (g : ℍ → ℂ)) (z : ℍ) :
    quotientOfBound f g hg hfg z = f z / g z := rfl

/-- The cusp improvement of the level-six coefficient bound. -/
theorem cusp_eq_zero_of_coeff_eq_zero {k : ℤ}
    (f : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (m : ℕ) (hk : k < (m : ℤ) + 3)
    (hc : ∀ n < m, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  let F := norm (ModularFormClass.modularForm f)
  let G := discriminantPower (m + 3)
  have hG : ∀ z, G z ≠ 0 := by
    intro z
    change discriminantPower (m + 3) z ≠ 0
    rw [discriminantPower_apply]
    exact pow_ne_zero _ (discriminant_ne_zero z)
  have hFG : (F : ℍ → ℂ) =O[atImInfty] (G : ℍ → ℂ) := by
    simpa only [G, show (discriminantPower (m + 3) : ℍ → ℂ) =
      (fun z => discriminant z ^ (m + 3)) from funext (discriminantPower_apply _)]
      using norm_isBigO_discriminant_pow f m hc
  have hzero : quotientOfBound F G hG hFG = 0 :=
    ModularForm.isZero_of_neg_weight (by push_cast; omega) _
  have hF : F = 0 := by
    ext z
    have he := congrArg (fun H => H z) hzero
    simpa only [quotientOfBound_apply, ModularForm.zero_apply,
      div_eq_zero_iff, or_iff_left (hG z)] using he
  have hf := (norm_eq_zero_iff (ModularFormClass.modularForm f)).mp hF
  ext z
  exact congrArg (fun H => H z) hf

theorem weightSix_eq_zero_of_first_three
    (f : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6)
    (hc : ∀ n : Fin 3, (qExpansion 1 f).coeff (n.val + 1) = 0) : f = 0 := by
  apply cusp_eq_zero_of_coeff_eq_zero f 4 (by norm_num)
  intro n hn
  rcases n with _ | n
  · simp only [qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul, iteratedDeriv_zero]
    exact CuspFormClass.cuspFunction_apply_zero f one_pos infinity_period
  · exact hc ⟨n, by omega⟩

/-- Three actual Fourier coefficients, as a complex-linear map. -/
noncomputable def firstThree :
    CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6 →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun f n := (qExpansion 1 f).coeff (n.val + 1)
  map_add' f g := by
    funext n
    rw [CuspForm.coe_add, ModularFormClass.qExpansion_add one_pos infinity_period]
    rfl
  map_smul' c f := by
    funext n
    rw [CuspForm.IsGLPos.coe_smul, ModularFormClass.qExpansion_smul one_pos infinity_period]
    rfl

theorem firstThree_injective : Function.Injective firstThree := by
  intro f g he
  have hz : f - g = 0 := weightSix_eq_zero_of_first_three (f - g) (by
    intro n
    change firstThree (f - g) n = 0
    rw [map_sub, he]
    simp)
  exact sub_eq_zero.mp hz

instance : FiniteDimensional ℂ (CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6) :=
  FiniteDimensional.of_injective firstThree firstThree_injective

theorem weightSix_finrank_le_three :
    Module.finrank ℂ (CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6) ≤ 3 := by
  simpa using LinearMap.finrank_le_finrank_of_injective firstThree_injective

end RamanujanTau.TheoremA.LevelSix
