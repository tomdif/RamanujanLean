import RamanujanTau.TheoremA.LevelSixCosets
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# A level-one product of the twelve level-six translates

The norm is constructed on actual modular forms. The finite coset certificate
proves invariance under S and T; all analytic and cusp conditions are retained.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelSix
open Matrix CongruenceSubgroup ModularGroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

variable {k : ℤ}

lemma translate_invariant (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (g : SL(2, ℤ)) (σ : Equiv.Perm (Fin 12))
    (h : ∀ i, rep i * g * (rep (σ i))⁻¹ ∈ Gamma0 6) (i : Fin 12) :
    ((f : ℍ → ℂ) ∣[k] rep i) ∣[k] g = (f : ℍ → ℂ) ∣[k] rep (σ i) := by
  rw [← SlashAction.slash_mul]
  have he : rep i * g = (rep i * g * (rep (σ i))⁻¹) * rep (σ i) := by group
  rw [he, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨_, h i, rfl⟩

noncomputable def normFunction (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∏ i : Fin 12, f ∣[k] rep i

lemma norm_invariant (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (g : SL(2, ℤ)) (σ : Equiv.Perm (Fin 12))
    (h : ∀ i, rep i * g * (rep (σ i))⁻¹ ∈ Gamma0 6) :
    normFunction k f ∣[k * 12] g = normFunction k f := by
  unfold normFunction
  have hp := ModularForm.prod_slash (k := k) (g := (g : GL (Fin 2) ℝ))
    (f := fun i : Fin 12 => (f : ℍ → ℂ) ∣[k] rep i) (s := Finset.univ)
  have hp' : (∏ i : Fin 12, (f : ℍ → ℂ) ∣[k] rep i) ∣[k * 12] g =
      ∏ i : Fin 12, ((f : ℍ → ℂ) ∣[k] rep i) ∣[k] g := by simpa using hp
  rw [hp']
  simp_rw [translate_invariant f g σ h]
  exact Equiv.prod_comp σ (fun i : Fin 12 => (f : ℍ → ℂ) ∣[k] rep i)

lemma norm_SL_invariant (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (g : SL(2, ℤ)) : normFunction k f ∣[k * 12] g = normFunction k f :=
  SlashInvariantForm.slash_action_generators_SL2Z
    (norm_invariant f S permS correctionS_mem)
    (norm_invariant f T permT correctionT_mem) g

lemma translate_bdd (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (g : SL(2, ℤ)) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] g) := by
  have hc : IsCusp ((g : GL (Fin 2) ℝ) • (OnePoint.infty : OnePoint ℝ))
      (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact IsCusp.smul_of_mem (by infer_instance : Fact (IsCusp OnePoint.infty 𝒮ℒ)).out ⟨g, rfl⟩
  exact ModularFormClass.bdd_at_cusps f hc _ rfl

/-- The product is an actual level-one modular form of twelve times the weight. -/
noncomputable def norm (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm 𝒮ℒ (k * 12) where
  toFun := normFunction k f
  slash_action_eq' g hg := by
    obtain ⟨g, rfl⟩ := hg
    exact norm_SL_invariant f g
  holo' := by
    change MDiff (∏ i : Fin 12, (f : ℍ → ℂ) ∣[k] rep i)
    exact .prod fun i _ => (ModularFormClass.holo f).slash k (rep i)
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro g _
    rw [norm_SL_invariant]
    have hb : (fun z : ℍ => ∏ i : Fin 12, ((f : ℍ → ℂ) ∣[k] rep i) z)
        =O[atImInfty] (fun _ : ℍ => ∏ _i : Fin 12, (1 : ℝ)) :=
      Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun i _ => translate_bdd f (rep i))
    simpa only [Finset.prod_const_one] using hb

/-- The norm detects zero: its factors are holomorphic translates of one form. -/
theorem norm_eq_zero_iff (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    norm f = 0 ↔ f = 0 := by
  rw [← DFunLike.coe_injective.eq_iff]
  change normFunction k f = 0 ↔ f = 0
  unfold normFunction
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin 12)), MDiff ((f : ℍ → ℂ) ∣[k] rep i) :=
    fun i _ => (ModularFormClass.holo f).slash k (rep i)
  rw [UpperHalfPlane.prod_eq_zero_iff hh]
  simp [SlashAction.slash_eq_zero_iff, ModularForm.coe_eq_zero_iff]

end RamanujanTau.TheoremA.LevelSix
