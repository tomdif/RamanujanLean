/-
# The Hecke operator `T_p` on level-one cusp forms

Packages `HeckeCore.heckeFun` as an operator `CuspForm 𝒮ℒ k → CuspForm 𝒮ℒ k` for a prime `p`:
modularity (from the `S`/`T` computation and `slash_action_generators_SL2Z`), holomorphy (affine
reparametrizations of a holomorphic function), and vanishing at `i∞`.
-/
import RamanujanTau.HeckeCore

set_option autoImplicit false

namespace RamanujanTau.Hecke
open Complex UpperHalfPlane ModularForm Filter Finset
open scoped MatrixGroups ModularForm Topology Manifold

variable {k : ℤ}

/-- a level-one cusp form, read on `ℂ`, satisfies `IsModular`. -/
lemma isModular_of (f : CuspForm 𝒮ℒ k) : IsModular k (f ∘ ofComplex) := by
  intro a b c d hdet z hz
  let A : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two]; linarith⟩
  let τ : ℍ := ⟨z, hz⟩
  have hinv : (f : ℍ → ℂ) ∣[k] A = f := by
    have := SlashInvariantFormClass.slash_action_eq f (A : GL (Fin 2) ℝ) ⟨A, rfl⟩
    simpa [ModularForm.SL_slash] using this
  have h := congrFun hinv τ
  rw [SL_slash_apply] at h
  have hden : denom A τ = c * z + d := by simp [A, τ, UpperHalfPlane.denom]
  have hcoe : ((A • τ : ℍ) : ℂ) = (a * z + b) / (c * z + d) := by
    rw [coe_specialLinearGroup_apply]; simp [A, τ]
  have hne : (c : ℂ) * z + d ≠ 0 := hden ▸ denom_ne_zero A τ
  simp only [Function.comp_apply]
  rw [← hcoe, ofComplex_apply, show ofComplex z = τ from ofComplex_apply_of_im_pos hz]
  rw [hden] at h
  rw [← h, mul_left_comm, ← zpow_add₀ hne, add_neg_cancel, zpow_zero, mul_one]

variable (p : ℕ) [hp : Fact p.Prime]

/-- `T_p f` as a function on `ℍ`. -/
noncomputable def heckeH (f : CuspForm 𝒮ℒ k) (τ : ℍ) : ℂ := heckeFun k (f ∘ ofComplex) p τ

lemma heckeH_S (f : CuspForm 𝒮ℒ k) : heckeH p f ∣[k] ModularGroup.S = heckeH p f := by
  funext τ
  rw [SL_slash_apply, ModularGroup.denom_S, heckeH, heckeH, modular_S_smul]
  have hz : 0 < (τ : ℂ).im := τ.im_pos
  have e : ((mk (-(τ : ℂ))⁻¹ τ.im_inv_neg_coe_pos : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    simp [neg_div, inv_neg]
  rw [e, heckeFun_S (isModular_of f) hz]
  have hne : (τ : ℂ) ≠ 0 := ne_zero τ
  rw [mul_comm, ← mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, one_mul]

lemma heckeH_T (f : CuspForm 𝒮ℒ k) : heckeH p f ∣[k] ModularGroup.T = heckeH p f := by
  funext τ
  rw [SL_slash_apply, heckeH, heckeH, modular_T_smul]
  have hden : denom ModularGroup.T τ = 1 := by simp [ModularGroup.T, ModularGroup.denom_apply]
  rw [hden, one_zpow, mul_one, UpperHalfPlane.coe_vadd, ofReal_one, add_comm]
  exact heckeFun_add_one (isModular_of f) hp.out.pos τ.im_pos

lemma differentiableOn_g (f : CuspForm 𝒮ℒ k) :
    DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)

lemma heckeH_holo (f : CuspForm 𝒮ℒ k) : MDiff (heckeH p f) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hpos := hp.out.pos
  have hd : DifferentiableOn ℂ (heckeFun k (f ∘ ofComplex) p) {z : ℂ | 0 < z.im} := by
    unfold heckeFun
    refine (DifferentiableOn.const_mul ?_ _).add (DifferentiableOn.const_mul ?_ _)
    · exact (differentiableOn_g f).comp (by fun_prop) fun z hz => im_nat_mul hz hpos
    · refine DifferentiableOn.fun_sum fun j _ => ?_
      exact (differentiableOn_g f).comp (by fun_prop) fun z hz => im_div_nat hz hpos
  refine hd.congr fun z hz => ?_
  simp [heckeH, ofComplex_apply_of_im_pos (show 0 < z.im from hz)]

/-- maps `ℍ → ℍ` given by a complex function preserving the upper half plane and sending `im → ∞`. -/
lemma tendsto_comp {φ : ℂ → ℂ} (hφ : ∀ z : ℂ, 0 < z.im → 0 < (φ z).im) (c : ℝ) (hc : 0 < c)
    (him : ∀ z : ℂ, 0 < z.im → (φ z).im = c * z.im) :
    Tendsto (fun τ : ℍ => ofComplex (φ τ)) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ fun τ : ℍ => ofComplex (φ τ)) = fun τ => c * τ.im := by
    funext τ
    simp only [Function.comp_apply]
    rw [ofComplex_apply_of_im_pos (hφ _ τ.im_pos)]
    exact him _ τ.im_pos
  rw [this]
  exact (tendsto_comap.const_mul_atTop hc)

lemma heckeH_zero (f : CuspForm 𝒮ℒ k) : IsZeroAtImInfty (heckeH p f) := by
  have hpos := hp.out.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hpos
  have hf : Tendsto (f : ℍ → ℂ) atImInfty (𝓝 0) := by
    have := CuspFormClass.zero_at_infty f
    simpa [IsZeroAtImInfty, ZeroAtFilter] using this
  have h1 : Tendsto (fun τ : ℍ => f (ofComplex (p * (τ : ℂ)))) atImInfty (𝓝 0) :=
    hf.comp (tendsto_comp (fun z hz => im_nat_mul hz hpos) p hp' fun z _ => by simp)
  have h2 : ∀ j : ℕ, Tendsto (fun τ : ℍ => f (ofComplex (((τ : ℂ) + j) / p))) atImInfty (𝓝 0) :=
    fun j => hf.comp (tendsto_comp (fun z hz => im_div_nat hz hpos) (1 / p) (by positivity)
      fun z _ => by rw [div_natCast_im]; simp; ring)
  have := (h1.const_mul ((p : ℂ) ^ (k - 1))).add
    ((tendsto_finsetSum (range p) fun j _ => h2 j).const_mul ((p : ℂ)⁻¹))
  simpa [IsZeroAtImInfty, ZeroAtFilter, heckeH, heckeFun] using this

/-- **The Hecke operator `T_p`** on `CuspForm 𝒮ℒ k`. -/
noncomputable def heckeCusp (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k where
  toFun := heckeH p f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z (heckeH_S p f) (heckeH_T p f) A
  holo' := heckeH_holo p f
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z (heckeH_S p f) (heckeH_T p f)]
    exact heckeH_zero p f

lemma heckeCusp_apply (f : CuspForm 𝒮ℒ k) (τ : ℍ) : heckeCusp p f τ = heckeH p f τ := rfl

end RamanujanTau.Hecke
