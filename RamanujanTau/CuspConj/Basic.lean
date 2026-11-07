/-
# The conjugate cusp form `f^ρ(z) = conj f(−z̄)`

For `f ∈ S_k(SL₂(ℤ))`:
* `cuspConj f : CuspForm 𝒮ℒ k`, `cuspConj f z = conj (f (−z̄))`;
* `coef_cuspConj : coef (cuspConj f) n = conj (coef f n)`.

Invariance: `−conj(γz) = γ'(−z̄)` with `γ' = [[a,−b],[−c,d]] ∈ SL₂(ℤ)` (conjugation by
`diag(−1,1)`), and `−c(−z̄) + d = conj(cz+d)`.  Holomorphy: `conj ∘ F ∘ conj`
(`DifferentiableAt.conj_conj`).  Cusps: `|f^ρ(z)| = |f(−z̄)|`, `Im(−z̄) = Im z`.
Coefficients: `conj(q(−z̄)) = q(z)` and `ModularFormClass.qExpansion_coeff_unique`.
-/
import RamanujanTau.SubconvexGeneral.TwoPointF

set_option autoImplicit false

namespace RamanujanTau.CuspConj

open Complex ModularForm Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real Manifold
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral RamanujanTau.SCSProof

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℕ}

/-- The reflection `z ↦ −z̄` of `ℍ`. -/
def refl (z : ℍ) : ℍ := ⟨-conj (z : ℂ), by simpa using z.im_pos⟩

lemma refl_coe (z : ℍ) : ((refl z : ℍ) : ℂ) = -conj (z : ℂ) := rfl

lemma refl_im (z : ℍ) : (refl z).im = z.im := by
  show (-conj (z : ℂ)).im = z.im; simp

/-- `γ' = [[a,−b],[−c,d]]`. -/
def gConj (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]; linarith⟩

lemma refl_smul (γ : SL(2, ℤ)) (z : ℍ) : refl (γ • z) = gConj γ • refl z := by
  apply UpperHalfPlane.ext
  rw [refl_coe, coe_smul_sl, coe_smul_sl, refl_coe]
  have hz := denom_ne_zero' γ z
  have hz' : conj ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := (map_ne_zero _).2 hz
  simp only [gConj, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, Int.cast_neg]
  simp only [map_add, map_mul, map_intCast] at hz'
  rw [map_div₀]
  simp only [map_add, map_mul, map_intCast]
  have hd : -(γ 1 0 : ℂ) * -conj (z : ℂ) + γ 1 1 = (γ 1 0 : ℂ) * conj (z : ℂ) + γ 1 1 := by ring
  rw [hd]
  field_simp
  ring

/-- The underlying function `z ↦ conj f(−z̄)`. -/
noncomputable def conjFun (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℍ) : ℂ := conj (f (refl z))

lemma conjFun_smul (f : CuspForm 𝒮ℒ (k : ℤ)) (γ : SL(2, ℤ)) (z : ℍ) :
    conjFun f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * conjFun f z := by
  unfold conjFun
  rw [refl_smul, f_smul]
  simp only [gConj, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, Int.cast_neg, refl_coe, map_mul, map_pow,
    map_add, map_neg, map_intCast, Complex.conj_conj]
  ring

lemma conjFun_slash (f : CuspForm 𝒮ℒ (k : ℤ)) (γ : SL(2, ℤ)) :
    conjFun f ∣[(k : ℤ)] γ = conjFun f := by
  funext z
  rw [SL_slash_apply, conjFun_smul, mul_comm, ← mul_assoc]
  have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have e : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z = (γ 1 0 : ℂ) * z + γ 1 1 := by
    simp [UpperHalfPlane.denom]
  rw [e] at h ⊢
  rw [← zpow_natCast, ← zpow_add₀ h]
  simp

lemma mdiff_conjFun (f : CuspForm 𝒮ℒ (k : ℤ)) : MDiff (conjFun f) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hF := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  set F := (f : ℍ → ℂ) ∘ ofComplex
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hD : DifferentiableOn ℂ (fun z => conj (F (-conj z))) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < (-conj z).im := by simpa using hz
    have hFa : DifferentiableAt ℂ F (-conj z) :=
      (hF _ hz').differentiableAt (hopen.mem_nhds hz')
    have hG : DifferentiableAt ℂ (fun u => F (-u)) (conj z) := by
      have : DifferentiableAt ℂ (fun u : ℂ => -u) (conj z) := differentiableAt_id.neg
      exact hFa.comp (conj z) this
    have := hG.conj_conj
    rw [Complex.conj_conj] at this
    have h2 : (fun z => conj (F (-conj z))) =
        (starRingEnd ℂ ∘ (fun u => F (-u)) ∘ starRingEnd ℂ) := rfl
    rw [h2]
    exact this.differentiableWithinAt
  refine hD.congr fun z hz => ?_
  have hz' : 0 < (-conj z).im := by simpa using hz
  simp only [Function.comp, conjFun, F]
  congr 2
  rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
  rfl

lemma isZeroAtImInfty_conjFun (f : CuspForm 𝒮ℒ (k : ℤ)) : IsZeroAtImInfty (conjFun f) := by
  have hf := CuspFormClass.zero_at_infty f
  rw [isZeroAtImInfty_iff] at hf ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := hf ε hε
  refine ⟨A, fun z hz => ?_⟩
  have := hA (refl z) (by rw [refl_im]; exact hz)
  simpa [conjFun] using this

/-- **The conjugate cusp form** `f^ρ(z) = conj f(−z̄)`. -/
noncomputable def cuspConj (f : CuspForm 𝒮ℒ (k : ℤ)) : CuspForm 𝒮ℒ (k : ℤ) where
  toFun := conjFun f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact conjFun_slash f A
  holo' := mdiff_conjFun f
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [conjFun_slash f γ]
    exact isZeroAtImInfty_conjFun f

lemma cuspConj_apply (f : CuspForm 𝒮ℒ (k : ℤ)) (z : ℍ) :
    cuspConj f z = conj (f (refl z)) := rfl

/-! ### Coefficients -/

lemma hasSum_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℍ) :
    HasSum (fun m => coef f m • 𝕢 1 (w : ℂ) ^ m) (f w) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  exact hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) w

lemma coef_eq_of_hasSum (f : CuspForm 𝒮ℒ (k : ℤ)) {c : ℕ → ℂ}
    (hc : ∀ w : ℍ, HasSum (fun m => c m • 𝕢 1 (w : ℂ) ^ m) (f w)) (m : ℕ) : coef f m = c m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL hc m).symm

lemma conj_qParam_refl (w : ℍ) : conj (𝕢 1 ((refl w : ℍ) : ℂ)) = 𝕢 1 (w : ℂ) := by
  rw [qParam_one, qParam_one, refl_coe, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_conj, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **`a_{f^ρ}(n) = conj a_f(n)`.** -/
theorem coef_cuspConj (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) :
    coef (cuspConj f) n = conj (coef f n) := by
  refine coef_eq_of_hasSum (cuspConj f) (c := fun n => conj (coef f n)) (fun w => ?_) n
  have h := hasSum_conj'.mpr (hasSum_coef f (refl w))
  rw [cuspConj_apply]
  refine h.congr_fun fun m => ?_
  simp only [smul_eq_mul, map_mul, map_pow, conj_qParam_refl]

end RamanujanTau.CuspConj
