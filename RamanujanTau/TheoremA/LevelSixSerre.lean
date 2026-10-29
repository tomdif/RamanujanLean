import RamanujanTau.TheoremA.LevelSixModularSturm
import RamanujanTau.RamanujanODE.Main
import Mathlib.Analysis.Complex.Liouville

/-!
# The actual Serre derivative at level six

Cauchy's estimate shows that a holomorphic function bounded at infinity
has bounded derivative there. Slash-equivariance then proves every cusp
condition for the Serre derivative of an actual level-six modular form.
The scaled operator 12∂ has the integral q-expansion formula 12θ - kE₂.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup Derivative RamanujanODEProof Filter
open UpperHalfPlane hiding I
open Complex hiding eta
open scoped MatrixGroups ModularForm Manifold Real

theorem derivative_bdd_at_infty {f : ℍ → ℂ} (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) : IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hb ⊢
  obtain ⟨M, A, hM⟩ := hb
  refine ⟨‖(2 * π * I : ℂ)⁻¹‖ * M, max A 0 + 2, fun z hz => ?_⟩
  have hheight (w : ℂ) (hw : w ∈ Metric.closedBall (z : ℂ) 1) : 0 < w.im ∧ A ≤ w.im := by
    have hdist : ‖w - (z : ℂ)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hi := (abs_le.mp ((abs_im_le_norm (w - (z : ℂ))).trans hdist)).1
    simp only [sub_im, UpperHalfPlane.coe_im] at hi
    constructor <;> linarith [le_max_left A 0, le_max_right A 0]
  have hhol := UpperHalfPlane.mdifferentiable_iff.mp hf
  have hd : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) 1) :=
    hhol.diffContOnCl_ball (fun w hw => (hheight w hw).1)
  have hder : ‖deriv (f ∘ ofComplex) (z : ℂ)‖ ≤ M := by
    simpa only [div_one] using norm_deriv_le_of_forall_mem_sphere_norm_le
      (one_pos : (0 : ℝ) < 1) hd (fun w hw => by
        have h := hheight w (Metric.sphere_subset_closedBall hw)
        simpa only [Function.comp_apply, ofComplex_apply_of_im_pos h.1] using hM ⟨w, h.1⟩ h.2)
  simpa only [normalizedDerivOfComplex, norm_mul] using
    mul_le_mul_of_nonneg_left hder (norm_nonneg ((2 * π * I : ℂ)⁻¹))

theorem serre_bdd_at_infty (k : ℂ) {f : ℍ → ℂ} (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serreDerivative k f) := by
  rw [serre_eq]
  exact (derivative_bdd_at_infty hf hb).add
    ((isQSeries_E2.isBoundedAtImInfty.mul hb).smul _).neg

namespace LevelSix

/-- The actual Serre derivative preserves level six and raises the weight by two. -/
noncomputable def serreForm {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (k + 2) where
  toFun := serreDerivative k f
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    apply serre_slash_invariant k f (ModularFormClass.holo f) γ
    exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩
  holo' := serreDerivative_mdifferentiable _ (ModularFormClass.holo f)
  bdd_at_cusps' h := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at h
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z h]
    intro γ _
    rw [serre_slash_equivariant k f (ModularFormClass.holo f) γ]
    exact serre_bdd_at_infty k ((ModularFormClass.holo f).slash k γ) (translate_bdd f γ)

@[simp] theorem serreForm_apply {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    serreForm f z = serreDerivative k f z := rfl

lemma isQSeries_modularForm {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    IsQSeries f (fun n => (qExpansion 1 f).coeff n) := fun z =>
  hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f infinity_period)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) z

theorem qExpansion_serreForm {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (serreForm f) = Igusa.theta (qExpansion 1 f) -
      ((k : ℂ) * 12⁻¹) • (Igusa.E2 ℂ * qExpansion 1 f) := by
  have he : PowerSeries.mk (fun n => (qExpansion 1 f).coeff n) = qExpansion 1 f := by
    ext n
    rw [PowerSeries.coeff_mk]
  simpa only [he] using
    qExpansion_serre (k : ℂ) (isQSeries_modularForm f) (ModularFormClass.holo f)

noncomputable def integralSerreForm {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (k + 2) :=
  (12 : ℂ) • serreForm f

theorem qExpansion_integralSerreForm {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (integralSerreForm f) =
      (12 : ℂ) • Igusa.theta (qExpansion 1 f) - (k : ℂ) • (Igusa.E2 ℂ * qExpansion 1 f) := by
  rw [integralSerreForm, ModularForm.IsGLPos.coe_smul,
    ModularFormClass.qExpansion_smul one_pos infinity_period, qExpansion_serreForm,
    smul_sub, smul_smul]
  congr 1
  congr 1
  ring

end LevelSix
end RamanujanTau.TheoremA
