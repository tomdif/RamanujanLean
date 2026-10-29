import RamanujanTau.TheoremA.BadPrimeCosets
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Bad-prime Hecke operators on actual cusp forms

For a prime dividing the level, the sum over `[1 j; 0 p]` preserves
Mathlib's `CuspForm (Γ₀(N)) k`, including vanishing at every cusp.
With Mathlib's slash normalization this is already the averaged translate
operator; its coefficient-extraction formula is proved separately.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.BadPrime
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Filter
open scoped MatrixGroups ModularForm Manifold Topology

variable {p N : ℕ} [hp : Fact p.Prime]

/-- Rational representatives let us transport vanishing at rational cusps. -/
noncomputable def rationalRep (p : ℕ) [Fact p.Prime] (j : ZMod p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' ((representative p j.val).map (Int.castRingHom ℚ)) (by
    have he : ((representative p j.val).map (Int.castRingHom ℚ)).det = (p : ℚ) := by
      simp [representative, Matrix.det_fin_two]
    rw [he]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

/-- The same representative acting on the upper half-plane. -/
noncomputable def realRep (p : ℕ) [Fact p.Prime] (j : ZMod p) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (rationalRep p j)

lemma realRep_val (j : ZMod p) :
    (realRep p j).val = (representative p j.val).map (Int.castRingHom ℝ) := by
  ext a b
  simp [realRep, rationalRep]

/-- The integral coset identity transported to the slash-action group. -/
lemma realRep_mul (hN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (j : ZMod p) :
    realRep p j * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ (correction hN γ hγ j) * realRep p (perm hN γ hγ j) := by
  apply Units.ext
  change (realRep p j).val * (SpecialLinearGroup.mapGL ℝ γ).val =
    (SpecialLinearGroup.mapGL ℝ (correction hN γ hγ j)).val *
      (realRep p (perm hN γ hγ j)).val
  rw [realRep_val, realRep_val]
  have he := congrArg (RingHom.mapMatrix (Int.castRingHom ℝ)) (representative_mul hN γ hγ j)
  simpa only [map_mul, RingHom.mapMatrix_apply] using he

/-- Rational matrices preserve the cusps of an arithmetic subgroup. -/
lemma isCusp_rational_smul {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (GeneralLinearGroup.map (algebraMap ℚ ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨r, rfl⟩ := hc
  refine ⟨g • r, ?_⟩
  simpa only [← Rat.coe_castHom, ← (Rat.castHom ℝ).algebraMap_toAlgebra]
    using OnePoint.map_smul (algebraMap ℚ ℝ) g r

variable {k : ℤ}

/-- The candidate `U_p` on functions, using the actual modular slash action. -/
noncomputable def slashU (p : ℕ) [Fact p.Prime] (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j : ZMod p, f ∣[k] realRep p j

theorem slashU_invariant (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
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

/-- **`U_p` preserves cusp forms on Γ₀(N) when `p ∣ N`.**
This constructs an actual Mathlib cusp form, with holomorphy and all cusp
conditions discharged; there are no modularity hypotheses left over. -/
noncomputable def cuspU [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := slashU p k f
  slash_action_eq' γ hγ := by
    obtain ⟨γ, hγ, rfl⟩ := hγ
    exact slashU_invariant hN f γ hγ
  holo' := by
    exact .sum fun j _ => (ModularFormClass.holo f).slash k (realRep p j)
  zero_at_cusps' {c} hc γ hγ := by
    have hj : ∀ j : ZMod p, OnePoint.IsZeroAt c ((f : ℍ → ℂ) ∣[k] realRep p j) k := by
      intro j
      apply OnePoint.IsZeroAt.smul_iff.mp
      exact CuspFormClass.zero_at_cusps f (isCusp_rational_smul hc (rationalRep p j))
    change IsZeroAtImInfty ((∑ j : ZMod p, (f : ℍ → ℂ) ∣[k] realRep p j) ∣[k] γ)
    rw [SlashAction.sum_slash]
    change Filter.Tendsto _ _ (nhds 0)
    simpa [Finset.sum_fn] using tendsto_finsetSum Finset.univ (fun j _ => hj j γ hγ)

@[simp] theorem cuspU_apply [NeZero N] (hN : p ∣ N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (z : ℍ) :
    cuspU hN f z = slashU p k f z := rfl

end RamanujanTau.TheoremA.BadPrime
