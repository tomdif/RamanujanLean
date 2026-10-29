import RamanujanTau.TheoremA.LevelSixNorm
import RamanujanTau.TheoremA.CoefficientDecay
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Decay of the level-six norm

The three cusp blocks other than infinity contribute three full powers of q.
Vanishing through q^(m-1) at infinity therefore gives norm decay of order m+3.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.LevelSix
open Matrix CongruenceSubgroup ModularGroup ModularForm UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm Manifold Pointwise Real

lemma upperRight_eq_T_pow (n : ℕ) :
    GeneralLinearGroup.upperRightHom (n : ℝ) = SpecialLinearGroup.mapGL ℝ (T ^ n) := by
  have hv : (T ^ n : SL(2, ℤ)).val = !![1, (n : ℤ); 0, 1] := by
    simpa only [zpow_natCast] using coe_T_zpow (n : ℤ)
  apply Units.ext
  ext i j
  change !![1, (n : ℝ); 0, 1] i j = (((T ^ n : SL(2, ℤ)).val i j : ℤ) : ℝ)
  rw [hv]
  fin_cases i <;> fin_cases j <;> simp

lemma translate_period (i : Fin 12) : (width i : ℝ) ∈
    (ConjAct.toConjAct (rep i : GL (Fin 2) ℝ)⁻¹ •
      (Gamma0 6 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, upperRight_eq_T_pow,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  refine ⟨rep i * T ^ width i * (rep i)⁻¹, period_mem i, ?_⟩
  simp only [map_mul, map_inv, map_pow]
  rfl

variable {k : ℤ}

theorem translate_decay (f : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (i : Fin 12) : ((f : ℍ → ℂ) ∣[k] rep i) =O[atImInfty]
      (fun z : ℍ => Real.exp (-2 * π * z.im / width i)) := by
  exact CuspFormClass.exp_decay_atImInfty (CuspForm.translate f (rep i))
    (by exact_mod_cast width_pos i) (translate_period i)

lemma infinity_period : (1 : ℝ) ∈ (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp [strictPeriods_Gamma0]

theorem norm_decay (f : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (m : ℕ) (hc : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    normFunction k f =O[atImInfty]
      (fun z : ℍ => Real.exp (-2 * π * z.im) ^ (m + 3)) := by
  let r : Fin 12 → ℝ := fun i => if i = 0 then (m : ℝ) else (width i : ℝ)⁻¹
  have hi : ∀ i : Fin 12, ((f : ℍ → ℂ) ∣[k] rep i) =O[atImInfty]
      (fun z : ℍ => Real.exp ((-2 * π * z.im) * r i)) := by
    intro i
    by_cases hi : i = 0
    · subst i
      have he := decay_of_coeff_eq_zero (f := (f : ℍ → ℂ)) one_pos
        (SlashInvariantFormClass.periodic_comp_ofComplex f infinity_period)
        (ModularFormClass.holo f) (CuspFormClass.zero_at_infty f).isBoundedAtImInfty m hc
      simpa [r, rep, ← Real.exp_nat_mul, mul_comm] using he
    · simpa [r, hi, div_eq_mul_inv] using translate_decay f i
  have hp := IsBigO.finsetProd (s := Finset.univ) (fun i _ => hi i)
  have hr : ∑ i : Fin 12, r i = m + 3 := by
    norm_num [r, width, Fin.sum_univ_succ]
  have he : (fun z : ℍ => ∏ i : Fin 12, Real.exp ((-2 * π * z.im) * r i)) =
      (fun z : ℍ => Real.exp (-2 * π * z.im) ^ (m + 3)) := by
    funext z
    rw [← Real.exp_sum, ← Finset.mul_sum, hr, ← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  rw [he] at hp
  exact hp

/-- The same estimate expressed using the nonvanishing discriminant. -/
theorem norm_isBigO_discriminant_pow
    (f : CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k)
    (m : ℕ) (hc : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    normFunction k f =O[atImInfty] (fun z : ℍ => discriminant z ^ (m + 3)) :=
  (norm_decay f m hc).trans (exp_isBigO_discriminant.pow (m + 3))

end RamanujanTau.TheoremA.LevelSix
