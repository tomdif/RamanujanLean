import RamanujanTau.TheoremA.EtaCuspData
import RamanujanTau.TheoremA.EtaQuotientModularity

/-! Transformation of each eta quotient at the twelve cusp representatives. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

noncomputable def cuspAffine (i : Fin 12) (j : Fin 4) (z : ℍ) : ℍ :=
  ⟨((cuspA i j : ℝ) / cuspD i j : ℂ) * z + ((cuspB i j : ℝ) / cuspD i j : ℂ), by
    simpa using mul_pos
      (div_pos (by exact_mod_cast (cusp_positive i j).1 : (0 : ℝ) < cuspA i j)
        (by exact_mod_cast (cusp_positive i j).2 : (0 : ℝ) < cuspD i j)) z.im_pos⟩

lemma cuspD_ne_zero (i : Fin 12) (j : Fin 4) : (cuspD i j : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (cusp_positive i j).2

lemma cusp_denom (i : Fin 12) (j : Fin 4) (z : ℍ) :
    denom (wordMatrix (cuspWord i j)) (cuspAffine i j z) =
      denom (LevelSix.rep i) z / cuspD i j := by
  obtain ⟨_, _, hc, he⟩ := cusp_factorization i j
  change ((wordMatrix (cuspWord i j) 1 0 : ℂ) *
    (((cuspA i j : ℝ) / cuspD i j : ℂ) * z + ((cuspB i j : ℝ) / cuspD i j : ℂ)) +
    wordMatrix (cuspWord i j) 1 1) =
    ((LevelSix.rep i 1 0 : ℂ) * z + LevelSix.rep i 1 1) / cuspD i j
  rw [hc, he]
  push_cast
  field_simp [cuspD_ne_zero i j]
  ring

lemma cusp_smul (i : Fin 12) (j : Fin 4) (z : ℍ) :
    scale (dilation j) (dilation_pos j) (LevelSix.rep i • z) =
      wordMatrix (cuspWord i j) • cuspAffine i j z := by
  obtain ⟨ha, hb, hc, he⟩ := cusp_factorization i j
  have ha' : (dilation j : ℂ) * LevelSix.rep i 0 0 =
      (wordMatrix (cuspWord i j) 0 0 : ℂ) * cuspA i j := by exact_mod_cast ha
  have hb' : (dilation j : ℂ) * LevelSix.rep i 0 1 =
      (wordMatrix (cuspWord i j) 0 0 : ℂ) * cuspB i j +
        (wordMatrix (cuspWord i j) 0 1 : ℂ) * cuspD i j := by exact_mod_cast hb
  apply UpperHalfPlane.ext
  change (dilation j : ℂ) * (↑(LevelSix.rep i • z) : ℂ) = _
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  change (dilation j : ℂ) *
    (((LevelSix.rep i 0 0 : ℂ) * z + LevelSix.rep i 0 1) / denom (LevelSix.rep i) z) =
      (((wordMatrix (cuspWord i j) 0 0 : ℂ) * cuspAffine i j z +
        wordMatrix (cuspWord i j) 0 1) / denom (wordMatrix (cuspWord i j)) (cuspAffine i j z))
  rw [cusp_denom]
  have hn : (wordMatrix (cuspWord i j) 0 0 : ℂ) * cuspAffine i j z +
      wordMatrix (cuspWord i j) 0 1 =
      ((dilation j : ℂ) * ((LevelSix.rep i 0 0 : ℂ) * z + LevelSix.rep i 0 1)) / cuspD i j := by
    change (wordMatrix (cuspWord i j) 0 0 : ℂ) *
      (((cuspA i j : ℝ) / cuspD i j : ℂ) * z + ((cuspB i j : ℝ) / cuspD i j : ℂ)) + _ = _
    push_cast
    simp only [mul_add, ← mul_assoc, ha', hb']
    field_simp [cuspD_ne_zero i j]
    ring
  rw [hn]
  field_simp [cuspD_ne_zero i j, denom_ne_zero (LevelSix.rep i) z]

theorem scaledEta_rep_apply (i : Fin 12) (j : Fin 4) (z : ℍ) :
    scaledEta (dilation j) (dilation_pos j) (LevelSix.rep i • z) =
      (phase (wordExponent (cuspWord i j)) / cuspD i j) *
        etaSquared (cuspAffine i j z) * denom (LevelSix.rep i) z := by
  have ht := congrFun (slash_word (cuspWord i j)) (cuspAffine i j z)
  rw [SL_slash_apply] at ht
  have ht' : etaSquared (wordMatrix (cuspWord i j) • cuspAffine i j z) =
      phase (wordExponent (cuspWord i j)) * etaSquared (cuspAffine i j z) *
        denom (wordMatrix (cuspWord i j)) (cuspAffine i j z) := by
    simpa only [neg_mul, mul_one, zpow_neg_one, Pi.smul_apply, smul_eq_mul,
      mul_inv_eq_iff_eq_mul₀ (denom_ne_zero _ _)] using ht
  change etaSquared (scale (dilation j) (dilation_pos j) (LevelSix.rep i • z)) = _
  rw [cusp_smul, ht', cusp_denom]
  ring

noncomputable def cuspConstant (a : Fin 3) (i : Fin 12) : ℂ :=
  ∏ j : Fin 4, (phase (wordExponent (cuspWord i j)) / cuspD i j) ^ basisExponent a j

theorem basisFunction_rep_apply (a : Fin 3) (i : Fin 12) (z : ℍ) :
    (basisFunction a ∣[(6 : ℤ)] LevelSix.rep i) z =
      cuspConstant a i * ∏ j : Fin 4, etaSquared (cuspAffine i j z) ^ basisExponent a j := by
  rw [SL_slash_apply]
  simp only [basisFunction, scaledEta_rep_apply, mul_zpow, Finset.prod_mul_distrib]
  rw [← zpow_sum_of_ne_zero _ _ (denom_ne_zero _ _), basisExponent_sum,
    mul_assoc, ← zpow_add₀ (denom_ne_zero _ _)]
  simp [cuspConstant]

end RamanujanTau.TheoremA.EtaSquared
