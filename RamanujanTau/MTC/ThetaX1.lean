/-
# `θ_{3,4}(x₁, y₁)`: the sixteen summands at the MTC₁ point

At `x₁ = Z²¹t^{189}`, `y₁ = Z⁶³t^{189}`: `A_r = B_r = −Q^{10r+8}` and
`thV_x1`: `Σ_{r,s} Tn/Td = 2 j(Q³;Q¹²) · S₁`,
`S₁ = j(Q¹⁴;Q⁴⁰)/(J̄₁₈J̄₈) + Q⁻² j(Q⁶;Q⁴⁰)/(J̄₂J̄₈) − Q³ j(Q⁶;Q⁴⁰)/(J̄₁₂J̄₁₈) − Q⁻³ j(Q¹⁴;Q⁴⁰)/(J̄₁₂J̄₂)`.
-/
import RamanujanTau.MTC.ThetaX373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma u160_2688 : θ (h160 hqT) 2688 1 = jA 16 := θ_cgx _ (by norm_num) rfl
lemma u160_4368 : θ (h160 hqT) 4368 1 = jA 14 := by
  have h := θ_reflect (h160 hqT) 2352 one_ne_zero
  rw [inv_one] at h
  rw [show (4368 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 2352 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma u160_6048 : θ (h160 hqT) 6048 1 = jA 4 := by
  have h := θ_reflect (h160 hqT) 672 one_ne_zero
  rw [inv_one] at h
  rw [show (6048 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 672 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma u160_7728 : θ (h160 hqT) 7728 1 = mono (-1008) (-1) * jA 6 := by
  rw [show (7728 : ℤ) = 1008 + 6720 by norm_num, t160_sh]; congr 1
lemma u160_9408 : θ (h160 hqT) 9408 1 = mono (-2688) (-1) * jA 16 := by
  rw [show (9408 : ℤ) = 2688 + 6720 by norm_num, t160_sh, u160_2688]
lemma u160_11088 : θ (h160 hqT) 11088 1 = mono (-4368) (-1) * jA 14 := by
  rw [show (11088 : ℤ) = 4368 + 6720 by norm_num, t160_sh, u160_4368]
lemma u160_12768 : θ (h160 hqT) 12768 1 = mono (-6048) (-1) * jA 4 := by
  rw [show (12768 : ℤ) = 6048 + 6720 by norm_num, t160_sh, u160_6048]

lemma uB_1344 : θ (h160 hqT) 1344 (-1) = jB 8 := θ_cgx _ (by norm_num) rfl
lemma uB_3024 : θ (h160 hqT) 3024 (-1) = jB 18 := θ_cgx _ (by norm_num) rfl
lemma uB_4704 : θ (h160 hqT) 4704 (-1) = jB 12 := by
  have h := θ_reflect (h160 hqT) 2016 (by norm_num : (-1 : ℂ) ≠ 0)
  rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  rw [show (4704 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 2016 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma uB_6384 : θ (h160 hqT) 6384 (-1) = jB 2 := by
  have h := θ_reflect (h160 hqT) 336 (by norm_num : (-1 : ℂ) ≠ 0)
  rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  rw [show (6384 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 336 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl

lemma U00 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 0 0 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 0 0 189 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 189 0 0 189 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma U01 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 0 1 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 0 1 189 (Z84 ^ (21 : ℤ)) = mono (0) (1) * (j12 3 * jA 14) / (jB 8 * jB 18) := by
  have hm : (mono (eTn (qe := 42) 189 0 1 189) (cTn (Z84 ^ (63 : ℤ)) 0 1 (Z84 ^ (21 : ℤ))) : L) = mono (0) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 0 1 189 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 0 1 189 = 4368 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 0 189 = 1344 by norm_num [eAT], cAT_x, uB_1344,
    show eBT (qe := 42) 189 1 189 = 3024 by norm_num [eBT], cBT_x, uB_3024, t48_504, u160_4368]
  linear_combination (j12 3 * jA 14 / (jB 8 * jB 18)) * hm

lemma U02 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 0 2 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 0 2 189 (Z84 ^ (21 : ℤ)) = mono (273) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 4) / (jB 8 * jB 12) := by
  have hm : (mono (eTn (qe := 42) 189 0 2 189) (cTn (Z84 ^ (63 : ℤ)) 0 2 (Z84 ^ (21 : ℤ))) : L) = mono (273) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 0 2 189 = 1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 0 2 189 = 6048 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 0 189 = 1344 by norm_num [eAT], cAT_x, uB_1344,
    show eBT (qe := 42) 189 2 189 = 4704 by norm_num [eBT], cBT_x, uB_4704, t48_1008, u160_6048]
  linear_combination (j12 6 * jA 4 / (jB 8 * jB 12)) * hm

lemma U03 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 0 3 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 0 3 189 (Z84 ^ (21 : ℤ)) = mono (-336) (1) * (j12 3 * jA 6) / (jB 8 * jB 2) := by
  have hm : (mono (eTn (qe := 42) 189 0 3 189) (cTn (Z84 ^ (63 : ℤ)) 0 3 (Z84 ^ (21 : ℤ))) * mono (-1008) (-1) : L) = mono (-336) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 0 3 189 = 1512 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 0 3 189 = 7728 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 0 189 = 1344 by norm_num [eAT], cAT_x, uB_1344,
    show eBT (qe := 42) 189 3 189 = 6384 by norm_num [eBT], cBT_x, uB_6384, t48_1512, u160_7728]
  linear_combination (j12 3 * jA 6 / (jB 8 * jB 2)) * hm

lemma U10 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 1 0 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 1 0 189 (Z84 ^ (21 : ℤ)) = mono (0) (1) * (j12 3 * jA 14) / (jB 18 * jB 8) := by
  have hm : (mono (eTn (qe := 42) 189 1 0 189) (cTn (Z84 ^ (63 : ℤ)) 1 0 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) : L) = mono (0) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 1 0 189 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 1 0 189 = 4368 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 1 189 = 3024 by norm_num [eAT], cAT_x, uB_3024,
    show eBT (qe := 42) 189 0 189 = 1344 by norm_num [eBT], cBT_x, uB_1344, t48_m504, u160_4368]
  linear_combination (j12 3 * jA 14 / (jB 18 * jB 8)) * hm

lemma U11 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 1 1 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 1 1 189 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 189 1 1 189 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma U12 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 1 2 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 1 2 189 (Z84 ^ (21 : ℤ)) = -(mono (504) (1) * (j12 3 * jA 6) / (jB 18 * jB 12)) := by
  have hm : (mono (eTn (qe := 42) 189 1 2 189) (cTn (Z84 ^ (63 : ℤ)) 1 2 (Z84 ^ (21 : ℤ))) * mono (-1008) (-1) : L) = -mono (504) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 1 2 189 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 1 2 189 = 7728 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 1 189 = 3024 by norm_num [eAT], cAT_x, uB_3024,
    show eBT (qe := 42) 189 2 189 = 4704 by norm_num [eBT], cBT_x, uB_4704, t48_504, u160_7728]
  linear_combination (j12 3 * jA 6 / (jB 18 * jB 12)) * hm

lemma U13 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 1 3 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 1 3 189 (Z84 ^ (21 : ℤ)) = -(mono (-483) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 16) / (jB 18 * jB 2)) := by
  have hm : (mono (eTn (qe := 42) 189 1 3 189) (cTn (Z84 ^ (63 : ℤ)) 1 3 (Z84 ^ (21 : ℤ))) * mono (-2688) (-1) : L) = -mono (-483) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 1 3 189 = 1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 1 3 189 = 9408 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 1 189 = 3024 by norm_num [eAT], cAT_x, uB_3024,
    show eBT (qe := 42) 189 3 189 = 6384 by norm_num [eBT], cBT_x, uB_6384, t48_1008, u160_9408]
  linear_combination (j12 6 * jA 16 / (jB 18 * jB 2)) * hm

lemma U20 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 2 0 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 2 0 189 (Z84 ^ (21 : ℤ)) = -(mono (273) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 4) / (jB 12 * jB 8)) := by
  have hm : (mono (eTn (qe := 42) 189 2 0 189) (cTn (Z84 ^ (63 : ℤ)) 2 0 (Z84 ^ (21 : ℤ))) * (-mono (-1008) 1) : L) = -mono (273) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 2 0 189 = -1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 2 0 189 = 6048 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 2 189 = 4704 by norm_num [eAT], cAT_x, uB_4704,
    show eBT (qe := 42) 189 0 189 = 1344 by norm_num [eBT], cBT_x, uB_1344, t48_m1008, u160_6048]
  linear_combination (j12 6 * jA 4 / (jB 12 * jB 8)) * hm

lemma U21 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 2 1 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 2 1 189 (Z84 ^ (21 : ℤ)) = -(mono (504) (1) * (j12 3 * jA 6) / (jB 12 * jB 18)) := by
  have hm : (mono (eTn (qe := 42) 189 2 1 189) (cTn (Z84 ^ (63 : ℤ)) 2 1 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) * mono (-1008) (-1) : L) = -mono (504) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 2 1 189 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 2 1 189 = 7728 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 2 189 = 4704 by norm_num [eAT], cAT_x, uB_4704,
    show eBT (qe := 42) 189 1 189 = 3024 by norm_num [eBT], cBT_x, uB_3024, t48_m504, u160_7728]
  linear_combination (j12 3 * jA 6 / (jB 12 * jB 18)) * hm

lemma U22 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 2 2 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 2 2 189 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 189 2 2 189 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma U23 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 2 3 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 2 3 189 (Z84 ^ (21 : ℤ)) = -(mono (-504) (1) * (j12 3 * jA 14) / (jB 12 * jB 2)) := by
  have hm : (mono (eTn (qe := 42) 189 2 3 189) (cTn (Z84 ^ (63 : ℤ)) 2 3 (Z84 ^ (21 : ℤ))) * mono (-4368) (-1) : L) = -mono (-504) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 2 3 189 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 2 3 189 = 11088 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 2 189 = 4704 by norm_num [eAT], cAT_x, uB_4704,
    show eBT (qe := 42) 189 3 189 = 6384 by norm_num [eBT], cBT_x, uB_6384, t48_504, u160_11088]
  linear_combination (j12 3 * jA 14 / (jB 12 * jB 2)) * hm

lemma U30 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 3 0 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 3 0 189 (Z84 ^ (21 : ℤ)) = mono (-336) (1) * (j12 3 * jA 6) / (jB 2 * jB 8) := by
  have hm : (mono (eTn (qe := 42) 189 3 0 189) (cTn (Z84 ^ (63 : ℤ)) 3 0 (Z84 ^ (21 : ℤ))) * (-mono (-1512) 1) * mono (-1008) (-1) : L) = mono (-336) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 3 0 189 = -1512 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 3 0 189 = 7728 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 3 189 = 6384 by norm_num [eAT], cAT_x, uB_6384,
    show eBT (qe := 42) 189 0 189 = 1344 by norm_num [eBT], cBT_x, uB_1344, t48_m1512, u160_7728]
  linear_combination (j12 3 * jA 6 / (jB 2 * jB 8)) * hm

lemma U31 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 3 1 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 3 1 189 (Z84 ^ (21 : ℤ)) = mono (-483) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 16) / (jB 2 * jB 18) := by
  have hm : (mono (eTn (qe := 42) 189 3 1 189) (cTn (Z84 ^ (63 : ℤ)) 3 1 (Z84 ^ (21 : ℤ))) * (-mono (-1008) 1) * mono (-2688) (-1) : L) = mono (-483) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 3 1 189 = -1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 3 1 189 = 9408 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 3 189 = 6384 by norm_num [eAT], cAT_x, uB_6384,
    show eBT (qe := 42) 189 1 189 = 3024 by norm_num [eBT], cBT_x, uB_3024, t48_m1008, u160_9408]
  linear_combination (j12 6 * jA 16 / (jB 2 * jB 18)) * hm

lemma U32 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 3 2 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 3 2 189 (Z84 ^ (21 : ℤ)) = -(mono (-504) (1) * (j12 3 * jA 14) / (jB 2 * jB 12)) := by
  have hm : (mono (eTn (qe := 42) 189 3 2 189) (cTn (Z84 ^ (63 : ℤ)) 3 2 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) * mono (-4368) (-1) : L) = -mono (-504) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 189 3 2 189 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 189 3 2 189 = 11088 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 189 3 189 = 6384 by norm_num [eAT], cAT_x, uB_6384,
    show eBT (qe := 42) 189 2 189 = 4704 by norm_num [eBT], cBT_x, uB_4704, t48_m504, u160_11088]
  linear_combination (j12 3 * jA 14 / (jB 2 * jB 12)) * hm

lemma U33 : Tn hqT 189 (Z84 ^ (63 : ℤ)) 3 3 189 (Z84 ^ (21 : ℤ)) / Td hqT 189 (Z84 ^ (63 : ℤ)) 3 3 189 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 189 3 3 189 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

/-- **`θ_{3,4}(x₁, y₁)`**. -/
theorem thV_x1 : thV hqT 189 (Z84 ^ (63 : ℤ)) 189 (Z84 ^ (21 : ℤ)) =
    2 * j12 3 * (jA 14 / (jB 18 * jB 8) + mono (-336) 1 * jA 6 / (jB 2 * jB 8) -
      mono 504 1 * jA 6 / (jB 12 * jB 18) - mono (-504) 1 * jA 14 / (jB 12 * jB 2)) := by
  unfold thV
  simp only [Icc03_x, Finset.sum_insert (show (0 : ℤ) ∉ ({1, 2, 3} : Finset ℤ) by decide),
    Finset.sum_insert (show (1 : ℤ) ∉ ({2, 3} : Finset ℤ) by decide),
    Finset.sum_insert (show (2 : ℤ) ∉ ({3} : Finset ℤ) by decide), Finset.sum_singleton]
  rw [U00, U01, U02, U03, U10, U11, U12, U13, U20, U21, U22, U23, U30, U31, U32, U33]
  simp only [show (mono 0 1 : L) = 1 from rfl, one_mul]
  ring

end MTC
