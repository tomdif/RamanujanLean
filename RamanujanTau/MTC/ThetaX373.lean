/-
# `θ_{3,4}(x*, y*)`: the sixteen summands at the MTC₀ point

At `x* = Z²¹t^{105}`, `y* = Z⁶³t^{105}`, `q = t^{42}`, `Q = t^{168}`: `A_r = B_r = −Q^{10r+6}`, the `s = r` summands vanish
(`j(1; Q¹²) = 0`), the `s − r = ±2` ones cancel in pairs, and the rest pair up (`T(r,s) = T(s,r)`):

`thV_xstar`: `Σ_{r,s} Tn/Td = 2 j(Q³;Q¹²) · S`,
`S = Q⁻¹ j(Q¹⁸;Q⁴⁰)/(J̄₆J̄₁₆) + j(Q²;Q⁴⁰)/(J̄₄J̄₆) − Q⁵ j(Q²;Q⁴⁰)/(J̄₁₄J̄₁₆) − Q⁻² j(Q¹⁸;Q⁴⁰)/(J̄₁₄J̄₄)`
(`J̄_a = j(−Q^a; Q⁴⁰)`).
-/
import RamanujanTau.MTC.T373
import RamanujanTau.MTC.Z84
import RamanujanTau.ALTheta

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma hqT : 1 ≤ 42 := by norm_num

/-- `j(Q^a; Q^{12})`, `j(Q^a; Q^{40})`, `j(−Q^a; Q^{40})`. -/
noncomputable def j12 (a : ℤ) : L := θ (h48 hqT) (168 * a) 1
noncomputable def jA (a : ℤ) : L := θ (h160 hqT) (168 * a) 1
noncomputable def jB (a : ℤ) : L := θ (h160 hqT) (168 * a) (-1)

lemma θ_cgx {N : ℕ} (hN : 1 ≤ N) {e e' : ℤ} {c c' : ℂ} (he : e = e') (hc : c = c') : θ hN e c = θ hN e' c' := by
  subst he hc; rfl

lemma neg_mono_x (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

/-! ## canonical forms -/

lemma t48_0 : θ (h48 hqT) 0 1 = 0 := θ_one (h48 hqT)
lemma t48_504 : θ (h48 hqT) 504 1 = j12 3 := θ_cgx _ (by norm_num) rfl
lemma t48_1008 : θ (h48 hqT) 1008 1 = j12 6 := θ_cgx _ (by norm_num) rfl
lemma t48_1512 : θ (h48 hqT) 1512 1 = j12 3 := by
  have h := θ_reflect (h48 hqT) 504 one_ne_zero
  rw [inv_one] at h
  rw [← t48_504, ← h]; exact θ_cgx _ (by norm_num) rfl
lemma t48_m504 : θ (h48 hqT) (-504) 1 = -mono (-504) 1 * j12 3 := by
  have h := θ_inv (h48 hqT) 504 one_ne_zero
  rw [inv_one] at h
  rw [h, t48_504]
lemma t48_m1008 : θ (h48 hqT) (-1008) 1 = -mono (-1008) 1 * j12 6 := by
  have h := θ_inv (h48 hqT) 1008 one_ne_zero
  rw [inv_one] at h
  rw [h, t48_1008]
lemma t48_m1512 : θ (h48 hqT) (-1512) 1 = -mono (-1512) 1 * j12 3 := by
  have h := θ_inv (h48 hqT) 1512 one_ne_zero
  rw [inv_one] at h
  rw [h, t48_1512]

lemma t160_2016 : θ (h160 hqT) 2016 1 = jA 12 := θ_cgx _ (by norm_num) rfl
lemma t160_3696 : θ (h160 hqT) 3696 1 = jA 18 := by
  have h := θ_reflect (h160 hqT) 3024 one_ne_zero
  rw [inv_one] at h
  rw [show (3696 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 3024 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma t160_5376 : θ (h160 hqT) 5376 1 = jA 8 := by
  have h := θ_reflect (h160 hqT) 1344 one_ne_zero
  rw [inv_one] at h
  rw [show (5376 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 1344 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma t160_sh (e : ℤ) : θ (h160 hqT) (e + 6720) 1 = mono (-e) (-1) * θ (h160 hqT) e 1 := by
  have h := θ_qshift (h160 hqT) e one_ne_zero 1
  rw [show e + ((160 * 42 : ℕ) : ℤ) * 1 = e + 6720 by norm_num] at h
  rw [h]
  congr 1
  exact mono_ext (by norm_num [c2]; ring) (by norm_num)
lemma t160_7056 : θ (h160 hqT) 7056 1 = mono (-336) (-1) * jA 2 := by
  rw [show (7056 : ℤ) = 336 + 6720 by norm_num, t160_sh]; congr 1
lemma t160_8736 : θ (h160 hqT) 8736 1 = mono (-2016) (-1) * jA 12 := by
  rw [show (8736 : ℤ) = 2016 + 6720 by norm_num, t160_sh, t160_2016]
lemma t160_10416 : θ (h160 hqT) 10416 1 = mono (-3696) (-1) * jA 18 := by
  rw [show (10416 : ℤ) = 3696 + 6720 by norm_num, t160_sh, t160_3696]
lemma t160_12096 : θ (h160 hqT) 12096 1 = mono (-5376) (-1) * jA 8 := by
  rw [show (12096 : ℤ) = 5376 + 6720 by norm_num, t160_sh, t160_5376]

lemma tB_1008 : θ (h160 hqT) 1008 (-1) = jB 6 := θ_cgx _ (by norm_num) rfl
lemma tB_2688 : θ (h160 hqT) 2688 (-1) = jB 16 := θ_cgx _ (by norm_num) rfl
lemma tB_4368 : θ (h160 hqT) 4368 (-1) = jB 14 := by
  have h := θ_reflect (h160 hqT) 2352 (by norm_num : (-1 : ℂ) ≠ 0)
  rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  rw [show (4368 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 2352 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl
lemma tB_6048 : θ (h160 hqT) 6048 (-1) = jB 4 := by
  have h := θ_reflect (h160 hqT) 672 (by norm_num : (-1 : ℂ) ≠ 0)
  rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  rw [show (6048 : ℤ) = ((160 * 42 : ℕ) : ℤ) - 672 by norm_num, h]; exact θ_cgx _ (by norm_num) rfl

lemma c1T_x : c1T (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
  unfold c1T; simp only [Z_neg']; zsimp; exact Z_eq_one (by norm_num)
lemma c2T_x : c2T (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
  unfold c2T; zsimp; exact Z_eq_one (by norm_num)
lemma cAT_x : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = -1 := by
  unfold cAT; rw [Z_neg1]; zsimp; exact Z_mod (by norm_num)
lemma cBT_x : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = -1 := by
  unfold cBT; rw [Z_neg1]; zsimp; exact Z_mod (by norm_num)

/-! ## the sixteen summands -/

lemma T00 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 0 0 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 0 0 105 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 105 0 0 105 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma T01 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 0 1 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 0 1 105 (Z84 ^ (21 : ℤ)) = mono (-168) (1) * (j12 3 * jA 18) / (jB 6 * jB 16) := by
  have hm : (mono (eTn (qe := 42) 105 0 1 105) (cTn (Z84 ^ (63 : ℤ)) 0 1 (Z84 ^ (21 : ℤ))) : L) = mono (-168) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 0 1 105 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 0 1 105 = 3696 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 0 105 = 1008 by norm_num [eAT], cAT_x, tB_1008,
    show eBT (qe := 42) 105 1 105 = 2688 by norm_num [eBT], cBT_x, tB_2688, t48_504, t160_3696]
  linear_combination (j12 3 * jA 18 / (jB 6 * jB 16)) * hm

lemma T02 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 0 2 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 0 2 105 (Z84 ^ (21 : ℤ)) = mono (21) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 8) / (jB 6 * jB 14) := by
  have hm : (mono (eTn (qe := 42) 105 0 2 105) (cTn (Z84 ^ (63 : ℤ)) 0 2 (Z84 ^ (21 : ℤ))) : L) = mono (21) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 0 2 105 = 1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 0 2 105 = 5376 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 0 105 = 1008 by norm_num [eAT], cAT_x, tB_1008,
    show eBT (qe := 42) 105 2 105 = 4368 by norm_num [eBT], cBT_x, tB_4368, t48_1008, t160_5376]
  linear_combination (j12 6 * jA 8 / (jB 6 * jB 14)) * hm

lemma T03 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 0 3 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 0 3 105 (Z84 ^ (21 : ℤ)) = mono (0) (1) * (j12 3 * jA 2) / (jB 6 * jB 4) := by
  have hm : (mono (eTn (qe := 42) 105 0 3 105) (cTn (Z84 ^ (63 : ℤ)) 0 3 (Z84 ^ (21 : ℤ))) * mono (-336) (-1) : L) = mono (0) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 0 3 105 = 1512 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 0 3 105 = 7056 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 0 105 = 1008 by norm_num [eAT], cAT_x, tB_1008,
    show eBT (qe := 42) 105 3 105 = 6048 by norm_num [eBT], cBT_x, tB_6048, t48_1512, t160_7056]
  linear_combination (j12 3 * jA 2 / (jB 6 * jB 4)) * hm

lemma T10 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 1 0 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 1 0 105 (Z84 ^ (21 : ℤ)) = mono (-168) (1) * (j12 3 * jA 18) / (jB 16 * jB 6) := by
  have hm : (mono (eTn (qe := 42) 105 1 0 105) (cTn (Z84 ^ (63 : ℤ)) 1 0 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) : L) = mono (-168) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 1 0 105 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 1 0 105 = 3696 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 1 105 = 2688 by norm_num [eAT], cAT_x, tB_2688,
    show eBT (qe := 42) 105 0 105 = 1008 by norm_num [eBT], cBT_x, tB_1008, t48_m504, t160_3696]
  linear_combination (j12 3 * jA 18 / (jB 16 * jB 6)) * hm

lemma T11 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 1 1 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 1 1 105 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 105 1 1 105 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma T12 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 1 2 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 1 2 105 (Z84 ^ (21 : ℤ)) = -(mono (840) (1) * (j12 3 * jA 2) / (jB 16 * jB 14)) := by
  have hm : (mono (eTn (qe := 42) 105 1 2 105) (cTn (Z84 ^ (63 : ℤ)) 1 2 (Z84 ^ (21 : ℤ))) * mono (-336) (-1) : L) = -mono (840) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 1 2 105 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 1 2 105 = 7056 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 1 105 = 2688 by norm_num [eAT], cAT_x, tB_2688,
    show eBT (qe := 42) 105 2 105 = 4368 by norm_num [eBT], cBT_x, tB_4368, t48_504, t160_7056]
  linear_combination (j12 3 * jA 2 / (jB 16 * jB 14)) * hm

lemma T13 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 1 3 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 1 3 105 (Z84 ^ (21 : ℤ)) = -(mono (-231) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 12) / (jB 16 * jB 4)) := by
  have hm : (mono (eTn (qe := 42) 105 1 3 105) (cTn (Z84 ^ (63 : ℤ)) 1 3 (Z84 ^ (21 : ℤ))) * mono (-2016) (-1) : L) = -mono (-231) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 1 3 105 = 1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 1 3 105 = 8736 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 1 105 = 2688 by norm_num [eAT], cAT_x, tB_2688,
    show eBT (qe := 42) 105 3 105 = 6048 by norm_num [eBT], cBT_x, tB_6048, t48_1008, t160_8736]
  linear_combination (j12 6 * jA 12 / (jB 16 * jB 4)) * hm

lemma T20 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 2 0 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 2 0 105 (Z84 ^ (21 : ℤ)) = -(mono (21) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 8) / (jB 14 * jB 6)) := by
  have hm : (mono (eTn (qe := 42) 105 2 0 105) (cTn (Z84 ^ (63 : ℤ)) 2 0 (Z84 ^ (21 : ℤ))) * (-mono (-1008) 1) : L) = -mono (21) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 2 0 105 = -1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 2 0 105 = 5376 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 2 105 = 4368 by norm_num [eAT], cAT_x, tB_4368,
    show eBT (qe := 42) 105 0 105 = 1008 by norm_num [eBT], cBT_x, tB_1008, t48_m1008, t160_5376]
  linear_combination (j12 6 * jA 8 / (jB 14 * jB 6)) * hm

lemma T21 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 2 1 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 2 1 105 (Z84 ^ (21 : ℤ)) = -(mono (840) (1) * (j12 3 * jA 2) / (jB 14 * jB 16)) := by
  have hm : (mono (eTn (qe := 42) 105 2 1 105) (cTn (Z84 ^ (63 : ℤ)) 2 1 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) * mono (-336) (-1) : L) = -mono (840) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 2 1 105 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 2 1 105 = 7056 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 2 105 = 4368 by norm_num [eAT], cAT_x, tB_4368,
    show eBT (qe := 42) 105 1 105 = 2688 by norm_num [eBT], cBT_x, tB_2688, t48_m504, t160_7056]
  linear_combination (j12 3 * jA 2 / (jB 14 * jB 16)) * hm

lemma T22 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 2 2 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 2 2 105 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 105 2 2 105 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma T23 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 2 3 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 2 3 105 (Z84 ^ (21 : ℤ)) = -(mono (-336) (1) * (j12 3 * jA 18) / (jB 14 * jB 4)) := by
  have hm : (mono (eTn (qe := 42) 105 2 3 105) (cTn (Z84 ^ (63 : ℤ)) 2 3 (Z84 ^ (21 : ℤ))) * mono (-3696) (-1) : L) = -mono (-336) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 2 3 105 = 504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 2 3 105 = 10416 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 2 105 = 4368 by norm_num [eAT], cAT_x, tB_4368,
    show eBT (qe := 42) 105 3 105 = 6048 by norm_num [eBT], cBT_x, tB_6048, t48_504, t160_10416]
  linear_combination (j12 3 * jA 18 / (jB 14 * jB 4)) * hm

lemma T30 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 3 0 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 3 0 105 (Z84 ^ (21 : ℤ)) = mono (0) (1) * (j12 3 * jA 2) / (jB 4 * jB 6) := by
  have hm : (mono (eTn (qe := 42) 105 3 0 105) (cTn (Z84 ^ (63 : ℤ)) 3 0 (Z84 ^ (21 : ℤ))) * (-mono (-1512) 1) * mono (-336) (-1) : L) = mono (0) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_eq_one (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 3 0 105 = -1512 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 3 0 105 = 7056 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 3 105 = 6048 by norm_num [eAT], cAT_x, tB_6048,
    show eBT (qe := 42) 105 0 105 = 1008 by norm_num [eBT], cBT_x, tB_1008, t48_m1512, t160_7056]
  linear_combination (j12 3 * jA 2 / (jB 4 * jB 6)) * hm

lemma T31 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 3 1 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 3 1 105 (Z84 ^ (21 : ℤ)) = mono (-231) (Z84 ^ (21 : ℤ)) * (j12 6 * jA 12) / (jB 4 * jB 16) := by
  have hm : (mono (eTn (qe := 42) 105 3 1 105) (cTn (Z84 ^ (63 : ℤ)) 3 1 (Z84 ^ (21 : ℤ))) * (-mono (-1008) 1) * mono (-2016) (-1) : L) = mono (-231) (Z84 ^ (21 : ℤ)) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 3 1 105 = -1008 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 3 1 105 = 8736 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 3 105 = 6048 by norm_num [eAT], cAT_x, tB_6048,
    show eBT (qe := 42) 105 1 105 = 2688 by norm_num [eBT], cBT_x, tB_2688, t48_m1008, t160_8736]
  linear_combination (j12 6 * jA 12 / (jB 4 * jB 16)) * hm

lemma T32 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 3 2 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 3 2 105 (Z84 ^ (21 : ℤ)) = -(mono (-336) (1) * (j12 3 * jA 18) / (jB 4 * jB 14)) := by
  have hm : (mono (eTn (qe := 42) 105 3 2 105) (cTn (Z84 ^ (63 : ℤ)) 3 2 (Z84 ^ (21 : ℤ))) * (-mono (-504) 1) * mono (-3696) (-1) : L) = -mono (-336) (1) := by
    try simp only [neg_mono_x, mono_mul, neg_mul, mul_neg]
    refine mono_ext (by norm_num [eTn, c2]) ?_
    unfold cTn
    simp only [Z_neg']
    zsimp
    exact Z_mod (by norm_num)
  unfold Tn Td
  rw [show e1T (qe := 42) 105 3 2 105 = -504 by norm_num [e1T], c1T_x,
    show e2T (qe := 42) 105 3 2 105 = 10416 by norm_num [e2T], c2T_x,
    show eAT (qe := 42) 105 3 105 = 6048 by norm_num [eAT], cAT_x, tB_6048,
    show eBT (qe := 42) 105 2 105 = 4368 by norm_num [eBT], cBT_x, tB_4368, t48_m504, t160_10416]
  linear_combination (j12 3 * jA 18 / (jB 4 * jB 14)) * hm

lemma T33 : Tn hqT 105 (Z84 ^ (63 : ℤ)) 3 3 105 (Z84 ^ (21 : ℤ)) / Td hqT 105 (Z84 ^ (63 : ℤ)) 3 3 105 (Z84 ^ (21 : ℤ)) = 0 := by
  unfold Tn Td
  rw [show e1T (qe := 42) 105 3 3 105 = 0 by norm_num [e1T], c1T_x, t48_0]
  simp

lemma Icc03_x : Finset.Icc (0 : ℤ) 3 = {0, 1, 2, 3} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **`θ_{3,4}(x*, y*)`**. -/
theorem thV_xstar : thV hqT 105 (Z84 ^ (63 : ℤ)) 105 (Z84 ^ (21 : ℤ)) =
    2 * j12 3 * (mono (-168) 1 * jA 18 / (jB 6 * jB 16) + jA 2 / (jB 4 * jB 6) -
      mono 840 1 * jA 2 / (jB 14 * jB 16) - mono (-336) 1 * jA 18 / (jB 14 * jB 4)) := by
  unfold thV
  simp only [Icc03_x, Finset.sum_insert (show (0 : ℤ) ∉ ({1, 2, 3} : Finset ℤ) by decide),
    Finset.sum_insert (show (1 : ℤ) ∉ ({2, 3} : Finset ℤ) by decide),
    Finset.sum_insert (show (2 : ℤ) ∉ ({3} : Finset ℤ) by decide), Finset.sum_singleton]
  rw [T00, T01, T02, T03, T10, T11, T12, T13, T20, T21, T22, T23, T30, T31, T32, T33]
  simp only [show (mono 0 1 : L) = 1 from rfl, one_mul]
  ring

end MTC
