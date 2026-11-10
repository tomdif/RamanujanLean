/-
# Entry 3.29

`{G(q²)G(q²³) + q⁵H(q²)H(q²³)}{G(q⁴⁶)H(q) − q⁹G(q)H(q⁴⁶)} = χ(−q)χ(−q²³) + q + 2q²/(χ(−q)χ(−q²³))`.

Yesilyurt's proof (JMAA 388 (2012) §4) with his second functional equation replaced by the identity of his closing
remark (proved here for 23). With `A`, `B` as in `E29c.lean`, `v = χ(−q)χ(−q²³)`, `u = χ(q)χ(q²³)`,
`w = χ(−q²)χ(−q⁴⁶) = uv`:
* `E1` (his (4.13)): `f(−q)f(−Q) A(q) = f(−q²)f(−Q²) (A(q²)B(−q) − qA(q))`, from `L29p` (`D5p_eq`) and the
  evaluations `D5p_ι`, `Ye_ι`, `Yo_ι`, pulled back by `q² ↦ q`;
* `E2`: `f(−q²)f(−Q²) A(q)A(−q) = A(q²) (f(−q²)f(−Q²) + 2q² f(−q⁴)f(−Q⁴))`, i.e.
  `A(q)A(−q) = (1 + 2q²/w) A(q²)`, from `L29m − L29p`;
* `E1` at `−q` gives `A(q²)B(q) = A(−q)(u − q)`; with `E2`, `w·A(q)B(q) = (w + 2q²)(u − q)`;
* the degree-23 equation `M23` (`u − v = 2q + 2q³/w`) turns this into Entry 3.29.
-/
import RamanujanTau.Forty.E29d

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

lemma S2_A29 : S 2 A29 = S 4 G * S 46 G + X ^ 10 * S 4 H * S 46 H := by
  simp only [A29, map_add, map_mul, map_pow, S_S8 2 2, S_S8 2 23, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  ring

lemma S4_A29 : S 2 (S 2 A29) = S 8 G * S 92 G + X ^ 20 * S 8 H * S 92 H := by
  simp only [S2_A29, map_add, map_mul, map_pow, S_S8 2 4, S_S8 2 46, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  ring

lemma Ng_B29 : Ng B29 = S 46 G * Ng H + X ^ 9 * Ng G * S 46 H := by
  simp only [B29, map_sub, map_mul, map_pow, Ng_S_ev 46 (by norm_num), Ng_X]
  ring

lemma S2_NgB29 : S 2 (Ng B29) = S 92 G * S 2 (Ng H) + X ^ 18 * S 2 (Ng G) * S 92 H := by
  simp only [Ng_B29, map_add, map_mul, map_pow, S_S8 2 46, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  ring

lemma cc_A29 : constantCoeff (A29) = 1 := by
  simp only [A29, map_add, map_mul, map_pow, constantCoeff_X, cc_S, cc_G]
  norm_num

lemma A29_ne : S 2 A29 ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [cc_S, cc_A29, map_zero] at this
  exact one_ne_zero this

/-- Yesilyurt (4.13): `f(−q)f(−Q) A(q) = f(−q²)f(−Q²) (A(q²)B(−q) − qA(q))`. -/
theorem E1_29 : Pinf 1 1 * Pinf 23 23 * A29 =
    Pinf 2 2 * Pinf 46 46 * (S 2 A29 * Ng B29) - X * (Pinf 2 2 * Pinf 46 46 * A29) := by
  have hP := D5p_eq
  rw [D5p_ι, Ye_ι, Yo_ι, ← map_sub] at hP
  have hP' := ι_inj hP
  apply S_inj 2
  simp only [map_mul, map_sub, S_P' 2 1 1 le_rfl le_rfl (rfl : 2 = 2 * 1) (rfl : 2 = 2 * 1),
    S_P' 2 23 23 (by norm_num) (by norm_num) (rfl : 46 = 2 * 23) (rfl : 46 = 2 * 23),
    S_P' 2 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 4 = 2 * 2),
    S_P' 2 46 46 (by norm_num) (by norm_num) (rfl : 92 = 2 * 46) (rfl : 92 = 2 * 46),
    S2_NgB29, S2_A29, map_add, map_pow, S_S8 2 4, S_S8 2 46, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  linear_combination hP'

/-- `f(−q²)f(−Q²) A(q)A(−q) = A(q²) (f(−q²)f(−Q²) + 2q² f(−q⁴)f(−Q⁴))`. -/
theorem E2_29 : Pinf 2 2 * Pinf 46 46 * A29 * Ng A29 =
    S 2 A29 * (Pinf 2 2 * Pinf 46 46 + 2 * X ^ 2 * (Pinf 4 4 * Pinf 92 92)) := by
  have hP := D5p_eq
  rw [D5p_ι, Ye_ι, Yo_ι, ← map_sub] at hP
  have hM := D5m_eq
  rw [D5m_ι, Ye_ι, Yo_ι, ← map_add] at hM
  have hP' := ι_inj hP
  have hM' := ι_inj hM
  rw [S2_A29]
  linear_combination hM' - hP'

lemma Ng_P2323 : Ng (Pinf 23 23) = Pinf 46 46 * chip 23 := by
  have h := Ng_S_odd8 23 (by decide) (Pinf 1 1)
  rw [S_Pinf 23 1 1 le_rfl le_rfl, Ng_E1, map_mul, S_Pinf 23 2 2 (by norm_num) (by norm_num), S23_chip1] at h
  exact h

/-- **Entry 3.29** (Ramanujan; proved by Biagioli with modular forms, elementary proof by Yesilyurt 2012):
`{G(q²)G(q²³) + q⁵H(q²)H(q²³)}{G(q⁴⁶)H(q) − q⁹G(q)H(q⁴⁶)} = χ(−q)χ(−q²³) + q + 2q²/(χ(−q)χ(−q²³))`. -/
theorem entry_3_29 : (S 2 G * S 23 G + X ^ 5 * S 2 H * S 23 H) * (S 46 G * H - X ^ 9 * G * S 46 H) =
    chim 1 * chim 23 + X + 2 * X ^ 2 * Ring.inverse (chim 1 * chim 23) := by
  have e1 := E1_29
  have ne1 := congrArg Ng e1
  simp only [map_mul, map_sub, Ng_Ng, Ng_X, Ng_E1, Ng_P2323, Ng_S_ev 2 (by norm_num),
    Ng_Pinf_even 1 1 le_rfl le_rfl, Ng_Pinf_even 23 23 (by norm_num) (by norm_num)] at ne1
  simp only [Nat.reduceMul] at ne1
  have e2 := E2_29
  have hm := M23
  simp only [chim, Nat.reduceMul] at hm ⊢
  have hc1 := chip_mul 1
  have hc23 := chip_mul 23
  norm_num at hc1 hc23
  have a2 : Pinf 2 2 = Pinf 2 4 * Pinf 4 4 := by
    have h := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at h
    norm_num at h
    exact h
  have a46 : Pinf 46 46 = Pinf 46 92 * Pinf 92 92 := by
    have h := congrArg (S 23) a2
    simp only [S_P' 23 2 2 (by norm_num) (by norm_num) (rfl : 46 = 23 * 2) (rfl : 46 = 23 * 2),
      S_P' 23 2 4 (by norm_num) (by norm_num) (rfl : 46 = 23 * 2) (rfl : 92 = 23 * 4),
      S_P' 23 4 4 (by norm_num) (by norm_num) (rfl : 92 = 23 * 4) (rfl : 92 = 23 * 4), map_mul] at h
    exact h
  set A := A29 with hA
  set B := B29 with hB
  set u := chip 1 * chip 23 with hu
  set v := Pinf 1 2 * Pinf 23 46 with hv
  set w := Pinf 2 4 * Pinf 46 92 with hw
  have uvw : u * v = w := by rw [hu, hv, hw]; linear_combination (chip 23 * Pinf 23 46) * hc1 + Pinf 2 4 * hc23
  have hD : Pinf 2 2 * Pinf 46 46 ≠ 0 := mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 46 46 (by norm_num) (by norm_num))
  -- `A(q²) B(q) = A(−q) (u − q)`
  have st2 : S 2 A * B = Ng A * (u - X) := by
    apply mul_left_cancel₀ hD
    linear_combination -ne1
  -- `f(−q²)f(−Q²) A B = (f(−q²)f(−Q²) + 2q² f(−q⁴)f(−Q⁴)) (u − q)`
  have st3 : Pinf 2 2 * Pinf 46 46 * (A * B) = (Pinf 2 2 * Pinf 46 46 + 2 * X ^ 2 * (Pinf 4 4 * Pinf 92 92)) * (u - X) := by
    apply mul_left_cancel₀ A29_ne
    linear_combination (Pinf 2 2 * Pinf 46 46 * A) * st2 + (u - X) * e2
  have st4 : w * (A * B) = (w + 2 * X ^ 2) * (u - X) := by
    apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 4 4 (by norm_num) (by norm_num)) (Pinf_ne 92 92 (by norm_num) (by norm_num)))
    rw [a2, a46] at st3
    linear_combination st3
  have hwu : IsUnit w := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).mul (isUnit_Pinf 46 92 (by norm_num) (by norm_num))
  have hvu : IsUnit v := (isUnit_Pinf 1 2 (by norm_num) (by norm_num)).mul (isUnit_Pinf 23 46 (by norm_num) (by norm_num))
  have iw := Ring.mul_inverse_cancel _ hwu
  have iv := Ring.mul_inverse_cancel _ hvu
  apply mul_left_cancel₀ hwu.ne_zero
  rw [show (S 2 G * S 23 G + X ^ 5 * S 2 H * S 23 H) * (S 46 G * H - X ^ 9 * G * S 46 H) = A * B from rfl]
  linear_combination st4 + w * hm + 2 * X ^ 3 * iw - 2 * X ^ 2 * u * iv + 2 * X ^ 2 * Ring.inverse v * uvw

end Forty
