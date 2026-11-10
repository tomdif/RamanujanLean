/-
# Entry 3.29: the evaluations `Yo_ι`, `Ye_ι`, `D5p_ι`, `D5m_ι` (see `E29c.lean`)
-/
import RamanujanTau.Forty.E29c

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "ψ" => RamanujanTau.Septic.ramF 1 3

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm230 : 1 ≤ 230 := by norm_num
private lemma hm460 : 1 ≤ 460 := by norm_num
private lemma hm1380 : 1 ≤ 1380 := by norm_num

lemma S_S8 (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] (f : PowerSeries ℤ) : S a (S b f) = S (a * b) f := by
  ext n
  simp only [coeff_S]
  have ha := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb := Nat.pos_of_ne_zero (NeZero.ne b)
  by_cases h1 : a ∣ n
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right a m), Nat.mul_div_cancel_left m ha]
    by_cases h2 : b ∣ m
    · obtain ⟨k, rfl⟩ := h2
      rw [if_pos (dvd_mul_right b k), ← mul_assoc, if_pos (dvd_mul_right _ k),
        Nat.mul_div_cancel_left k hb, Nat.mul_div_cancel_left k (Nat.mul_pos ha hb)]
    · rw [if_neg h2, if_neg]
      intro h; exact h2 ((Nat.mul_dvd_mul_iff_left ha).mp h)
  · rw [if_neg h1, if_neg]
    intro h; exact h1 (dvd_trans (dvd_mul_right a b) h)

/-- `Yo = q² f(−q⁴) f(−Q⁴) A(q²)`. -/
theorem Yo_ι : Yo = ι (X ^ 2 * Pinf 4 4 * Pinf 92 92 * (S 4 G * S 46 G + X ^ 10 * S 4 H * S 46 H)) := by
  have h := Yo_c
  rw [θu' hm460 46 (e' := 46) (by norm_num) (by norm_num) (by norm_num),
    θu' hm460 138 (e' := 138) (by norm_num) (by norm_num) (by norm_num),
    θu' hm1380 460 (e' := 460) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm460 92 (e' := 92) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm460 184 (e' := 184) (by norm_num) (by norm_num) (by norm_num)] at h
  have r1 := congrArg (S 46) R44a
  have r2 := congrArg (S 46) R44b
  simp only [map_mul, S_J' 46 2 10 (by norm_num) (by norm_num) (rfl : 92 = 46 * 2) (rfl : 460 = 46 * 10),
    S_J' 46 1 10 (by norm_num) (by norm_num) (rfl : 46 = 46 * 1) (rfl : 460 = 46 * 10),
    S_J' 46 4 10 (by norm_num) (by norm_num) (rfl : 184 = 46 * 4) (rfl : 460 = 46 * 10),
    S_J' 46 3 10 (by norm_num) (by norm_num) (rfl : 138 = 46 * 3) (rfl : 460 = 46 * 10),
    S_P' 46 10 10 (by norm_num) (by norm_num) (rfl : 460 = 46 * 10) (rfl : 460 = 46 * 10),
    S_P' 46 2 2 (by norm_num) (by norm_num) (rfl : 92 = 46 * 2) (rfl : 92 = 46 * 2)] at r1 r2
  have e1 := SG_E 4
  have e2 := SH_E 4
  norm_num at e1 e2
  have key : J 460 1380 * (X ^ 2 * (J 8 20 * J 92 460 * J 138 460) + X ^ 12 * (J 4 20 * J 184 460 * J 46 460)) =
      X ^ 2 * Pinf 4 4 * Pinf 92 92 * (S 4 G * S 46 G + X ^ 10 * S 4 H * S 46 H) * (J 46 460 * J 138 460) := by
    rw [J460_1380, ← e1, ← e2]
    linear_combination (X ^ 2 * S 4 G * Pinf 4 4 * J 138 460) * r1 + (X ^ 12 * S 4 H * Pinf 4 4 * J 46 460) * r2
  have k2 := congrArg ι key
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat] at k2
  apply mul_right_cancel₀ (ι_ne29 (mul_ne_zero (J_ne29 46 460 (by norm_num) (by norm_num))
    (J_ne29 138 460 (by norm_num) (by norm_num))))
  rw [map_mul ι (J 46 460)]
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat]
  linear_combination h + k2

/-- `Ye = f(−q⁴) f(−Q⁴) A(q⁴) B(−q²)`. -/
theorem Ye_ι : Ye = ι (Pinf 4 4 * Pinf 92 92 * (S 8 G * S 92 G + X ^ 20 * S 8 H * S 92 H) *
    (S 92 G * S 2 (Ng H) + X ^ 18 * S 2 (Ng G) * S 92 H)) := by
  have h := Ye_c
  rw [θu' hm460 92 (e' := 92) (by norm_num) (by norm_num) (by norm_num),
    θu' hm460 184 (e' := 184) (by norm_num) (by norm_num) (by norm_num),
    θu' hm1380 460 (e' := 460) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num)] at h
  have g1 := SG_E 92
  have g2 := SH_E 92
  have gh := SGH_E 92
  norm_num at g1 g2 gh
  have a1 := congrArg (S 2) R46a
  have a2 := congrArg (S 2) R46b
  have a3 := congrArg (S 2) NgE33
  simp only [map_mul, map_add, S_S8 2 4, S_J' 2 3 10 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 20 = 2 * 10),
    S_J' 2 1 10 (by norm_num) (by norm_num) (rfl : 2 = 2 * 1) (rfl : 20 = 2 * 10),
    S_J' 2 5 10 (by norm_num) (by norm_num) (rfl : 10 = 2 * 5) (rfl : 20 = 2 * 10),
    S_P' 2 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 4 = 2 * 2), map_pow,
    show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _, Nat.reduceMul] at a1 a2 a3
  have key : J 460 1380 * (J 6 20 * J 184 460 * J 184 460 + X ^ 38 * (J 2 20 * J 92 460 * J 92 460)
      + X ^ 18 * (J 10 20 * J 92 460 * J 184 460)) =
      Pinf 4 4 * Pinf 92 92 * (S 8 G * S 92 G + X ^ 20 * S 8 H * S 92 H) *
        (S 92 G * S 2 (Ng H) + X ^ 18 * S 2 (Ng G) * S 92 H) * (J 92 460 * J 184 460) := by
    rw [J460_1380, ← gh, ← g1, ← g2, a1, a2, ← a3]
    ring
  have k2 := congrArg ι key
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat] at k2
  apply mul_right_cancel₀ (ι_ne29 (mul_ne_zero (J_ne29 92 460 (by norm_num) (by norm_num))
    (J_ne29 184 460 (by norm_num) (by norm_num))))
  rw [map_mul ι (J 92 460)]
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat]
  linear_combination h + k2

/-- `D5p = f(−q²) f(−Q²) A(q²)`. -/
theorem D5p_ι : D5p = ι (Pinf 2 2 * Pinf 46 46 * (S 4 G * S 46 G + X ^ 10 * S 4 H * S 46 H)) := by
  have h := D5p_c
  have b2 := θ_bar hm10 2 (by norm_num) (by norm_num)
  have b4 := θ_bar hm10 4 (by norm_num) (by norm_num)
  norm_num at b2 b4
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm230 92 (e' := 92) (by norm_num) (by norm_num) (by norm_num),
    θu' hm230 46 (e' := 46) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num)] at h
  have e1 := SG_E 4
  have e2 := SH_E 4
  have e3 := SG_E 46
  have e4 := SH_E 46
  norm_num at e1 e2 e3 e4
  have k := K1
  have key : J 10 30 * (J 92 230 * J 4 10 * (J 8 20 * J 10 20) * J 2 10
      + X ^ 10 * (J 46 230 * J 8 10 * (J 4 20 * J 10 20) * J 4 10)) =
      Pinf 2 2 * Pinf 46 46 * (S 4 G * S 46 G + X ^ 10 * S 4 H * S 46 H) * ((J 4 20 * J 10 20) * (J 8 20 * J 10 20)) := by
    apply mul_right_cancel₀ (Pinf_ne 4 4 (by norm_num) (by norm_num))
    rw [J10_30, J8_10, ← e1, ← e2, ← e3, ← e4] at *
    linear_combination (Pinf 46 46 * J 10 20 * Pinf 4 4 * (S 46 G * S 4 G + X ^ 10 * S 46 H * S 4 H)) * k
  have k2 := congrArg ι key
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat] at k2
  have h' : D5p * ((θ hm10 2 (-1) * ι (J 2 10)) * (θ hm10 4 (-1) * ι (J 4 10))) = ι (J 10 30) *
      (ι (J 92 230) * ι (J 4 10) * (θ hm10 4 (-1) * ι (J 4 10)) * ι (J 2 10)
        + mono 10 1 * (ι (J 46 230) * ι (J 8 10) * (θ hm10 2 (-1) * ι (J 2 10)) * ι (J 4 10))) := by
    linear_combination (ι (J 2 10) * ι (J 4 10)) * h
  rw [b2, b4] at h'
  have hne : ι (J 4 20) * ι (J 10 20) * (ι (J 8 20) * ι (J 10 20)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 4 20 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 10 20 (by norm_num) (by norm_num))))
      (mul_ne_zero (ι_ne29 (J_ne29 8 20 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 10 20 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

lemma Ng_A29 : Ng A29 = S 2 G * S 23 (Ng G) - X ^ 5 * S 2 H * S 23 (Ng H) := by
  simp only [A29, map_add, map_mul, map_pow, Ng_S_ev 2 (by norm_num), Ng_S_odd8 23 (by decide), Ng_X]
  ring

/-- `D5m = f(−q²) f(−Q²) A(q) A(−q)`. -/
theorem D5m_ι : D5m = ι (Pinf 2 2 * Pinf 46 46 * A29 * Ng A29) := by
  have h := D5m_c
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num)] at h
  have c1 := θ_bar hm230 92 (by norm_num) (by norm_num)
  have c2 := θ_bar hm230 46 (by norm_num) (by norm_num)
  have c0 := θ_bar0 hm230
  norm_num at c1 c2 c0
  have h' : D5m * (ι (J 2 10) * ι (J 4 10)) * (ι (J 92 230) * ι (J 46 230) * ι (Pinf 230 460)) = ι (J 10 30) *
      ((θ hm230 92 (-1) * ι (J 92 230)) * ι (J 4 10) * ι (J 4 10) * ι (J 46 230) * ι (Pinf 230 460)
        - mono 10 1 * ((θ hm230 46 (-1) * ι (J 46 230)) * ι (J 8 10) * ι (J 2 10) * ι (J 92 230) * ι (Pinf 230 460))
        - mono 28 1 * ((θ hm230 0 (-1) * ι (Pinf 230 460)) * ι (J 2 10) * ι (J 4 10) * ι (J 92 230) * ι (J 46 230))) := by
    linear_combination (ι (J 92 230) * ι (J 46 230) * ι (Pinf 230 460)) * h
  rw [c1, c2, c0] at h'
  have G23 := congrArg (S 23) GNgG
  have H23 := congrArg (S 23) HNgH
  have E23 := congrArg (S 23) E21c
  have p230 := congrArg (S 230) psi_mul
  simp only [map_mul, map_sub, map_ofNat, map_pow, S_S8 23 10, show (S 23) X = X ^ 23 from RankProof.Ea_X 23 _,
    S_J' 23 4 10 (by norm_num) (by norm_num) (rfl : 92 = 23 * 4) (rfl : 230 = 23 * 10),
    S_J' 23 2 10 (by norm_num) (by norm_num) (rfl : 46 = 23 * 2) (rfl : 230 = 23 * 10),
    S_J' 23 8 20 (by norm_num) (by norm_num) (rfl : 184 = 23 * 8) (rfl : 460 = 23 * 20),
    S_J' 23 4 20 (by norm_num) (by norm_num) (rfl : 92 = 23 * 4) (rfl : 460 = 23 * 20),
    S_J' 23 10 20 (by norm_num) (by norm_num) (rfl : 230 = 23 * 10) (rfl : 460 = 23 * 20),
    S_P' 23 2 2 (by norm_num) (by norm_num) (rfl : 46 = 23 * 2) (rfl : 46 = 23 * 2),
    S_P' 230 1 2 (by norm_num) (by norm_num) (rfl : 230 = 230 * 1) (rfl : 460 = 230 * 2),
    S_P' 230 2 2 (by norm_num) (by norm_num) (rfl : 460 = 230 * 2) (rfl : 460 = 230 * 2), Nat.reduceMul] at G23 H23 E23 p230
  have e1 := SG_E 2
  have e2 := SH_E 2
  have sgh := SGH_E 2
  norm_num at e1 e2 sgh
  have key : J 10 30 * (J 184 460 * J 230 460 * J 4 10 * J 4 10 * J 46 230 * Pinf 230 460
      - X ^ 10 * (J 92 460 * J 230 460 * J 8 10 * J 2 10 * J 92 230 * Pinf 230 460)
      - X ^ 28 * (2 * Pinf 460 460 * J 2 10 * J 4 10 * J 92 230 * J 46 230)) =
      Pinf 2 2 * Pinf 46 46 * (S 2 G * S 23 G + X ^ 5 * S 2 H * S 23 H) *
        (S 2 G * S 23 (Ng G) - X ^ 5 * S 2 H * S 23 (Ng H)) *
        (J 2 10 * J 4 10 * (J 92 230 * J 46 230 * Pinf 230 460)) := by
    rw [J10_30, J8_10, ← e1, ← e2, ← sgh]
    linear_combination
      (-(S 2 G * S 2 H * Pinf 2 2 * (S 2 G * Pinf 2 2) ^ 2 * J 46 230 * Pinf 230 460)) * G23
      + (S 2 G * S 2 H * Pinf 2 2 * X ^ 10 * (S 2 H * Pinf 2 2) ^ 2 * J 92 230 * Pinf 230 460) * H23
      + (Pinf 2 2 * X ^ 5 * S 2 G * S 2 H * (S 2 H * S 2 G * Pinf 2 2 ^ 2) * J 92 230 * J 46 230 * Pinf 230 460) * E23
      + (2 * X ^ 28 * S 2 G ^ 2 * S 2 H ^ 2 * Pinf 2 2 ^ 3 * J 92 230 * J 46 230) * p230
  have k2 := congrArg ι key
  simp only [map_mul, map_add, map_sub, map_ofNat, ι_Xpow, Nat.cast_ofNat] at k2
  rw [Ng_A29, A29]
  have hne : ι (J 2 10) * ι (J 4 10) * (ι (J 92 230) * ι (J 46 230) * ι (Pinf 230 460)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 2 10 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 4 10 (by norm_num) (by norm_num))))
      (mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 92 230 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 46 230 (by norm_num) (by norm_num))))
        (ι_ne29 (Pinf_ne 230 460 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, map_sub, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

end Forty
