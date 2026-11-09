/-
# Entry 3.28 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm170 : 1 ≤ 170 := by norm_num
private lemma hm340 : 1 ≤ 340 := by norm_num

/-- Entry 3.28, side a: `B = (-1 -3; 1 -2)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_28a : ECS where
  b11 := (-1)
  b12 := (-3)
  b21 := 1
  b22 := (-2)
  r1 := 1
  r2 := 0
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 1 * ((1 * m + 1 * n - (-3)) % 5 + (-3))) - (-3) * (n - 0 * ((1 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), (((-1) * (n - 0 * ((1 * m + 1 * n - (-3)) % 5 + (-3))) - 1 * (m - 1 * ((1 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.28, side b: `B = (-1 1; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_28b : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-5)
  r1 := 0
  r2 := 1
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    (((-5) * (m - 0 * ((0 * m + 1 * n - (-3)) % 5 + (-3))) - 1 * (n - 1 * ((0 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), (((-1) * (n - 1 * ((0 * m + 1 * n - (-3)) % 5 + (-3))) - 0 * (m - 0 * ((0 * m + 1 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_28 : 2 * (θ hm20 4 1 * θ hm170 68 1) - 2 * (mono 6 1 * (θ hm20 8 1 * θ hm170 34 1)) = 2 * (θ hm10 4 1 * θ hm340 136 1) + 2 * (mono 14 1 * (θ hm10 2 1 * θ hm340 68 1)) := by
  have h := qf_two 5 1 7 1 7 1 0 B3_28a B3_28b
    hm20 hm170 hm10 hm340 (by norm_num [B3_28a]) (by norm_num [B3_28a]) (by norm_num [B3_28a])
    (by norm_num [B3_28b]) (by norm_num [B3_28b]) (by norm_num [B3_28b])
  simp only [B3_28a, B3_28b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm170 34 0 0 1 (e := 136) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm170 68 0 0 1 (e := 102) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 1 (-12) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm340 136 0 0 1 (e := 204) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm340 68 0 0 1 (e := 272) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 4 1 one_ne_zero (-4) (-1) (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm170 1 (e := 170) (by norm_num), θz' hm20 2 (e := 40) (by norm_num), θz' hm340 1 (e := 340) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_28` in `ℤ⟦q⟧`. -/
theorem P3_28 : (J 2 10 * J 34 85) - (PowerSeries.X ^ 3 * (J 4 10 * J 17 85)) = (J 2 5 * J 68 170) + (PowerSeries.X ^ 7 * (J 1 5 * J 34 170)) := by
  apply S_inj 2
  have h := L3_28
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num), θu' hm170 34 (e' := 34) (by norm_num) (by norm_num) (by norm_num), θu' hm170 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num), θu' hm340 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num), θu' hm340 136 (e' := 136) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 20 * J 68 170) - (PowerSeries.X ^ 6 * (J 8 20 * J 34 170)))) = ι (2 * ((J 4 10 * J 136 340) + (PowerSeries.X ^ 14 * (J 2 10 * J 68 340)))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 2 10 (by norm_num) (by norm_num), S_J 2 4 10 (by norm_num) (by norm_num), S_J 2 17 85 (by norm_num) (by norm_num), S_J 2 34 85 (by norm_num) (by norm_num), S_J 2 34 170 (by norm_num) (by norm_num), S_J 2 68 170 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.28 (first part)** (Bressoud): with `U = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷)` and
`V = G(q)G(q³⁴) + q⁷H(q)H(q³⁴)`, `U/V = χ(−q)/χ(−q¹⁷)`. -/
theorem entry_3_28_i : S 17 G * S 2 H - PowerSeries.X ^ 3 * S 2 G * S 17 H =
    (G * S 34 G + PowerSeries.X ^ 7 * H * S 34 H) * chim 1 * Ring.inverse (chim 17) := by
  apply eq_mul_inv_of (isUnit_Pinf 17 34 (by norm_num) (by norm_num))
  have e1 := SG_E 17
  have e2 := SH_E 17
  have e3 := SG_E 2
  have e4 := SH_E 2
  have e5 := SG_E 34
  have e6 := SH_E 34
  norm_num at e1 e2 e3 e4 e5 e6
  have e7 := G_E
  have e8 := H_E
  have k : Pinf 1 1 * Pinf 34 34 * Pinf 17 34 = Pinf 17 17 * Pinf 2 2 * Pinf 1 2 := by
    simp (disch := norm_num) only [atom _ _ 34]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 17 17 (by norm_num) (by norm_num)) (Pinf_ne 2 2 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  set V := G * S 34 G + PowerSeries.X ^ 7 * H * S 34 H
  have hV : V * (Pinf 1 1 * Pinf 34 34) = J 2 5 * J 68 170 + PowerSeries.X ^ 7 * (J 1 5 * J 34 170) := by
    simp only [V]
    linear_combination (S 34 G * Pinf 34 34) * e7 + J 2 5 * e5 + (PowerSeries.X ^ 7 * (S 34 H * Pinf 34 34)) * e8
      + (PowerSeries.X ^ 7 * J 1 5) * e6
  linear_combination (Pinf 17 34 * (S 2 H * Pinf 2 2)) * e1 + (Pinf 17 34 * J 34 85) * e4
    - (PowerSeries.X ^ 3 * Pinf 17 34 * (S 17 H * Pinf 17 17)) * e3 - (PowerSeries.X ^ 3 * Pinf 17 34 * J 4 10) * e2
    + Pinf 17 34 * P3_28 - Pinf 17 34 * hV + V * k

end Forty
