/-
# Entry 3.19 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm130 : 1 ≤ 130 := by norm_num
private lemma hm390 : 1 ≤ 390 := by norm_num

/-- Entry 3.19, side a: `B = (-1 1; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_19a : ECS where
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

/-- Entry 3.19, side b: `B = (-1 3; -1 -2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_19b : ECS where
  b11 := (-1)
  b12 := 3
  b21 := (-1)
  b22 := (-2)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 4 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - 3 * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), (((-1) * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_19 : 2 * (θ hm10 4 1 * θ hm390 156 1) + 2 * (mono 16 1 * (θ hm10 2 1 * θ hm390 78 1)) = 2 * (θ hm30 6 1 * θ hm130 52 1) - 2 * (mono 4 1 * (θ hm30 12 1 * θ hm130 26 1)) := by
  have h := qf_two 5 1 8 1 8 1 0 B3_19a B3_19b
    hm10 hm390 hm30 hm130 (by norm_num [B3_19a]) (by norm_num [B3_19a]) (by norm_num [B3_19a])
    (by norm_num [B3_19b]) (by norm_num [B3_19b]) (by norm_num [B3_19b])
  simp only [B3_19a, B3_19b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm130 26 0 0 1 (e := 104) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm130 52 0 0 1 (e := 78) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 12 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 6 (-1) (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 156 0 0 1 (e := 234) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 78 0 0 1 (e := 312) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 12 (-1) one_ne_zero (-18) (-1) (e := (-18)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm130 0 (e := 0) (by norm_num), θz' hm30 1 (e := 30) (by norm_num), θz' hm390 1 (e := 390) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_19` in `ℤ⟦q⟧`. -/
theorem P3_19 : (J 2 5 * J 78 195) + (PowerSeries.X ^ 8 * (J 1 5 * J 39 195)) = (J 3 15 * J 26 65) - (PowerSeries.X ^ 2 * (J 6 15 * J 13 65)) := by
  apply S_inj 2
  have h := L3_19
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm30 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num), θu' hm30 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num), θu' hm130 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num), θu' hm130 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num), θu' hm390 78 (e' := 78) (by norm_num) (by norm_num) (by norm_num), θu' hm390 156 (e' := 156) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 10 * J 156 390) + (PowerSeries.X ^ 16 * (J 2 10 * J 78 390)))) = ι (2 * ((J 6 30 * J 52 130) - (PowerSeries.X ^ 4 * (J 12 30 * J 26 130)))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 3 15 (by norm_num) (by norm_num), S_J 2 6 15 (by norm_num) (by norm_num), S_J 2 13 65 (by norm_num) (by norm_num), S_J 2 26 65 (by norm_num) (by norm_num), S_J 2 39 195 (by norm_num) (by norm_num), S_J 2 78 195 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.19 (first equality)** (Bressoud): `{G(q)G(q³⁹) + q⁸H(q)H(q³⁹)} f(−q)f(−q³⁹)
= {G(q¹³)H(q³) − q²G(q³)H(q¹³)} f(−q³)f(−q¹³)`. -/
theorem entry_3_19_i : (G * S 39 G + PowerSeries.X ^ 8 * H * S 39 H) * (fm 1 * fm 39) =
    (S 13 G * S 3 H - PowerSeries.X ^ 2 * S 3 G * S 13 H) * (fm 3 * fm 13) := by
  have e1 := SG_E 39
  have e2 := SH_E 39
  have e5 := SG_E 13
  have e6 := SH_E 13
  have e7 := SG_E 3
  have e8 := SH_E 3
  norm_num at e1 e2 e5 e6 e7 e8
  have e3 := G_E
  have e4 := H_E
  simp only [fm]
  linear_combination (S 39 G * Pinf 39 39) * e3 + J 2 5 * e1 + (PowerSeries.X ^ 8 * (S 39 H * Pinf 39 39)) * e4
    + (PowerSeries.X ^ 8 * J 1 5) * e2 + P3_19
    - (S 3 H * Pinf 3 3) * e5 - J 26 65 * e8 + (PowerSeries.X ^ 2 * (S 13 H * Pinf 13 13)) * e7
    + (PowerSeries.X ^ 2 * J 6 15) * e6

end Forty
