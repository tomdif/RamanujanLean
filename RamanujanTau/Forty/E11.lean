/-
# Entry 3.11 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm48 : 1 ≤ 48 := by norm_num
private lemma hm80 : 1 ≤ 80 := by norm_num

/-- Entry 3.11, side a: `B = (-1 3; -1 -2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_11a : ECS where
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

/-- Entry 3.11, side b: `B = (-1 1; 0 -2)`, shifts `i (0, 1)`, `i ∈ {(-1), 0}`. -/
def B3_11b : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-2)
  r1 := 0
  r2 := 1
  I := {(-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-1)) % 2 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 0 * ((0 * m + 1 * n - (-1)) % 2 + (-1))) - 1 * (n - 1 * ((0 * m + 1 * n - (-1)) % 2 + (-1)))) / 2), (((-1) * (n - 1 * ((0 * m + 1 * n - (-1)) % 2 + (-1))) - 0 * (m - 0 * ((0 * m + 1 * n - (-1)) % 2 + (-1)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_11 : 2 * (θ hm30 6 1 * θ hm80 32 1) - 2 * (mono 2 1 * (θ hm30 12 1 * θ hm80 16 1)) = 2 * (θ hm8 2 1 * θ hm48 12 1) := by
  have h := qf_two 4 2 7 2 7 1 0 B3_11a B3_11b
    hm30 hm80 hm8 hm48 (by norm_num [B3_11a]) (by norm_num [B3_11a]) (by norm_num [B3_11a])
    (by norm_num [B3_11b]) (by norm_num [B3_11b]) (by norm_num [B3_11b])
  simp only [B3_11a, B3_11b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm30 12 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 6 (-1) (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm48 12 0 0 1 (e := 36) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm8 2 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm80 16 0 0 1 (e := 64) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm80 32 0 0 1 (e := 48) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 12 (-1) one_ne_zero (-18) (-1) (e := (-18)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm30 1 (e := 30) (by norm_num), θz' hm80 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_11` in `ℤ⟦q⟧`. -/
theorem P3_11 : (J 3 15 * J 16 40) - (PowerSeries.X ^ 1 * (J 6 15 * J 8 40)) = (J 1 4 * J 6 24) := by
  apply S_inj 2
  have h := L3_11
  rw [θu' hm8 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm30 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num), θu' hm30 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num), θu' hm48 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num), θu' hm80 16 (e' := 16) (by norm_num) (by norm_num) (by norm_num), θu' hm80 32 (e' := 32) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 6 30 * J 32 80) - (PowerSeries.X ^ 2 * (J 12 30 * J 16 80)))) = ι (2 * ((J 2 8 * J 12 48))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 4 (by norm_num) (by norm_num), S_J 2 3 15 (by norm_num) (by norm_num), S_J 2 6 15 (by norm_num) (by norm_num), S_J 2 6 24 (by norm_num) (by norm_num), S_J 2 8 40 (by norm_num) (by norm_num), S_J 2 16 40 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.11** (Rogers 1921): `G(q⁸)H(q³) − qG(q³)H(q⁸) = χ(−q)χ(−q⁴)/(χ(−q³)χ(−q¹²))`. -/
theorem entry_3_11 : S 8 G * S 3 H - PowerSeries.X * S 3 G * S 8 H =
    chim 1 * chim 4 * Ring.inverse (chim 3 * chim 12) := by
  apply eq_mul_inv_of ((isUnit_Pinf 3 6 (by norm_num) (by norm_num)).mul (isUnit_Pinf 12 24 (by norm_num) (by norm_num)))
  have e1 := SG_E 8
  have e2 := SH_E 8
  have e3 := SG_E 3
  have e4 := SH_E 3
  norm_num at e1 e2 e3 e4
  have k : J 1 4 * J 6 24 * (Pinf 3 6 * Pinf 12 24) = Pinf 8 8 * Pinf 3 3 * (Pinf 1 2 * Pinf 4 8) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 24]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 8 8 (by norm_num) (by norm_num)) (Pinf_ne 3 3 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  linear_combination ((Pinf 3 6 * Pinf 12 24) * (S 3 H * Pinf 3 3)) * e1 + ((Pinf 3 6 * Pinf 12 24) * J 16 40) * e4
    - (PowerSeries.X * (Pinf 3 6 * Pinf 12 24) * (S 8 H * Pinf 8 8)) * e3
    - (PowerSeries.X * (Pinf 3 6 * Pinf 12 24) * J 6 15) * e2
    + (Pinf 3 6 * Pinf 12 24) * P3_11 + k

end Forty
