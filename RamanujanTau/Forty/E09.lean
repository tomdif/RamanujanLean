/-
# Entry 3.9 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm70 : 1 ≤ 70 := by norm_num
private lemma hm84 : 1 ≤ 84 := by norm_num

/-- Entry 3.9, side a: `B = (-1 3; -1 -2)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_9a : ECS where
  b11 := (-1)
  b12 := 3
  b21 := (-1)
  b22 := (-2)
  r1 := 1
  r2 := 0
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 4 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 1 * ((1 * m + 4 * n - (-3)) % 5 + (-3))) - 3 * (n - 0 * ((1 * m + 4 * n - (-3)) % 5 + (-3)))) / 5), (((-1) * (n - 0 * ((1 * m + 4 * n - (-3)) % 5 + (-3))) - (-1) * (m - 1 * ((1 * m + 4 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.9, side b: `B = (-1 1; 0 -3)`, shifts `i (0, 1)`, `i ∈ {(-1), 0, 1}`. -/
def B3_9b : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-3)
  r1 := 0
  r2 := 1
  I := {(-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-1)) % 3 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    (((-3) * (m - 0 * ((0 * m + 1 * n - (-1)) % 3 + (-1))) - 1 * (n - 1 * ((0 * m + 1 * n - (-1)) % 3 + (-1)))) / 3), (((-1) * (n - 1 * ((0 * m + 1 * n - (-1)) % 3 + (-1))) - 0 * (m - 0 * ((0 * m + 1 * n - (-1)) % 3 + (-1)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_9 : 2 * (θ hm20 4 1 * θ hm70 28 1) - 2 * (mono 2 1 * (θ hm20 8 1 * θ hm70 14 1)) = 2 * (θ hm6 2 1 * θ hm84 28 1) := by
  have h := qf_two 3 1 5 (-1) (-5) 1 0 B3_9a B3_9b
    hm20 hm70 hm6 hm84 (by norm_num [B3_9a]) (by norm_num [B3_9a]) (by norm_num [B3_9a])
    (by norm_num [B3_9b]) (by norm_num [B3_9b]) (by norm_num [B3_9b])
  simp only [B3_9a, B3_9b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 1 (-12) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm6 2 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm70 14 0 0 1 (e := 56) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm70 28 0 0 1 (e := 42) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm84 28 0 0 1 (e := 56) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 4 1 one_ne_zero (-4) (-1) (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 2 (e := 40) (by norm_num), θz' hm6 1 (e := 6) (by norm_num), θz' hm70 0 (e := 0) (by norm_num), θz' hm84 1 (e := 84) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_9` in `ℤ⟦q⟧`. -/
theorem P3_9 : (J 2 10 * J 14 35) - (PowerSeries.X ^ 1 * (J 4 10 * J 7 35)) = (J 1 3 * J 14 42) := by
  apply S_inj 2
  have h := L3_9
  rw [θu' hm6 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num), θu' hm70 14 (e' := 14) (by norm_num) (by norm_num) (by norm_num), θu' hm70 28 (e' := 28) (by norm_num) (by norm_num) (by norm_num), θu' hm84 28 (e' := 28) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 20 * J 28 70) - (PowerSeries.X ^ 2 * (J 8 20 * J 14 70)))) = ι (2 * ((J 2 6 * J 28 84))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 3 (by norm_num) (by norm_num), S_J 2 2 10 (by norm_num) (by norm_num), S_J 2 4 10 (by norm_num) (by norm_num), S_J 2 7 35 (by norm_num) (by norm_num), S_J 2 14 35 (by norm_num) (by norm_num), S_J 2 14 42 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.9** (Rogers 1921): `G(q⁷)H(q²) − qG(q²)H(q⁷) = χ(−q)/χ(−q⁷)`. -/
theorem entry_3_9 : S 7 G * S 2 H - PowerSeries.X * S 2 G * S 7 H = chim 1 * Ring.inverse (chim 7) := by
  apply eq_mul_inv_of (isUnit_Pinf 7 14 (by norm_num) (by norm_num))
  have e1 := SG_E 7
  have e2 := SH_E 7
  have e3 := SG_E 2
  have e4 := SH_E 2
  norm_num at e1 e2 e3 e4
  have k : J 1 3 * J 14 42 * Pinf 7 14 = Pinf 7 7 * Pinf 2 2 * Pinf 1 2 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 42]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 7 7 (by norm_num) (by norm_num)) (Pinf_ne 2 2 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  linear_combination (Pinf 7 14 * (S 2 H * Pinf 2 2)) * e1 + (Pinf 7 14 * J 14 35) * e4
    - (PowerSeries.X * Pinf 7 14 * (S 7 H * Pinf 7 7)) * e3 - (PowerSeries.X * Pinf 7 14 * J 4 10) * e2
    + Pinf 7 14 * P3_9 + k

end Forty
