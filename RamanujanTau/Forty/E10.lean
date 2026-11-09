/-
# Entry 3.10 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm12 : 1 ≤ 12 := by norm_num
private lemma hm42 : 1 ≤ 42 := by norm_num
private lemma hm140 : 1 ≤ 140 := by norm_num

/-- Entry 3.10, side a: `B = (0 -5; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_10a : ECS where
  b11 := 0
  b12 := (-5)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - (-5) * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), ((0 * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - 1 * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.10, side b: `B = (-1 -2; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0}`. -/
def B3_10b : ECS where
  b11 := (-1)
  b12 := (-2)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 3 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 3 + (-2))) - (-2) * (n - 0 * ((1 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), (((-1) * (n - 0 * ((1 * m + 1 * n - (-2)) % 3 + (-2))) - 1 * (m - 1 * ((1 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_10 : 2 * (θ hm10 4 1 * θ hm140 56 1) + 2 * (mono 6 1 * (θ hm10 2 1 * θ hm140 28 1)) = 2 * (θ hm12 4 1 * θ hm42 14 1) := by
  have h := qf_two 3 1 5 3 1 0 1 B3_10a B3_10b
    hm10 hm140 hm12 hm42 (by norm_num [B3_10a]) (by norm_num [B3_10a]) (by norm_num [B3_10a])
    (by norm_num [B3_10b]) (by norm_num [B3_10b]) (by norm_num [B3_10b])
  simp only [B3_10a, B3_10b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm12 4 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm140 28 0 0 1 (e := 112) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm140 56 0 0 1 (e := 84) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm42 14 0 0 1 (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 0 (e := 0) (by norm_num), θz' hm12 1 (e := 12) (by norm_num), θz' hm140 1 (e := 140) (by norm_num), θz' hm42 1 (e := 42) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_10` in `ℤ⟦q⟧`. -/
theorem P3_10 : (J 2 5 * J 28 70) + (PowerSeries.X ^ 3 * (J 1 5 * J 14 70)) = (J 2 6 * J 7 21) := by
  apply S_inj 2
  have h := L3_10
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm12 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm42 14 (e' := 14) (by norm_num) (by norm_num) (by norm_num), θu' hm140 28 (e' := 28) (by norm_num) (by norm_num) (by norm_num), θu' hm140 56 (e' := 56) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 10 * J 56 140) + (PowerSeries.X ^ 6 * (J 2 10 * J 28 140)))) = ι (2 * ((J 4 12 * J 14 42))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 2 6 (by norm_num) (by norm_num), S_J 2 7 21 (by norm_num) (by norm_num), S_J 2 14 70 (by norm_num) (by norm_num), S_J 2 28 70 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.10** (Rogers 1921): `G(q)G(q¹⁴) + q³H(q)H(q¹⁴) = χ(−q⁷)/χ(−q)`. -/
theorem entry_3_10 : G * S 14 G + PowerSeries.X ^ 3 * H * S 14 H = chim 7 * Ring.inverse (chim 1) := by
  apply eq_mul_inv_of (isUnit_Pinf 1 2 le_rfl (by norm_num))
  have e1 := SG_E 14
  have e2 := SH_E 14
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : J 2 6 * J 7 21 * Pinf 1 2 = Pinf 1 1 * Pinf 14 14 * Pinf 7 14 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 42]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 1 1 le_rfl le_rfl) (Pinf_ne 14 14 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  linear_combination (Pinf 1 2 * (S 14 G * Pinf 14 14)) * e3 + (Pinf 1 2 * J 2 5) * e1
    + (PowerSeries.X ^ 3 * Pinf 1 2 * (S 14 H * Pinf 14 14)) * e4 + (PowerSeries.X ^ 3 * Pinf 1 2 * J 1 5) * e2
    + Pinf 1 2 * P3_10 + k

end Forty
