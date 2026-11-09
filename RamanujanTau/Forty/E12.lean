/-
# Entry 3.12 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm16 : 1 ≤ 16 := by norm_num
private lemma hm24 : 1 ≤ 24 := by norm_num
private lemma hm240 : 1 ≤ 240 := by norm_num

/-- Entry 3.12, side a: `B = (-1 1; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_12a : ECS where
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

/-- Entry 3.12, side b: `B = (-1 -1; 1 -1)`, shifts `i (0, 1)`, `i ∈ {(-1), 0}`. -/
def B3_12b : ECS where
  b11 := (-1)
  b12 := (-1)
  b21 := 1
  b22 := (-1)
  r1 := 0
  r2 := 1
  I := {(-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-1)) % 2 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 0 * ((1 * m + 1 * n - (-1)) % 2 + (-1))) - (-1) * (n - 1 * ((1 * m + 1 * n - (-1)) % 2 + (-1)))) / 2), (((-1) * (n - 1 * ((1 * m + 1 * n - (-1)) % 2 + (-1))) - 1 * (m - 0 * ((1 * m + 1 * n - (-1)) % 2 + (-1)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_12 : 2 * (θ hm10 4 1 * θ hm240 96 1) + 2 * (mono 10 1 * (θ hm10 2 1 * θ hm240 48 1)) = 2 * (θ hm16 4 1 * θ hm24 6 1) := by
  have h := qf_two 5 1 5 1 5 1 0 B3_12a B3_12b
    hm10 hm240 hm16 hm24 (by norm_num [B3_12a]) (by norm_num [B3_12a]) (by norm_num [B3_12a])
    (by norm_num [B3_12b]) (by norm_num [B3_12b]) (by norm_num [B3_12b])
  simp only [B3_12a, B3_12b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm16 4 0 0 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm24 6 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm240 48 0 0 1 (e := 192) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm240 96 0 0 1 (e := 144) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm240 1 (e := 240) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_12` in `ℤ⟦q⟧`. -/
theorem P3_12 : (J 2 5 * J 48 120) + (PowerSeries.X ^ 5 * (J 1 5 * J 24 120)) = (J 2 8 * J 3 12) := by
  apply S_inj 2
  have h := L3_12
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm16 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm24 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num), θu' hm240 48 (e' := 48) (by norm_num) (by norm_num) (by norm_num), θu' hm240 96 (e' := 96) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 10 * J 96 240) + (PowerSeries.X ^ 10 * (J 2 10 * J 48 240)))) = ι (2 * ((J 4 16 * J 6 24))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 2 8 (by norm_num) (by norm_num), S_J 2 3 12 (by norm_num) (by norm_num), S_J 2 24 120 (by norm_num) (by norm_num), S_J 2 48 120 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.12** (Bressoud): `G(q)G(q²⁴) + q⁵H(q)H(q²⁴) = χ(−q³)χ(−q¹²)/(χ(−q)χ(−q⁴))`. -/
theorem entry_3_12 : G * S 24 G + PowerSeries.X ^ 5 * H * S 24 H =
    chim 3 * chim 12 * Ring.inverse (chim 1 * chim 4) := by
  apply eq_mul_inv_of ((isUnit_Pinf 1 2 le_rfl (by norm_num)).mul (isUnit_Pinf 4 8 (by norm_num) (by norm_num)))
  have e1 := SG_E 24
  have e2 := SH_E 24
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : J 2 8 * J 3 12 * (Pinf 1 2 * Pinf 4 8) = Pinf 1 1 * Pinf 24 24 * (Pinf 3 6 * Pinf 12 24) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 24]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 1 1 le_rfl le_rfl) (Pinf_ne 24 24 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  linear_combination ((Pinf 1 2 * Pinf 4 8) * (S 24 G * Pinf 24 24)) * e3 + ((Pinf 1 2 * Pinf 4 8) * J 2 5) * e1
    + (PowerSeries.X ^ 5 * (Pinf 1 2 * Pinf 4 8) * (S 24 H * Pinf 24 24)) * e4
    + (PowerSeries.X ^ 5 * (Pinf 1 2 * Pinf 4 8) * J 1 5) * e2
    + (Pinf 1 2 * Pinf 4 8) * P3_12 + k

end Forty
