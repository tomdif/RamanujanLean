/-
# Entry 3.5 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm32 : 1 ≤ 32 := by norm_num
private lemma hm160 : 1 ≤ 160 := by norm_num

/-- Entry 3.5, side a: `B = (0 -5; 1 2)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_5a : ECS where
  b11 := 0
  b12 := (-5)
  b21 := 1
  b22 := 2
  r1 := 1
  r2 := 0
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - (-5) * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), ((0 * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - 1 * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.5, side b: `B = (-1 1; 0 -2)`, shifts `i (0, 1)`, `i ∈ {(-1), 0}`. -/
def B3_5b : ECS where
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

theorem L3_5 : 2 * (θ hm10 2 1 * θ hm160 64 1) - 2 * (mono 6 1 * (θ hm10 4 1 * θ hm160 32 1)) = 2 * (θ hm8 2 1 * θ hm32 8 1) := by
  have h := qf_two 4 2 5 2 (-3) 1 1 B3_5a B3_5b
    hm10 hm160 hm8 hm32 (by norm_num [B3_5a]) (by norm_num [B3_5a]) (by norm_num [B3_5a])
    (by norm_num [B3_5b]) (by norm_num [B3_5b]) (by norm_num [B3_5b])
  simp only [B3_5a, B3_5b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm160 32 0 0 1 (e := 128) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm160 64 0 0 1 (e := 96) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm32 8 0 0 1 (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm8 2 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 4 (-1) one_ne_zero (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm32 8 1 one_ne_zero (-8) (-1) (e := 40) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 (-1) (e := (-10)) (by norm_num), θz' hm160 1 (e := 160) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_5` in `ℤ⟦q⟧`. -/
theorem P3_5 : (J 1 5 * J 32 80) - (PowerSeries.X ^ 3 * (J 2 5 * J 16 80)) = (J 1 4 * J 4 16) := by
  apply S_inj 2
  have h := L3_5
  rw [θu' hm8 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm32 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num), θu' hm160 32 (e' := 32) (by norm_num) (by norm_num) (by norm_num), θu' hm160 64 (e' := 64) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 2 10 * J 64 160) - (PowerSeries.X ^ 6 * (J 4 10 * J 32 160)))) = ι (2 * ((J 2 8 * J 8 32))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 4 (by norm_num) (by norm_num), S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 4 16 (by norm_num) (by norm_num), S_J 2 16 80 (by norm_num) (by norm_num), S_J 2 32 80 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.5** (Rogers 1921): `G(q¹⁶)H(q) − q³G(q)H(q¹⁶) = χ(q²)`. -/
theorem entry_3_5 : S 16 G * H - PowerSeries.X ^ 3 * G * S 16 H = chip 2 := by
  have hc := chip_mul 2
  norm_num at hc
  suffices h : (S 16 G * H - PowerSeries.X ^ 3 * G * S 16 H) * Pinf 2 4 = Pinf 4 8 from
    mul_right_cancel₀ (Pinf_ne 2 4 (by norm_num) (by norm_num)) (h.trans hc.symm)
  have e1 := SG_E 16
  have e2 := SH_E 16
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : J 1 4 * J 4 16 * Pinf 2 4 = Pinf 16 16 * Pinf 1 1 * Pinf 4 8 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 16]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 16 16 (by norm_num) (by norm_num)) (Pinf_ne 1 1 le_rfl le_rfl))
  linear_combination (Pinf 2 4 * (H * Pinf 1 1)) * e1 + (Pinf 2 4 * J 32 80) * e4
    - (PowerSeries.X ^ 3 * Pinf 2 4 * (S 16 H * Pinf 16 16)) * e3 - (PowerSeries.X ^ 3 * Pinf 2 4 * J 2 5) * e2
    + Pinf 2 4 * P3_5 + k

end Forty
