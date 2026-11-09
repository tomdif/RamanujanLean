/-
# Entry 3.6 via two exact covers of a binary quadratic form (Cao, arXiv:2503.11445, Type II)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm18 : 1 ≤ 18 := by norm_num
private lemma hm90 : 1 ≤ 90 := by norm_num

/-- Entry 3.6, side a: `B = (-1 -4; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_6a : ECS where
  b11 := (-1)
  b12 := (-4)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - (-4) * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), (((-1) * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - 1 * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.6, side b: `B = (-2 -1; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-1), 0, 1}`. -/
def B3_6b : ECS where
  b11 := (-2)
  b12 := (-1)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 2 * n - (-1)) % 3 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 2 * n - (-1)) % 3 + (-1))) - (-1) * (n - 0 * ((1 * m + 2 * n - (-1)) % 3 + (-1)))) / 3), (((-2) * (n - 0 * ((1 * m + 2 * n - (-1)) % 3 + (-1))) - 1 * (m - 1 * ((1 * m + 2 * n - (-1)) % 3 + (-1)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_6 : 2 * (θ hm10 4 1 * θ hm90 36 1) + 2 * (mono 4 1 * (θ hm10 2 1 * θ hm90 18 1)) = 2 * (θ hm18 6 1 * θ hm18 6 1) := by
  have h := qf_two 2 1 5 (-2) (-1) 0 1 B3_6a B3_6b
    hm10 hm90 hm18 hm18 (by norm_num [B3_6a]) (by norm_num [B3_6a]) (by norm_num [B3_6a])
    (by norm_num [B3_6b]) (by norm_num [B3_6b]) (by norm_num [B3_6b])
  simp only [B3_6a, B3_6b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm18 6 0 0 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm90 18 0 0 1 (e := 72) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm90 36 0 0 1 (e := 54) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm18 1 (e := 18) (by norm_num), θz' hm90 1 (e := 90) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_6` in `ℤ⟦q⟧`. -/
theorem P3_6 : (J 2 5 * J 18 45) + (PowerSeries.X ^ 2 * (J 1 5 * J 9 45)) = (J 3 9 * J 3 9) := by
  apply S_inj 2
  have h := L3_6
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm18 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num), θu' hm90 18 (e' := 18) (by norm_num) (by norm_num) (by norm_num), θu' hm90 36 (e' := 36) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 4 10 * J 36 90) + (PowerSeries.X ^ 4 * (J 2 10 * J 18 90)))) = ι (2 * ((J 6 18 * J 6 18))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 3 9 (by norm_num) (by norm_num), S_J 2 9 45 (by norm_num) (by norm_num), S_J 2 18 45 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2



/-- **Entry 3.6** (Rogers 1921): `G(q)G(q⁹) + q²H(q)H(q⁹) = f(−q³)²/(f(−q)f(−q⁹))`. -/
theorem entry_3_6 : G * S 9 G + PowerSeries.X ^ 2 * H * S 9 H = fm 3 ^ 2 * Ring.inverse (fm 1 * fm 9) := by
  apply eq_mul_inv_of ((isUnit_Pinf 1 1 le_rfl le_rfl).mul (isUnit_Pinf 9 9 (by norm_num) (by norm_num)))
  have e1 := SG_E 9
  have e2 := SH_E 9
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : J 3 9 * J 3 9 = Pinf 3 3 ^ 2 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 9]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  simp only [fm]
  linear_combination (S 9 G * Pinf 9 9) * e3 + J 2 5 * e1 + (PowerSeries.X ^ 2 * (S 9 H * Pinf 9 9)) * e4
    + (PowerSeries.X ^ 2 * J 1 5) * e2 + P3_6 + k

end Forty
