/-
# Entry 3.14: `G(q³⁶)H(q) − q⁷G(q)H(q³⁶) = χ(−q⁶)χ(−q⁹)/(χ(−q²)χ(−q³))`

Cao (64): the form `5x²+4xy+8y²+3x−6y` with sign `(−1)^{x+y}` shows that the theta numerators of Entries 3.13 and
3.14 agree (`P3_14`). Entry 3.13 then gives 3.14, after a product identity among the `χ`s.
-/
import RamanujanTau.Forty.E13

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm40 : 1 ≤ 40 := by norm_num
private lemma hm90 : 1 ≤ 90 := by norm_num
private lemma hm360 : 1 ≤ 360 := by norm_num

/-- Entry 3.14, side a: `B = (2 1; -1 2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_14a : ECS where
  b11 := 2
  b12 := 1
  b21 := (-1)
  b22 := 2
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 2 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 1 * ((1 * m + 2 * n - (-2)) % 5 + (-2))) - 1 * (n - 0 * ((1 * m + 2 * n - (-2)) % 5 + (-2)))) / 5), ((2 * (n - 0 * ((1 * m + 2 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 2 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.14, side b: `B = (1 -2; 0 5)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_14b : ECS where
  b11 := 1
  b12 := (-2)
  b21 := 0
  b22 := 5
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((5 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - (-2) * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_14 : 2 * (θ hm40 8 1 * θ hm90 36 1) - 2 * (mono 2 1 * (θ hm40 16 1 * θ hm90 18 1)) = 2 * (θ hm10 2 1 * θ hm360 144 1) - 2 * (mono 14 1 * (θ hm10 4 1 * θ hm360 72 1)) := by
  have h := qf_two 5 2 8 3 (-6) 1 1 B3_14a B3_14b
    hm40 hm90 hm10 hm360 (by norm_num [B3_14a]) (by norm_num [B3_14a]) (by norm_num [B3_14a])
    (by norm_num [B3_14b]) (by norm_num [B3_14b]) (by norm_num [B3_14b])
  simp only [B3_14a, B3_14b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 1 (-6) (-1) (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm360 144 0 0 1 (e := 216) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm360 72 0 0 1 (e := 288) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm40 16 1 (-24) (-1) (e := 64) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm40 8 0 0 1 (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm90 18 0 0 1 (e := 72) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm90 36 0 0 1 (e := 54) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 2 1 one_ne_zero (-2) (-1) (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm40 8 1 one_ne_zero (-8) (-1) (e := 48) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 0 (e := 0) (by norm_num), θz' hm360 0 (e := 0) (by norm_num), θz' hm40 0 (e := 0) (by norm_num), θz' hm90 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_14` in `ℤ⟦q⟧`. -/
theorem P3_14 : (J 4 20 * J 18 45) - (PowerSeries.X ^ 1 * (J 8 20 * J 9 45)) = (J 1 5 * J 72 180) - (PowerSeries.X ^ 7 * (J 2 5 * J 36 180)) := by
  apply S_inj 2
  have h := L3_14
  rw [θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm40 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num), θu' hm40 16 (e' := 16) (by norm_num) (by norm_num) (by norm_num), θu' hm90 18 (e' := 18) (by norm_num) (by norm_num) (by norm_num), θu' hm90 36 (e' := 36) (by norm_num) (by norm_num) (by norm_num), θu' hm360 72 (e' := 72) (by norm_num) (by norm_num) (by norm_num), θu' hm360 144 (e' := 144) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 8 40 * J 36 90) - (PowerSeries.X ^ 2 * (J 16 40 * J 18 90)))) = ι (2 * ((J 2 10 * J 144 360) - (PowerSeries.X ^ 14 * (J 4 10 * J 72 360)))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 5 (by norm_num) (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 4 20 (by norm_num) (by norm_num), S_J 2 8 20 (by norm_num) (by norm_num), S_J 2 9 45 (by norm_num) (by norm_num), S_J 2 18 45 (by norm_num) (by norm_num), S_J 2 36 180 (by norm_num) (by norm_num), S_J 2 72 180 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2


/-- **Entry 3.14** (Bressoud; Cao (64)): `G(q³⁶)H(q) − q⁷G(q)H(q³⁶) = χ(−q⁶)χ(−q⁹)/(χ(−q²)χ(−q³))`. -/
theorem entry_3_14 : S 36 G * H - PowerSeries.X ^ 7 * G * S 36 H =
    chim 6 * chim 9 * Ring.inverse (chim 2 * chim 3) := by
  apply eq_mul_inv_of ((isUnit_Pinf 2 4 (by norm_num) (by norm_num)).mul (isUnit_Pinf 3 6 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  have h13 := entry_3_13
  have hu : IsUnit (Pinf 3 6 * Pinf 18 36) :=
    (isUnit_Pinf 3 6 (by norm_num) (by norm_num)).mul (isUnit_Pinf 18 36 (by norm_num) (by norm_num))
  simp only [chim, Nat.reduceMul] at h13
  have h13' : (S 9 G * S 4 H - PowerSeries.X * S 4 G * S 9 H) * (Pinf 3 6 * Pinf 18 36) = Pinf 1 2 * Pinf 6 12 := by
    rw [h13, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]
  have e1 := SG_E 9
  have e2 := SH_E 9
  have e3 := SG_E 4
  have e4 := SH_E 4
  have e5 := SG_E 36
  have e6 := SH_E 36
  norm_num at e1 e2 e3 e4 e5 e6
  have e7 := G_E
  have e8 := H_E
  have hL : (S 9 G * S 4 H - PowerSeries.X * S 4 G * S 9 H) * (Pinf 9 9 * Pinf 4 4) =
      J 18 45 * J 4 20 - PowerSeries.X * (J 8 20 * J 9 45) := by
    linear_combination (S 4 H * Pinf 4 4) * e1 + J 18 45 * e4 - PowerSeries.X * (S 9 H * Pinf 9 9) * e3
      - PowerSeries.X * J 8 20 * e2
  have hR : (S 36 G * H - PowerSeries.X ^ 7 * G * S 36 H) * (Pinf 36 36 * Pinf 1 1) =
      J 72 180 * J 1 5 - PowerSeries.X ^ 7 * (J 2 5 * J 36 180) := by
    linear_combination (H * Pinf 1 1) * e5 + J 72 180 * e8 - PowerSeries.X ^ 7 * (S 36 H * Pinf 36 36) * e7
      - PowerSeries.X ^ 7 * J 2 5 * e6
  have P := P3_14
  simp only [pow_one] at P
  have K : Pinf 1 2 * Pinf 6 12 * (Pinf 9 9 * Pinf 4 4) * (Pinf 2 4 * Pinf 3 6) =
      Pinf 6 12 * Pinf 9 18 * (Pinf 36 36 * Pinf 1 1) * (Pinf 3 6 * Pinf 18 36) := by
    simp (disch := norm_num) only [atom _ _ 36]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hW : (Pinf 36 36 * Pinf 1 1) * (Pinf 3 6 * Pinf 18 36) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Pinf_ne 36 36 (by norm_num) (by norm_num)) (Pinf_ne 1 1 le_rfl le_rfl))
      (mul_ne_zero (Pinf_ne 3 6 (by norm_num) (by norm_num)) (Pinf_ne 18 36 (by norm_num) (by norm_num)))
  apply mul_left_cancel₀ hW
  linear_combination (Pinf 2 4 * Pinf 3 6 * (Pinf 3 6 * Pinf 18 36)) * hR
    - (Pinf 2 4 * Pinf 3 6 * (Pinf 3 6 * Pinf 18 36)) * P
    + (Pinf 2 4 * Pinf 3 6 * (Pinf 9 9 * Pinf 4 4)) * h13'
    - (Pinf 2 4 * Pinf 3 6 * (Pinf 3 6 * Pinf 18 36)) * hL + K

end Forty
