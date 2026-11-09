/-
# Entry 3.4: `G(q¹¹)H(q) − q²G(q)H(q¹¹) = 1`

Cao's proof (arXiv:2503.11445, §3.3): the binary quadratic form `3x² + 2xy + 4y² + x + 4y` (with sign `(−1)^x`)
is split by two exact covers of determinants 3 and 5, giving (with `t² = q`)
`2 f(−q)f(−q¹¹) = 2 f(−q,−q⁴)f(−q²²,−q³³) − 2q² f(−q²,−q³)f(−q¹¹,−q⁴⁴)`.
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm66 : 1 ≤ 66 := by norm_num
private lemma hm110 : 1 ≤ 110 := by norm_num

/-- Entry 3.4, side a: `B = (-1 1; 0 -3)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0}`. -/
def B3_4a : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-3)
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 3 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-3) * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - 1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), (((-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.4, side b: `B = (-1 -3; 1 -2)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B3_4b : ECS where
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

theorem L3_4 : 2 * (θ hm6 2 1 * θ hm66 22 1) = 2 * (θ hm10 2 1 * θ hm110 44 1) - 2 * (mono 4 1 * (θ hm10 4 1 * θ hm110 22 1)) := by
  have h := qf_two 3 1 4 1 4 1 0 B3_4a B3_4b
    hm6 hm66 hm10 hm110 (by norm_num [B3_4a]) (by norm_num [B3_4a]) (by norm_num [B3_4a])
    (by norm_num [B3_4b]) (by norm_num [B3_4b]) (by norm_num [B3_4b])
  simp only [B3_4a, B3_4b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 1 (-6) (-1) (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm110 22 0 0 1 (e := 88) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm110 44 0 0 1 (e := 66) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm6 2 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm66 22 0 0 1 (e := 44) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 2 1 one_ne_zero (-2) (-1) (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 2 (e := 20) (by norm_num), θz' hm110 1 (e := 110) (by norm_num), θz' hm6 1 (e := 6) (by norm_num), θz' hm66 1 (e := 66) (by norm_num)] at h
  simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_4` in `ℤ⟦q⟧`. -/
theorem P3_4 : J 1 3 * J 11 33 = J 1 5 * J 22 55 - PowerSeries.X ^ 2 * (J 2 5 * J 11 55) := by
  apply S_inj 2
  have h := L3_4
  rw [θu' hm6 2 (by norm_num) (by norm_num) (by norm_num), θu' hm66 22 (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (by norm_num) (by norm_num) (by norm_num), θu' hm110 44 (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (by norm_num) (by norm_num) (by norm_num), θu' hm110 22 (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * (J 2 6 * J 22 66)) =
      ι (2 * (J 2 10 * J 44 110 - PowerSeries.X ^ 4 * (J 4 10 * J 22 110))) := by
    simp only [map_mul, map_sub, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, S_J 2 1 3 le_rfl (by norm_num),
    S_J 2 11 33 (by norm_num) (by norm_num), S_J 2 1 5 le_rfl (by norm_num), S_J 2 22 55 (by norm_num) (by norm_num),
    S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 11 55 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2

/-- **Entry 3.4** (Rogers 1921, Watson 1933): `G(q¹¹)H(q) − q²G(q)H(q¹¹) = 1`. -/
theorem entry_3_4 : S 11 G * H - PowerSeries.X ^ 2 * G * S 11 H = 1 := by
  have key := two_term (k := -PowerSeries.X ^ 2) (den := 1) (num := 1) (SG_mul 11) H_mul_vv G_mul_uu (SH_mul 11) ?_
  · linear_combination key
  have hE : (Pinf 5 5 * Pinf 55 55 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (isUnit_Pinf 5 5 (by norm_num) (by norm_num)).ne_zero (isUnit_Pinf 55 55 (by norm_num) (by norm_num)).ne_zero
  apply mul_left_cancel₀ hE
  have r1 := MTC.Pinf_splitk 1 1 5 le_rfl le_rfl (by norm_num)
  have r2 := MTC.Pinf_splitk 1 1 3 le_rfl le_rfl (by norm_num)
  have r3 := MTC.Pinf_splitk 11 11 5 (by norm_num) (by norm_num) (by norm_num)
  have r4 := MTC.Pinf_splitk 11 11 3 (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at r1 r2 r3 r4
  norm_num at r1 r2 r3 r4
  have P := P3_4
  simp only [J, uu, vv, Nat.reduceMul, Nat.reduceSub, mul_one] at P ⊢
  linear_combination (-1 : PowerSeries ℤ) * P - (Pinf 11 33 * Pinf 22 33 * Pinf 33 33) * r2 - Pinf 1 1 * r4
    + Pinf 11 11 * r1 + (Pinf 1 5 * Pinf 4 5 * (Pinf 2 5 * Pinf 3 5) * Pinf 5 5) * r3
  
end Forty
