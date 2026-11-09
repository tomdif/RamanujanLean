/-
# Entry 3.30: `{G(q¹⁹)H(q⁴) − q³G(q⁴)H(q¹⁹)}/{G(q⁷⁶)H(−q) + q¹⁵G(−q)H(q⁷⁶)} = χ(−q²)/χ(−q³⁸)`

Yesilyurt's proof in Cao's language (arXiv:2503.11445, Identity 30): the form `10x²+8xy+13y²+6x+10y` with sign
`(−1)^{x+y}` (`L3_30`), four quintuple collapses (`M3_30`), Cao (59) at `q¹⁹`, and the product forms of `G(−q)` and
`H(−q)` (`NgOdd`).
-/
import RamanujanTau.Forty.E13
import RamanujanTau.Forty.NgOdd

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm190 : 1 ≤ 190 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm380 : 1 ≤ 380 := by norm_num
private lemma hm570 : 1 ≤ 570 := by norm_num

/-- Entry 3.30, side a: `B = (1 -2; 0 5)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_30a : ECS where
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

/-- Entry 3.30, side b: `B = (1 3; -1 2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_30b : ECS where
  b11 := 1
  b12 := 3
  b21 := (-1)
  b22 := 2
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - 3 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_30 : (θ hm20 4 1 * θ hm570 247 1) - (mono 3 1 * (θ hm20 8 1 * θ hm570 209 1)) + (mono 19 1 * (θ hm20 4 1 * θ hm570 133 1)) - (mono 60 1 * (θ hm20 8 1 * θ hm570 19 1)) = (θ hm30 11 (-1) * θ hm380 152 1) - (mono 3 1 * (θ hm30 1 (-1) * θ hm380 152 1)) + (mono 15 1 * (θ hm30 13 (-1) * θ hm380 76 1)) - (mono 16 1 * (θ hm30 7 (-1) * θ hm380 76 1)) := by
  have h := qf_two 10 4 13 6 10 1 1 B3_30a B3_30b
    hm20 hm570 hm30 hm380 (by norm_num [B3_30a]) (by norm_num [B3_30a]) (by norm_num [B3_30a])
    (by norm_num [B3_30b]) (by norm_num [B3_30b]) (by norm_num [B3_30b])
  simp only [B3_30a, B3_30b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 1 (-12) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm380 152 0 0 1 (e := 228) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm380 76 0 0 1 (e := 304) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm570 133 0 0 1 (e := 437) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm570 19 0 0 1 (e := 551) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm570 247 0 0 1 (e := 323) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 1 (-1) (-1) 1 (e := (-1)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 13 (-1) (-13) 1 (e := (-13)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 7 0 0 1 (e := 23) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 4 1 one_ne_zero (-4) (-1) (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 5 1 (by norm_num : (-1 : ℂ) ≠ 0) (-5) 1 (e := 35) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 0 (e := 0) (by norm_num), θz' hm380 1 (e := 380) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- `L3_30` with four quintuple collapses (`c = 1` at nome `q¹⁹⁰`, `c = −1` at nome `q¹⁰`). -/
theorem M3_30 : θ hm570 190 1 * (θ hm20 4 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 1 (-1) * θ hm190 38 1
      - mono 3 1 * (θ hm20 8 1 * θ hm190 19 1 * θ hm10 3 (-1) * θ hm10 1 (-1) * θ hm190 76 1)) =
    θ hm30 10 1 * (θ hm380 152 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 1 (-1) * θ hm10 4 1
      + mono 15 1 * (θ hm380 76 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 2 1)) := by
  have hLat := L3_30
  have Q1 := quint1 hm190 hm570 rfl 19 247 437 190 38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm190 hm570 rfl 57 361 551 190 114 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q3 := quintm hm10 hm30 rfl 3 19 29 10 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q4 := quintm hm10 hm30 rfl 1 13 23 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm570 133 437 (by norm_num)] at Q1
  rw [θ_refl1 hm570 209 361 (by norm_num), θ_refl1 hm570 19 551 (by norm_num), θ_refl1 hm190 76 114 (by norm_num)] at Q2
  rw [θ_reflm hm30 11 19 (by norm_num), θ_reflm hm30 1 29 (by norm_num), θ_refl1 hm10 4 6 (by norm_num)] at Q3
  rw [θ_reflm hm30 7 23 (by norm_num)] at Q4
  have m1 : (mono 3 1 : L) * mono 57 1 = mono 60 1 := by rw [mono_mul]; norm_num
  have m2 : (mono 15 1 : L) * mono 1 1 = mono 16 1 := by rw [mono_mul]; norm_num
  linear_combination (θ hm190 19 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * hLat
    - (θ hm20 4 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * Q1
    + (mono 3 1 * θ hm20 8 1 * θ hm190 19 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * Q2
    + (θ hm380 152 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 1 (-1)) * Q3
    + (mono 15 1 * θ hm380 76 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 3 (-1)) * Q4
    - (θ hm20 8 1 * θ hm570 19 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * m1
    + (θ hm30 7 (-1) * θ hm380 76 1 * θ hm190 19 1 * θ hm190 57 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * m2


private lemma J_ne30 (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- the product form of `M3_30`. -/
theorem P3_30 : J 190 570 * (J 4 20 * J 57 190 * (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 38 190
      - PowerSeries.X ^ 3 * (J 8 20 * J 19 190 * (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 76 190)) =
    J 10 30 * (J 152 380 * J 19 190 * J 57 190 * (J 2 20 * J 10 20) * J 3 10 * J 4 10
      + PowerSeries.X ^ 15 * (J 76 380 * J 19 190 * J 57 190 * (J 6 20 * J 10 20) * J 1 10 * J 2 10)) := by
  apply ι_inj
  have h := congrArg (· * (ι (J 3 10) * ι (J 1 10))) M3_30
  simp only at h
  have hb3 := θ_bar hm10 3 (by norm_num) (by norm_num)
  have hb1 := θ_bar hm10 1 le_rfl (by norm_num)
  norm_num at hb3 hb1
  rw [θu' hm570 190 (e' := 190) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 19 (e' := 19) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 38 (e' := 38) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 57 (e' := 57) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 76 (e' := 76) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm380 152 (e' := 152) (by norm_num) (by norm_num) (by norm_num),
    θu' hm380 76 (e' := 76) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, map_add, ι_Xpow] at hb3 hb1 h ⊢
  push_cast at h ⊢
  linear_combination h
    - (ι (J 190 570) * (ι (J 4 20) * ι (J 57 190) * ι (J 38 190) - mono 3 1 * (ι (J 8 20) * ι (J 19 190) * ι (J 76 190)))
        * (θ hm10 1 (-1) * ι (J 1 10))) * hb3
    - (ι (J 190 570) * (ι (J 4 20) * ι (J 57 190) * ι (J 38 190) - mono 3 1 * (ι (J 8 20) * ι (J 19 190) * ι (J 76 190)))
        * (ι (J 6 20) * ι (J 10 20))) * hb1
    + (ι (J 10 30) * (ι (J 152 380) * ι (J 19 190) * ι (J 57 190) * ι (J 4 10)) * ι (J 3 10)) * hb1
    + (ι (J 10 30) * mono 15 1 * (ι (J 76 380) * ι (J 19 190) * ι (J 57 190) * ι (J 2 10)) * ι (J 1 10)) * hb3

/-- **Entry 3.30** (Yesilyurt 2009; Cao Type III): with `U = G(q¹⁹)H(q⁴) − q³G(q⁴)H(q¹⁹)` and
`V = G(q⁷⁶)H(−q) + q¹⁵G(−q)H(q⁷⁶)`, `U/V = χ(−q²)/χ(−q³⁸)`, i.e. `U χ(−q³⁸) = V χ(−q²)`. -/
theorem entry_3_30 : (S 19 G * S 4 H - PowerSeries.X ^ 3 * S 4 G * S 19 H) * chim 38 =
    (S 76 G * Ng H + PowerSeries.X ^ 15 * Ng G * S 76 H) * chim 2 := by
  simp only [chim, Nat.reduceMul]
  have e1 := SG_E 19
  have e2 := SH_E 19
  have e3 := SG_E 4
  have e4 := SH_E 4
  have e5 := SG_E 76
  have e6 := SH_E 76
  norm_num at e1 e2 e3 e4 e5 e6
  have hU : (S 19 G * S 4 H - PowerSeries.X ^ 3 * S 4 G * S 19 H) * (Pinf 19 19 * Pinf 4 4) =
      J 38 95 * J 4 20 - PowerSeries.X ^ 3 * (J 8 20 * J 19 95) := by
    linear_combination (S 4 H * Pinf 4 4) * e1 + J 38 95 * e4 - PowerSeries.X ^ 3 * (S 19 H * Pinf 19 19) * e3
      - PowerSeries.X ^ 3 * J 8 20 * e2
  have hV : (S 76 G * Ng H + PowerSeries.X ^ 15 * Ng G * S 76 H) * (Pinf 76 76 * Pinf 2 2) =
      J 152 380 * (Ng H * Pinf 2 2) + PowerSeries.X ^ 15 * ((Ng G * Pinf 2 2) * J 76 380) := by
    linear_combination (Ng H * Pinf 2 2) * e5 + PowerSeries.X ^ 15 * (Ng G * Pinf 2 2) * e6
  have kH : (Ng H * Pinf 2 2) * (J 6 20 * J 10 20) = Pinf 10 10 * J 4 10 * J 3 10 := by
    have hD : Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 2 10 (by norm_num) (by norm_num)) (Pinf_ne 8 10 (by norm_num) (by norm_num)))
        (Pinf_ne 14 20 (by norm_num) (by norm_num))) (Pinf_ne 6 20 (by norm_num) (by norm_num))
    apply mul_left_cancel₀ hD
    have k : Pinf 7 10 * Pinf 3 10 * Pinf 2 2 * (J 6 20 * J 10 20) =
        Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20 * (Pinf 10 10 * J 4 10 * J 3 10) := by
      simp only [J, Nat.reduceSub]
      simp (disch := norm_num) only [atom _ _ 20]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
        add_zero, mul_one]
      ring
    linear_combination (Pinf 2 2 * (J 6 20 * J 10 20)) * NgH_prod + k
  have kG : (Ng G * Pinf 2 2) * (J 2 20 * J 10 20) = Pinf 10 10 * J 2 10 * J 1 10 := by
    have hD : Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 2 20 (by norm_num) (by norm_num)) (Pinf_ne 6 10 (by norm_num) (by norm_num)))
        (Pinf_ne 4 10 (by norm_num) (by norm_num))) (Pinf_ne 18 20 (by norm_num) (by norm_num))
    apply mul_left_cancel₀ hD
    have k : Pinf 1 10 * Pinf 9 10 * Pinf 2 2 * (J 2 20 * J 10 20) =
        Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20 * (Pinf 10 10 * J 2 10 * J 1 10) := by
      simp only [J, Nat.reduceSub]
      simp (disch := norm_num) only [atom _ _ 20]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
        add_zero, mul_one]
      ring
    linear_combination (Pinf 2 2 * (J 2 20 * J 10 20)) * NgG_prod + k
  have r1 := congrArg (S 19) R59a
  have r2 := congrArg (S 19) R59b
  simp only [map_mul, S_J' 19 4 10 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 190 = 19 * 10),
    S_J' 19 3 10 (by norm_num) (by norm_num) (rfl : 57 = 19 * 3) (rfl : 190 = 19 * 10),
    S_J' 19 1 5 le_rfl (by norm_num) (rfl : 19 = 19 * 1) (rfl : 95 = 19 * 5),
    S_J' 19 2 10 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 190 = 19 * 10),
    S_J' 19 1 10 le_rfl (by norm_num) (rfl : 19 = 19 * 1) (rfl : 190 = 19 * 10),
    S_J' 19 2 5 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 95 = 19 * 5),
    S_P' 19 1 2 le_rfl (by norm_num) (rfl : 19 = 19 * 1) (rfl : 38 = 19 * 2),
    S_P' 19 10 10 (by norm_num) (by norm_num) (rfl : 190 = 19 * 10) (rfl : 190 = 19 * 10)] at r1 r2
  have jA : J 190 570 = Pinf 190 190 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 570]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have jB : J 10 30 = Pinf 10 10 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 30]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have P := P3_30
  rw [jA, jB] at P
  have W0 : (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 19 190 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (J_ne30 6 20 (by norm_num) (by norm_num)) (J_ne30 10 20 (by norm_num) (by norm_num)))
      (mul_ne_zero (J_ne30 2 20 (by norm_num) (by norm_num)) (J_ne30 10 20 (by norm_num) (by norm_num))))
      (J_ne30 57 190 (by norm_num) (by norm_num))) (J_ne30 19 190 (by norm_num) (by norm_num))
  have key : (S 19 G * S 4 H - PowerSeries.X ^ 3 * S 4 G * S 19 H) * (Pinf 19 19 * Pinf 4 4) =
      Pinf 19 38 * ((S 76 G * Ng H + PowerSeries.X ^ 15 * Ng G * S 76 H) * (Pinf 76 76 * Pinf 2 2)) := by
    apply mul_left_cancel₀ W0
    calc (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 19 190 *
          ((S 19 G * S 4 H - PowerSeries.X ^ 3 * S 4 G * S 19 H) * (Pinf 19 19 * Pinf 4 4))
        = (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 19 190 *
            (J 38 95 * J 4 20 - PowerSeries.X ^ 3 * (J 8 20 * J 19 95)) := by
          linear_combination ((J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 19 190) * hU
      _ = Pinf 19 38 * (Pinf 190 190 * (J 4 20 * J 57 190 * (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 38 190
            - PowerSeries.X ^ 3 * (J 8 20 * J 19 190 * (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 76 190))) := by
          linear_combination (-((J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 4 20)) * r2
            + (PowerSeries.X ^ 3 * (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 19 190 * J 8 20) * r1
      _ = Pinf 19 38 * (Pinf 10 10 * (J 152 380 * J 19 190 * J 57 190 * (J 2 20 * J 10 20) * J 3 10 * J 4 10
            + PowerSeries.X ^ 15 * (J 76 380 * J 19 190 * J 57 190 * (J 6 20 * J 10 20) * J 1 10 * J 2 10))) := by
          rw [P]
      _ = Pinf 19 38 * (J 19 190 * J 57 190 * (J 2 20 * J 10 20) * (J 6 20 * J 10 20) *
            (J 152 380 * (Ng H * Pinf 2 2) + PowerSeries.X ^ 15 * ((Ng G * Pinf 2 2) * J 76 380))) := by
          linear_combination (-(Pinf 19 38 * J 19 190 * J 57 190 * (J 2 20 * J 10 20) * J 152 380)) * kH
            - (Pinf 19 38 * J 19 190 * J 57 190 * (J 6 20 * J 10 20) * PowerSeries.X ^ 15 * J 76 380) * kG
      _ = (J 6 20 * J 10 20) * (J 2 20 * J 10 20) * J 57 190 * J 19 190 *
            (Pinf 19 38 * ((S 76 G * Ng H + PowerSeries.X ^ 15 * Ng G * S 76 H) * (Pinf 76 76 * Pinf 2 2))) := by
          linear_combination (-(Pinf 19 38 * J 19 190 * J 57 190 * (J 2 20 * J 10 20) * (J 6 20 * J 10 20))) * hV
  have a19 : Pinf 19 19 = Pinf 19 38 * Pinf 38 76 * Pinf 76 76 := by
    simp (disch := norm_num) only [atom _ _ 76]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have a2 : Pinf 2 2 = Pinf 2 4 * Pinf 4 4 := by
    simp (disch := norm_num) only [atom _ _ 4]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (Pinf_ne 19 38 (by norm_num) (by norm_num))
    (Pinf_ne 76 76 (by norm_num) (by norm_num))) (Pinf_ne 4 4 (by norm_num) (by norm_num)))
  rw [a19, a2] at key
  linear_combination key

end Forty
