/-
# Watson's Lemma 4.1, second half (Berndt et al. (4.24)): `H(q) f(−q²) = f(−q⁸) {q³ H(q¹⁶) + G(−q⁴)}`

The argument is the same as for (4.23) (`W41`):
* `f(−q²)H(q) = f(−q¹¹,−q¹⁹) + q³f(−q,−q²⁹)` is a quintuple collapse.
* Then `dis2` dissects each theta.
* Two quintuple collapses at `c = −1` and nome `q⁴⁰` recombine the pieces.
* The product forms of `H(q¹⁶)` and `G(−q⁴)` finish the proof.
-/
import RamanujanTau.Forty.W41

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm40 : 1 ≤ 40 := by norm_num
private lemma hm120 : 1 ≤ 120 := by norm_num

private lemma Jne' (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- (4.24) in `ℂ((t))`, after the quintuple collapses. -/
theorem M41b : θ hm30 10 1 * θ hm10 4 1 * (θ hm40 4 (-1) * θ hm40 16 (-1)) =
    θ hm10 3 1 * θ hm120 40 1 * (θ hm40 8 1 * θ hm40 16 (-1) + mono 3 1 * (θ hm40 8 1 * θ hm40 4 (-1))) := by
  have Q := quint1 hm10 hm30 rfl 3 19 29 10 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm30 11 19 (by norm_num), θ_refl1 hm30 1 29 (by norm_num), θ_refl1 hm10 4 6 (by norm_num)] at Q
  have d11 := dis2 hm30 hm120 rfl 11 one_ne_zero 52 (-8) 19 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d1 := dis2 hm30 hm120 rfl 1 one_ne_zero 32 (-28) 29 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have i8 := inv_m' hm120 8
  have i28 := inv_m' hm120 28
  have Qa := quintm hm40 hm120 rfl 4 52 92 40 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qb := quintm hm40 hm120 rfl 16 88 128 40 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm120 28 92 (by norm_num)] at Qa
  rw [θ_reflm hm120 32 88 (by norm_num), θ_refl1 hm40 8 32 (by norm_num),
    θ_sh hm120 8 1 (by norm_num : (-1 : ℂ) ≠ 0) (-8) 1 (e := 128) (by norm_num) (by norm_num [c2]) (by norm_num)] at Qb
  rw [d11, d1, i8, i28, show -(mono (-8) (-1) : L) = mono (-8) 1 by simp [mono],
    show -(mono (-28) (-1) : L) = mono (-28) 1 by simp [mono]] at Q
  have m1 : (mono 19 (-1) : L) * mono (-8) 1 = mono 11 (-1) := by rw [mono_mul]; norm_num
  have m2 : (mono 3 1 : L) * (mono 29 (-1) * mono (-28) 1) = mono 4 (-1) := by rw [mono_mul, mono_mul]; norm_num
  have m3 : (mono 3 1 : L) * (mono 16 1 * mono (-8) 1) = mono 11 1 := by rw [mono_mul, mono_mul]; norm_num
  have n11 : (mono 11 (-1) : L) = -mono 11 1 := by simp [mono]
  have n4 : (mono 4 (-1) : L) = -mono 4 1 := by simp [mono]
  linear_combination (-(θ hm40 4 (-1) * θ hm40 16 (-1))) * Q + (θ hm10 3 1 * θ hm40 16 (-1)) * Qa
    + (mono 3 1 * θ hm10 3 1 * θ hm40 4 (-1)) * Qb
    + ((θ hm40 4 (-1) * θ hm40 16 (-1) * θ hm10 3 1) * θ hm120 8 (-1)) * (m1 + m3 + n11) + ((θ hm40 4 (-1) * θ hm40 16 (-1) * θ hm10 3 1) * θ hm120 28 (-1)) * (m2 + n4)

/-- the product form of `M41b`. -/
theorem P41b : J 10 30 * J 4 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) =
    J 3 10 * J 40 120 * (J 8 40 * (J 32 80 * J 40 80) * J 4 40 + PowerSeries.X ^ 3 * (J 8 40 * (J 8 80 * J 40 80) * J 16 40)) := by
  apply ι_inj
  have h := congrArg (· * (ι (J 4 40) * ι (J 16 40))) M41b
  simp only at h
  have hb4 := θ_bar hm40 4 (by norm_num) (by norm_num)
  have hb16 := θ_bar hm40 16 (by norm_num) (by norm_num)
  norm_num at hb4 hb16
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 3 (e' := 3) (by norm_num) (by norm_num) (by norm_num), θu' hm120 40 (e' := 40) (by norm_num) (by norm_num) (by norm_num),
    θu' hm40 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_add, ι_Xpow] at hb4 hb16 h ⊢
  push_cast at h ⊢
  linear_combination h - (ι (J 10 30) * ι (J 4 10) * (θ hm40 16 (-1) * ι (J 16 40))) * hb4
    - (ι (J 10 30) * ι (J 4 10) * (ι (J 8 80) * ι (J 40 80))) * hb16
    + (ι (J 3 10) * ι (J 40 120) * ι (J 8 40) * ι (J 4 40)) * hb16
    + (ι (J 3 10) * ι (J 40 120) * mono 3 1 * ι (J 8 40) * ι (J 16 40)) * hb4

/-- **Watson's Lemma 4.1, (4.24)**: `H(q) f(−q²) = f(−q⁸) {q³ H(q¹⁶) + G(−q⁴)}`. -/
theorem lemma41b : H * Pinf 2 2 = Pinf 8 8 * (PowerSeries.X ^ 3 * S 16 H + S 4 (Ng G)) := by
  have hHE := H_E
  have a1 := E1_split
  have r := R59a
  have P := P41b
  have jA : J 10 30 = Pinf 10 10 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 30]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have jB : J 40 120 = Pinf 40 40 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 120]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  rw [jA, jB] at P
  have e16 := SH_E 16
  norm_num at e16
  have kD : Pinf 40 40 * J 8 40 * J 16 40 * Pinf 16 16 = Pinf 8 8 * J 16 80 * (J 32 80 * J 40 80) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 80]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have kC : Pinf 40 40 * J 8 40 * J 4 40 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) = Pinf 8 8 * (J 8 80 * J 40 80) * (Pinf 4 40 * Pinf 36 40) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 80]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hN := congrArg (S 4) NgG_prod
  simp only [map_mul, S_P' 4 2 20 (by norm_num) (by norm_num) (rfl : 8 = 4 * 2) (rfl : 80 = 4 * 20),
    S_P' 4 6 10 (by norm_num) (by norm_num) (rfl : 24 = 4 * 6) (rfl : 40 = 4 * 10),
    S_P' 4 4 10 (by norm_num) (by norm_num) (rfl : 16 = 4 * 4) (rfl : 40 = 4 * 10),
    S_P' 4 18 20 (by norm_num) (by norm_num) (rfl : 72 = 4 * 18) (rfl : 80 = 4 * 20),
    S_P' 4 1 10 le_rfl (by norm_num) (rfl : 4 = 4 * 1) (rfl : 40 = 4 * 10),
    S_P' 4 9 10 (by norm_num) (by norm_num) (rfl : 36 = 4 * 9) (rfl : 40 = 4 * 10)] at hN
  have hZ : Pinf 1 2 * J 3 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 1 2 le_rfl (by norm_num)) (Jne' 3 10 (by norm_num) (by norm_num)))
      (mul_ne_zero (mul_ne_zero (Jne' 8 80 (by norm_num) (by norm_num)) (Jne' 40 80 (by norm_num) (by norm_num)))
        (mul_ne_zero (Jne' 32 80 (by norm_num) (by norm_num)) (Jne' 40 80 (by norm_num) (by norm_num)))))
      (Pinf_ne 16 16 (by norm_num) (by norm_num))) ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 8 80 (by norm_num) (by norm_num)) (Pinf_ne 24 40 (by norm_num) (by norm_num)))
      (Pinf_ne 16 40 (by norm_num) (by norm_num))) (Pinf_ne 72 80 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hZ
  calc Pinf 1 2 * J 3 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (H * Pinf 2 2)
      = Pinf 1 2 * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (J 4 10 * Pinf 10 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80))) := by
        linear_combination (J 3 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80)) * hHE
          - (J 3 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * H) * a1 - (((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80)) * r
    _ = Pinf 1 2 * J 3 10 * (Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (Pinf 40 40 * J 8 40 * J 4 40) * (J 32 80 * J 40 80)
          + PowerSeries.X ^ 3 * (Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (Pinf 40 40 * J 8 40 * J 16 40) * (J 8 80 * J 40 80))) := by
        linear_combination (Pinf 1 2 * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80)) * P
    _ = Pinf 1 2 * J 3 10 * ((J 8 80 * J 40 80) * (J 32 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (Pinf 8 8 * (PowerSeries.X ^ 3 * S 16 H + S 4 (Ng G))) := by
        linear_combination (Pinf 1 2 * J 3 10 * Pinf 16 16 * (J 32 80 * J 40 80)) * kC
          + (Pinf 1 2 * J 3 10 * PowerSeries.X ^ 3 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (J 8 80 * J 40 80)) * kD
          - (Pinf 1 2 * J 3 10 * PowerSeries.X ^ 3 * (Pinf 8 80 * Pinf 24 40 * Pinf 16 40 * Pinf 72 80) * (J 8 80 * J 40 80) * Pinf 8 8 * (J 32 80 * J 40 80)) * e16
          - (Pinf 1 2 * J 3 10 * Pinf 16 16 * (J 32 80 * J 40 80) * Pinf 8 8 * (J 8 80 * J 40 80)) * hN

end Forty
