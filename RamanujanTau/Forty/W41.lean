/-
# Watson's Lemma 4.1 (Berndt et al. (4.23)): `G(q) f(−q²) = f(−q⁸) {G(q¹⁶) + q H(−q⁴)}`

* `f(−q²)G(q) = f(−q¹³,−q¹⁷) + q f(−q⁷,−q²³)` is a quintuple collapse.
* Each theta is 2-dissected (`dis2`).
* The four pieces recombine by two quintuple collapses at `c = −1` and nome `q⁴⁰`.
* Product identities for `G(q¹⁶)` and `H(−q⁴)` (`NgOdd`) finish the proof.
-/
import RamanujanTau.Forty.E13
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.NgOdd

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm40 : 1 ≤ 40 := by norm_num
private lemma hm120 : 1 ≤ 120 := by norm_num

private lemma Jne (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- (4.23) in `ℂ((t))`, after the quintuple collapses. -/
theorem M41a : θ hm30 10 1 * θ hm10 2 1 * (θ hm40 8 (-1) * θ hm40 12 (-1)) =
    θ hm10 1 1 * θ hm120 40 1 * (θ hm40 16 1 * θ hm40 12 (-1) + mono 1 1 * (θ hm40 24 1 * θ hm40 8 (-1))) := by
  have Q := quint1 hm10 hm30 rfl 1 13 23 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm30 7 23 (by norm_num)] at Q
  have d13 := dis2 hm30 hm120 rfl 13 one_ne_zero 56 (-4) 17 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d7 := dis2 hm30 hm120 rfl 7 one_ne_zero 44 (-16) 23 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have i4 := inv_m' hm120 4
  have i16 := inv_m' hm120 16
  have Qa := quintm hm40 hm120 rfl 8 64 104 40 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qb := quintm hm40 hm120 rfl 12 76 116 40 24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm120 56 64 (by norm_num), θ_reflm hm120 16 104 (by norm_num)] at Qa
  rw [θ_reflm hm120 44 76 (by norm_num), θ_reflm hm120 4 116 (by norm_num)] at Qb
  rw [d13, d7, i4, i16, show -(mono (-4) (-1) : L) = mono (-4) 1 by simp [mono],
    show -(mono (-16) (-1) : L) = mono (-16) 1 by simp [mono]] at Q
  have m1 : (mono 17 (-1) : L) * mono (-4) 1 = mono 13 (-1) := by rw [mono_mul]; norm_num
  have m2 : (mono 1 1 : L) * (mono 23 (-1) * mono (-16) 1) = mono 8 (-1) := by rw [mono_mul, mono_mul]; norm_num
  have m3 : (mono 1 1 : L) * mono 12 1 = mono 13 1 := by rw [mono_mul]; norm_num
  have n13 : (mono 13 (-1) : L) = -mono 13 1 := by simp [mono]
  have n8 : (mono 8 (-1) : L) = -mono 8 1 := by simp [mono]
  linear_combination (-(θ hm40 8 (-1) * θ hm40 12 (-1))) * Q + (θ hm10 1 1 * θ hm40 12 (-1)) * Qa
    + (mono 1 1 * θ hm10 1 1 * θ hm40 8 (-1)) * Qb + ((θ hm40 8 (-1) * θ hm40 12 (-1) * θ hm10 1 1) * θ hm120 4 (-1)) * (m1 + m3 + n13)
    + ((θ hm40 8 (-1) * θ hm40 12 (-1) * θ hm10 1 1) * θ hm120 16 (-1)) * (m2 + n8)


/-- the product form of `M41a`. -/
theorem P41a : J 10 30 * J 2 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) =
    J 1 10 * J 40 120 * (J 16 40 * (J 24 80 * J 40 80) * J 8 40 + PowerSeries.X * (J 24 40 * (J 16 80 * J 40 80) * J 12 40)) := by
  apply ι_inj
  have h := congrArg (· * (ι (J 8 40) * ι (J 12 40))) M41a
  simp only at h
  have hb8 := θ_bar hm40 8 (by norm_num) (by norm_num)
  have hb12 := θ_bar hm40 12 (by norm_num) (by norm_num)
  norm_num at hb8 hb12
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num), θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 1 (e' := 1) (by norm_num) le_rfl (by norm_num), θu' hm120 40 (e' := 40) (by norm_num) (by norm_num) (by norm_num),
    θu' hm40 16 (e' := 16) (by norm_num) (by norm_num) (by norm_num), θu' hm40 24 (e' := 24) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_add, ι_X] at hb8 hb12 h ⊢
  linear_combination h - (ι (J 10 30) * ι (J 2 10) * (θ hm40 12 (-1) * ι (J 12 40))) * hb8
    - (ι (J 10 30) * ι (J 2 10) * (ι (J 16 80) * ι (J 40 80))) * hb12
    + (ι (J 1 10) * ι (J 40 120) * ι (J 16 40) * ι (J 8 40)) * hb12
    + (ι (J 1 10) * ι (J 40 120) * mono 1 1 * ι (J 24 40) * ι (J 12 40)) * hb8

/-- **Watson's Lemma 4.1, (4.23)**: `G(q) f(−q²) = f(−q⁸) {G(q¹⁶) + q H(−q⁴)}`. -/
theorem lemma41a : G * Pinf 2 2 = Pinf 8 8 * (S 16 G + PowerSeries.X * S 4 (Ng H)) := by
  have hGE := G_E
  have a1 := E1_split
  have r := R59b
  have P := P41a
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
  have e16 := SG_E 16
  norm_num at e16
  have kA : Pinf 40 40 * J 16 40 * J 8 40 * Pinf 16 16 = Pinf 8 8 * J 32 80 * (J 16 80 * J 40 80) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 80]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have kB : Pinf 40 40 * J 24 40 * J 12 40 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) = Pinf 8 8 * (J 24 80 * J 40 80) * (Pinf 28 40 * Pinf 12 40) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 80]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hN := congrArg (S 4) NgH_prod
  simp only [map_mul, S_P' 4 2 10 (by norm_num) (by norm_num) (rfl : 8 = 4 * 2) (rfl : 40 = 4 * 10),
    S_P' 4 8 10 (by norm_num) (by norm_num) (rfl : 32 = 4 * 8) (rfl : 40 = 4 * 10),
    S_P' 4 14 20 (by norm_num) (by norm_num) (rfl : 56 = 4 * 14) (rfl : 80 = 4 * 20),
    S_P' 4 6 20 (by norm_num) (by norm_num) (rfl : 24 = 4 * 6) (rfl : 80 = 4 * 20),
    S_P' 4 7 10 (by norm_num) (by norm_num) (rfl : 28 = 4 * 7) (rfl : 40 = 4 * 10),
    S_P' 4 3 10 (by norm_num) (by norm_num) (rfl : 12 = 4 * 3) (rfl : 40 = 4 * 10)] at hN
  have hZ : Pinf 1 2 * J 1 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 1 2 le_rfl (by norm_num)) (Jne 1 10 le_rfl (by norm_num)))
      (mul_ne_zero (mul_ne_zero (Jne 16 80 (by norm_num) (by norm_num)) (Jne 40 80 (by norm_num) (by norm_num)))
        (mul_ne_zero (Jne 24 80 (by norm_num) (by norm_num)) (Jne 40 80 (by norm_num) (by norm_num)))))
      (Pinf_ne 16 16 (by norm_num) (by norm_num))) ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 8 40 (by norm_num) (by norm_num)) (Pinf_ne 32 40 (by norm_num) (by norm_num)))
      (Pinf_ne 56 80 (by norm_num) (by norm_num))) (Pinf_ne 24 80 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hZ
  calc Pinf 1 2 * J 1 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (G * Pinf 2 2)
      = Pinf 1 2 * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (J 2 10 * Pinf 10 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80))) := by
        linear_combination (J 1 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80)) * hGE
          - (J 1 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * G) * a1 - (((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80)) * r
    _ = Pinf 1 2 * J 1 10 * (Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (Pinf 40 40 * J 16 40 * J 8 40) * (J 24 80 * J 40 80)
          + PowerSeries.X * (Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (Pinf 40 40 * J 24 40 * J 12 40) * (J 16 80 * J 40 80))) := by
        linear_combination (Pinf 1 2 * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80)) * P
    _ = Pinf 1 2 * J 1 10 * ((J 16 80 * J 40 80) * (J 24 80 * J 40 80)) * Pinf 16 16 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (Pinf 8 8 * (S 16 G + PowerSeries.X * S 4 (Ng H))) := by
        linear_combination (Pinf 1 2 * J 1 10 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (J 24 80 * J 40 80)) * kA
          + (Pinf 1 2 * J 1 10 * PowerSeries.X * Pinf 16 16 * (J 16 80 * J 40 80)) * kB
          - (Pinf 1 2 * J 1 10 * (Pinf 8 40 * Pinf 32 40 * Pinf 56 80 * Pinf 24 80) * (J 24 80 * J 40 80) * Pinf 8 8 * (J 16 80 * J 40 80)) * e16
          - (Pinf 1 2 * J 1 10 * PowerSeries.X * Pinf 16 16 * (J 16 80 * J 40 80) * Pinf 8 8 * (J 24 80 * J 40 80)) * hN

end Forty
