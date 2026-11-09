/-
# Entry 3.13: `G(q⁹)H(q⁴) − qG(q⁴)H(q⁹) = χ(−q)χ(−q⁶)/(χ(−q³)χ(−q¹⁸))`

Cao (arXiv:2503.11445, proof of Identity 13): `S = Σ (−1)^{x₁} q^{7x₁²+6x₁x₂+9x₂²+6x₁}` expanded by two exact covers
(`L3_13`), the quintuple product (`ALz.quint_theta`, at `c = 1` and `c = −1`) and Cao (59) at `q⁹`.
-/
import RamanujanTau.Forty.E16

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm90 : 1 ≤ 90 := by norm_num
private lemma hm18 : 1 ≤ 18 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm108 : 1 ≤ 108 := by norm_num
private lemma hm270 : 1 ≤ 270 := by norm_num

/-- Entry 3.13, side a: `B = (1 3; -1 2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_13a : ECS where
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

/-- Entry 3.13, side b: `B = (0 -3; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-1), 0, 1}`. -/
def B3_13b : ECS where
  b11 := 0
  b12 := (-3)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-1)) % 3 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-1)) % 3 + (-1))) - (-3) * (n - 0 * ((1 * m + 0 * n - (-1)) % 3 + (-1)))) / 3), ((0 * (n - 0 * ((1 * m + 0 * n - (-1)) % 3 + (-1))) - 1 * (m - 1 * ((1 * m + 0 * n - (-1)) % 3 + (-1)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_13 : (θ hm20 4 1 * θ hm270 117 1) - (mono 1 1 * (θ hm20 8 1 * θ hm270 99 1)) + (mono 9 1 * (θ hm20 4 1 * θ hm270 63 1)) - (mono 28 1 * (θ hm20 8 1 * θ hm270 9 1)) = (θ hm18 9 (-1) * θ hm108 36 1) - (mono 1 1 * (θ hm18 3 (-1) * θ hm108 36 1)) := by
  have h := qf_two 7 3 9 6 0 1 0 B3_13a B3_13b
    hm20 hm270 hm18 hm108 (by norm_num [B3_13a]) (by norm_num [B3_13a]) (by norm_num [B3_13a])
    (by norm_num [B3_13b]) (by norm_num [B3_13b]) (by norm_num [B3_13b])
  simp only [B3_13a, B3_13b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm108 36 0 0 1 (e := 72) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 1 (-12) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm270 117 0 0 1 (e := 153) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm270 63 0 0 1 (e := 207) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm270 9 0 0 1 (e := 261) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm18 3 0 0 1 (e := 15) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 4 1 one_ne_zero (-4) (-1) (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm108 0 (e := 0) (by norm_num), θz' hm20 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


lemma J_ne (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- the quintuple product at `c = −1`. -/
lemma quintm {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : M = 3 * N) (e a b n f : ℤ) (ha : a = N + 3 * e)
    (hb : b = 2 * N + 3 * e) (hn : n = N) (hf : f = 2 * e) :
    (θ hM a (-1) - mono e 1 * θ hM b (-1)) * θ hN e (-1) = θ hM n 1 * θ hN f 1 := by
  subst hMN ha hb hn hf
  have h := quint_theta hN hM e (by norm_num : (-1 : ℂ) ≠ 0)
  have h3 : ((-1 : ℂ)) ^ 3 = -1 := by norm_num
  have h2 : ((-1 : ℂ)) ^ 2 = 1 := by norm_num
  rw [h3, h2, mono_neg1] at h
  linear_combination h

/-- `L3_13` with the three quintuple collapses applied. -/
theorem M3_13 : θ hm270 90 1 * (θ hm20 4 1 * θ hm90 27 1 * θ hm6 1 (-1) * θ hm90 18 1
      - mono 1 1 * (θ hm20 8 1 * θ hm90 9 1 * θ hm6 1 (-1) * θ hm90 36 1)) =
    θ hm108 36 1 * θ hm90 9 1 * θ hm90 27 1 * (θ hm18 6 1 * θ hm6 2 1) := by
  have hLat := L3_13
  have Q1 := quint1 hm90 hm270 rfl 9 117 207 90 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm90 hm270 rfl 27 171 261 90 54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q3 := quintm hm6 hm18 rfl 1 9 15 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm270 63 207 (by norm_num)] at Q1
  rw [θ_refl1 hm270 99 171 (by norm_num), θ_refl1 hm270 9 261 (by norm_num), θ_refl1 hm90 36 54 (by norm_num)] at Q2
  rw [θ_reflm hm18 3 15 (by norm_num)] at Q3
  have m1 : (mono 1 1 : L) * mono 27 1 = mono 28 1 := by rw [mono_mul]; norm_num
  linear_combination (θ hm90 9 1 * θ hm90 27 1 * θ hm6 1 (-1)) * hLat
    - (θ hm20 4 1 * θ hm90 27 1 * θ hm6 1 (-1)) * Q1
    + (mono 1 1 * θ hm20 8 1 * θ hm90 9 1 * θ hm6 1 (-1)) * Q2
    + (θ hm108 36 1 * θ hm90 9 1 * θ hm90 27 1) * Q3
    - (θ hm20 8 1 * θ hm270 9 1 * θ hm90 9 1 * θ hm90 27 1 * θ hm6 1 (-1)) * m1

/-- the product form of `M3_13`. -/
theorem P3_13 : J 90 270 * (J 4 20 * J 27 90 * (J 2 12 * J 6 12) * J 18 90
      - PowerSeries.X * (J 8 20 * J 9 90 * (J 2 12 * J 6 12) * J 36 90)) =
    J 36 108 * J 9 90 * J 27 90 * (J 6 18 * J 2 6) * J 1 6 := by
  apply ι_inj
  have h := congrArg (· * ι (J 1 6)) M3_13
  simp only at h
  have hb := θ_bar hm6 1 le_rfl (by norm_num)
  norm_num at hb
  rw [θu' hm270 90 (e' := 90) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm90 9 (e' := 9) (by norm_num) (by norm_num) (by norm_num),
    θu' hm90 18 (e' := 18) (by norm_num) (by norm_num) (by norm_num),
    θu' hm90 27 (e' := 27) (by norm_num) (by norm_num) (by norm_num),
    θu' hm90 36 (e' := 36) (by norm_num) (by norm_num) (by norm_num),
    θu' hm108 36 (e' := 36) (by norm_num) (by norm_num) (by norm_num),
    θu' hm18 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm6 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, ι_X] at hb h ⊢
  linear_combination h - (ι (J 90 270) * (ι (J 4 20) * ι (J 27 90) * ι (J 18 90)
    - mono 1 1 * (ι (J 8 20) * ι (J 9 90) * ι (J 36 90)))) * hb

/-- **Entry 3.13** (Bressoud; Cao Type III): `G(q⁹)H(q⁴) − qG(q⁴)H(q⁹) = χ(−q)χ(−q⁶)/(χ(−q³)χ(−q¹⁸))`. -/
theorem entry_3_13 : S 9 G * S 4 H - PowerSeries.X * S 4 G * S 9 H =
    chim 1 * chim 6 * Ring.inverse (chim 3 * chim 18) := by
  apply eq_mul_inv_of ((isUnit_Pinf 3 6 (by norm_num) (by norm_num)).mul (isUnit_Pinf 18 36 (by norm_num) (by norm_num)))
  simp only [chim, Nat.reduceMul]
  have e1 := SG_E 9
  have e2 := SH_E 9
  have e3 := SG_E 4
  have e4 := SH_E 4
  norm_num at e1 e2 e3 e4
  have hL : (S 9 G * S 4 H - PowerSeries.X * S 4 G * S 9 H) * (Pinf 9 9 * Pinf 4 4) =
      J 18 45 * J 4 20 - PowerSeries.X * (J 8 20 * J 9 45) := by
    linear_combination (S 4 H * Pinf 4 4) * e1 + J 18 45 * e4 - PowerSeries.X * (S 9 H * Pinf 9 9) * e3
      - PowerSeries.X * J 8 20 * e2
  have r1 := congrArg (S 9) R59a
  have r2 := congrArg (S 9) R59b
  simp only [map_mul, S_J' 9 4 10 (by norm_num) (by norm_num) (rfl : 36 = 9 * 4) (rfl : 90 = 9 * 10),
    S_J' 9 3 10 (by norm_num) (by norm_num) (rfl : 27 = 9 * 3) (rfl : 90 = 9 * 10),
    S_J' 9 1 5 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 45 = 9 * 5),
    S_J' 9 2 10 (by norm_num) (by norm_num) (rfl : 18 = 9 * 2) (rfl : 90 = 9 * 10),
    S_J' 9 1 10 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 90 = 9 * 10),
    S_J' 9 2 5 (by norm_num) (by norm_num) (rfl : 18 = 9 * 2) (rfl : 45 = 9 * 5),
    S_P' 9 1 2 le_rfl (by norm_num) (rfl : 9 = 9 * 1) (rfl : 18 = 9 * 2),
    S_P' 9 10 10 (by norm_num) (by norm_num) (rfl : 90 = 9 * 10) (rfl : 90 = 9 * 10)] at r1 r2
  have jA : J 90 270 = Pinf 90 90 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 270]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have K : Pinf 9 18 * J 36 108 * J 6 18 * J 2 6 * J 1 6 * (Pinf 3 6 * Pinf 18 36) =
      Pinf 1 2 * Pinf 6 12 * (Pinf 9 9 * Pinf 4 4) * (J 2 12 * J 6 12) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 108]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have P := P3_13
  rw [jA] at P
  -- `P9,18 · P` turns the left side into `J₂,₁₂J₆,₁₂J₂₇,₉₀J₉,₉₀ · (LG E₉E₄)`
  have hW : (J 2 12 * J 6 12) * J 27 90 * J 9 90 * (Pinf 9 9 * Pinf 4 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (J_ne 2 12 (by norm_num) (by norm_num))
      (J_ne 6 12 (by norm_num) (by norm_num))) (J_ne 27 90 (by norm_num) (by norm_num)))
      (J_ne 9 90 (by norm_num) (by norm_num)))
      (mul_ne_zero (Pinf_ne 9 9 (by norm_num) (by norm_num)) (Pinf_ne 4 4 (by norm_num) (by norm_num)))
  apply mul_left_cancel₀ hW
  calc (J 2 12 * J 6 12) * J 27 90 * J 9 90 * (Pinf 9 9 * Pinf 4 4) *
        ((S 9 G * S 4 H - PowerSeries.X * S 4 G * S 9 H) * (Pinf 3 6 * Pinf 18 36))
      = (J 2 12 * J 6 12) * J 27 90 * J 9 90 * (J 18 45 * J 4 20 - PowerSeries.X * (J 8 20 * J 9 45))
          * (Pinf 3 6 * Pinf 18 36) := by
        linear_combination ((J 2 12 * J 6 12) * J 27 90 * J 9 90 * (Pinf 3 6 * Pinf 18 36)) * hL
    _ = Pinf 9 18 * (Pinf 90 90 * (J 4 20 * J 27 90 * (J 2 12 * J 6 12) * J 18 90
          - PowerSeries.X * (J 8 20 * J 9 90 * (J 2 12 * J 6 12) * J 36 90))) * (Pinf 3 6 * Pinf 18 36) := by
        linear_combination (-(J 2 12 * J 6 12) * J 27 90 * J 4 20 * (Pinf 3 6 * Pinf 18 36)) * r2
          + (PowerSeries.X * (J 2 12 * J 6 12) * J 9 90 * J 8 20 * (Pinf 3 6 * Pinf 18 36)) * r1
    _ = Pinf 9 18 * (J 36 108 * J 9 90 * J 27 90 * (J 6 18 * J 2 6) * J 1 6) * (Pinf 3 6 * Pinf 18 36) := by
        rw [P]
    _ = (J 2 12 * J 6 12) * J 27 90 * J 9 90 * (Pinf 9 9 * Pinf 4 4) * (Pinf 1 2 * Pinf 6 12) := by
        linear_combination (J 9 90 * J 27 90) * K

end Forty
