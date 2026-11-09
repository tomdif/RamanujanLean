/-
# Entry 3.16 (first equality): `G(q²)G(q¹³) + q³H(q²)H(q¹³) = G(q²⁶)H(q) − q⁵G(q)H(q²⁶)`

Cao's Type III proof (arXiv:2503.11445, §3.4), via Yesilyurt/Bressoud. The form
`S = Σ (−1)^{x₁} q^{5x₁²+2x₁x₂+8x₂²+x₁−5x₂}` is expanded by two exact covers (`L3_16`). Each pair of terms is then
collapsed by the **quintuple product identity** in theta form (`ALz.quint_theta`, already in the repo, so no new
bridge is needed). The relations `f(−q⁴,−q⁶)/f(−q³,−q⁷) = f(−q,−q⁴)/(χ(−q)f(−q¹⁰))` (Cao (59)) finish the proof.
-/
import RamanujanTau.Forty.NgTools
import RamanujanTau.ALQuint

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

/-- the quintuple product identity at `c = 1`, numerals normalised:
`(θ_{3N}(N+3e) + tᵉ θ_{3N}(2N+3e)) θ_N(e) = θ_{3N}(N) θ_N(2e)`. -/
lemma quint1 {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : M = 3 * N) (e a b n f : ℤ) (ha : a = N + 3 * e)
    (hb : b = 2 * N + 3 * e) (hn : n = N) (hf : f = 2 * e) :
    (θ hM a 1 + mono e 1 * θ hM b 1) * θ hN e 1 = θ hM n 1 * θ hN f 1 := by
  subst hMN ha hb hn hf
  have h := quint_theta hN hM e one_ne_zero
  simpa only [one_pow] using h


private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm130 : 1 ≤ 130 := by norm_num
private lemma hm390 : 1 ≤ 390 := by norm_num

/-- Entry 3.16, side a: `B = (1 -1; 0 5)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_16a : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 5
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((5 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.16, side b: `B = (1 -3; 1 2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_16b : ECS where
  b11 := 1
  b12 := (-3)
  b21 := 1
  b22 := 2
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 4 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - (-3) * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - 1 * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_16 : (θ hm10 4 1 * θ hm390 169 1) + (mono 3 1 * (θ hm10 2 1 * θ hm390 143 1)) + (mono 13 1 * (θ hm10 4 1 * θ hm390 91 1)) + (mono 42 1 * (θ hm10 2 1 * θ hm390 13 1)) = (θ hm30 11 1 * θ hm130 52 1) + (mono 3 1 * (θ hm30 1 1 * θ hm130 52 1)) - (mono 5 1 * (θ hm30 13 1 * θ hm130 26 1)) - (mono 6 1 * (θ hm30 7 1 * θ hm130 26 1)) := by
  have h := qf_two 5 1 8 1 (-5) 1 0 B3_16a B3_16b
    hm10 hm390 hm30 hm130 (by norm_num [B3_16a]) (by norm_num [B3_16a]) (by norm_num [B3_16a])
    (by norm_num [B3_16b]) (by norm_num [B3_16b]) (by norm_num [B3_16b])
  simp only [B3_16a, B3_16b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm130 26 0 0 1 (e := 104) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm130 52 0 0 1 (e := 78) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 1 (-1) (-1) (-1) (e := (-1)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 13 (-1) (-13) (-1) (e := (-13)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 7 0 0 1 (e := 23) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 143 0 0 1 (e := 247) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 65 0 0 1 (e := 325) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 5 1 one_ne_zero (-5) (-1) (e := 35) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm130 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- `L3_16` with the four quintuple collapses applied. -/
theorem M3_16 : θ hm390 130 1 * (θ hm10 4 1 * θ hm130 39 1 * θ hm10 3 1 * θ hm10 1 1 * θ hm130 26 1
      + mono 3 1 * (θ hm10 2 1 * θ hm130 13 1 * θ hm10 3 1 * θ hm10 1 1 * θ hm130 52 1)) =
    θ hm30 10 1 * (θ hm130 52 1 * θ hm130 13 1 * θ hm130 39 1 * θ hm10 1 1 * θ hm10 4 1
      - mono 5 1 * (θ hm130 26 1 * θ hm130 13 1 * θ hm130 39 1 * θ hm10 3 1 * θ hm10 2 1)) := by
  have hLat := L3_16
  have Q1 := quint1 hm130 hm390 rfl 13 169 299 130 26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm130 hm390 rfl 39 247 377 130 78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q3 := quint1 hm10 hm30 rfl 3 19 29 10 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q4 := quint1 hm10 hm30 rfl 1 13 23 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm390 91 299 (by norm_num)] at Q1
  rw [θ_refl1 hm390 143 247 (by norm_num), θ_refl1 hm390 13 377 (by norm_num), θ_refl1 hm130 52 78 (by norm_num)] at Q2
  rw [θ_refl1 hm30 11 19 (by norm_num), θ_refl1 hm30 1 29 (by norm_num), θ_refl1 hm10 4 6 (by norm_num)] at Q3
  rw [θ_refl1 hm30 7 23 (by norm_num)] at Q4
  have m1 : (mono 3 1 : L) * mono 39 1 = mono 42 1 := by rw [mono_mul]; norm_num
  have m2 : (mono 5 1 : L) * mono 1 1 = mono 6 1 := by rw [mono_mul]; norm_num
  linear_combination (θ hm130 13 1 * θ hm130 39 1 * θ hm10 3 1 * θ hm10 1 1) * hLat
    - (θ hm10 4 1 * θ hm130 39 1 * θ hm10 3 1 * θ hm10 1 1) * Q1
    - (mono 3 1 * θ hm10 2 1 * θ hm130 13 1 * θ hm10 3 1 * θ hm10 1 1) * Q2
    + (θ hm130 52 1 * θ hm130 13 1 * θ hm130 39 1 * θ hm10 1 1) * Q3
    - (mono 5 1 * θ hm130 26 1 * θ hm130 13 1 * θ hm130 39 1 * θ hm10 3 1) * Q4
    + (θ hm10 2 1 * θ hm390 13 1 * θ hm130 39 1 * θ hm130 13 1 * θ hm10 3 1 * θ hm10 1 1) * m1
    + (θ hm30 7 1 * θ hm130 26 1 * θ hm130 13 1 * θ hm130 39 1 * θ hm10 3 1 * θ hm10 1 1) * m2


/-- the product form of `M3_16`. -/
theorem P3_16 : J 130 390 * (J 4 10 * J 39 130 * J 3 10 * J 1 10 * J 26 130
      + PowerSeries.X ^ 3 * (J 2 10 * J 13 130 * J 3 10 * J 1 10 * J 52 130)) =
    J 10 30 * (J 52 130 * J 13 130 * J 39 130 * J 1 10 * J 4 10
      - PowerSeries.X ^ 5 * (J 26 130 * J 13 130 * J 39 130 * J 3 10 * J 2 10)) := by
  apply ι_inj
  have h := M3_16
  rw [θu' hm390 130 (e' := 130) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 3 (e' := 3) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 1 (e' := 1) (by norm_num) (by norm_num) (by norm_num),
    θu' hm130 13 (e' := 13) (by norm_num) (by norm_num) (by norm_num),
    θu' hm130 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num),
    θu' hm130 39 (e' := 39) (by norm_num) (by norm_num) (by norm_num),
    θu' hm130 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_add, map_sub, ι_Xpow]
  push_cast
  linear_combination h

/-- Cao (59): `f(−q⁴,−q⁶) χ(−q) f(−q¹⁰) = f(−q³,−q⁷) f(−q,−q⁴)`. -/
lemma R59a : J 4 10 * Pinf 1 2 * Pinf 10 10 = J 3 10 * J 1 5 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 10]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring

/-- Cao (59): `f(−q²,−q⁸) χ(−q) f(−q¹⁰) = f(−q,−q⁹) f(−q²,−q³)`. -/
lemma R59b : J 2 10 * Pinf 1 2 * Pinf 10 10 = J 1 10 * J 2 5 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 10]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring

lemma S_J' (a : ℕ) [NeZero a] (e N : ℕ) (he : 1 ≤ e) (heN : e < N) {e' N' : ℕ} (h1 : e' = a * e) (h2 : N' = a * N) :
    S a (J e N) = J e' N' := by rw [S_J a e N he heN, h1, h2]

lemma S_P' (a : ℕ) [NeZero a] (b M : ℕ) (hb : 1 ≤ b) (hM : 1 ≤ M) {b' M' : ℕ} (h1 : b' = a * b) (h2 : M' = a * M) :
    S a (Pinf b M) = Pinf b' M' := by rw [S_Pinf a b M hb hM, h1, h2]

/-- **Entry 3.16 (first equality)** (Bressoud; Cao Type III): `G(q²)G(q¹³) + q³H(q²)H(q¹³) = G(q²⁶)H(q) − q⁵G(q)H(q²⁶)`. -/
theorem entry_3_16_i : (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) = (S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) := by
  have e1 := SG_E 2
  have e2 := SH_E 2
  have e3 := SG_E 13
  have e4 := SH_E 13
  have e5 := SG_E 26
  have e6 := SH_E 26
  norm_num at e1 e2 e3 e4 e5 e6
  have e7 := G_E
  have e8 := H_E
  have hL : (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) * (Pinf 2 2 * Pinf 13 13) = (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65)) := by
    linear_combination (S 13 G * Pinf 13 13) * e1 + J 4 10 * e3 + PowerSeries.X ^ 3 * (S 13 H * Pinf 13 13) * e2
      + PowerSeries.X ^ 3 * J 2 10 * e4
  have hR : (S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) * (Pinf 26 26 * Pinf 1 1) = (J 52 130 * J 1 5 - PowerSeries.X ^ 5 * (J 2 5 * J 26 130)) := by
    linear_combination (H * Pinf 1 1) * e5 + J 52 130 * e8 - PowerSeries.X ^ 5 * (S 26 H * Pinf 26 26) * e7
      - PowerSeries.X ^ 5 * J 2 5 * e6
  have r1 := R59a
  have r2 := R59b
  have r3 := congrArg (S 13) R59a
  have r4 := congrArg (S 13) R59b
  simp only [map_mul, S_J' 13 4 10 (by norm_num) (by norm_num) (rfl : 52 = 13 * 4) (rfl : 130 = 13 * 10),
    S_J' 13 3 10 (by norm_num) (by norm_num) (rfl : 39 = 13 * 3) (rfl : 130 = 13 * 10), S_J' 13 1 5 le_rfl (by norm_num) (rfl : 13 = 13 * 1) (rfl : 65 = 13 * 5),
    S_J' 13 2 10 (by norm_num) (by norm_num) (rfl : 26 = 13 * 2) (rfl : 130 = 13 * 10), S_J' 13 1 10 le_rfl (by norm_num) (rfl : 13 = 13 * 1) (rfl : 130 = 13 * 10),
    S_J' 13 2 5 (by norm_num) (by norm_num) (rfl : 26 = 13 * 2) (rfl : 65 = 13 * 5),
    S_P' 13 1 2 le_rfl (by norm_num) (rfl : 13 = 13 * 1) (rfl : 26 = 13 * 2), S_P' 13 10 10 (by norm_num) (by norm_num) (rfl : 130 = 13 * 10) (rfl : 130 = 13 * 10)]
    at r3 r4
  have kL : (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65)) * (J 39 130 * J 13 130) = Pinf 13 26 * Pinf 130 130 * (J 4 10 * J 39 130 * J 26 130 + PowerSeries.X ^ 3 * (J 2 10 * J 13 130 * J 52 130)) := by
    linear_combination (-(J 4 10 * J 39 130)) * r4 - PowerSeries.X ^ 3 * (J 2 10 * J 13 130) * r3
  have kR : (J 52 130 * J 1 5 - PowerSeries.X ^ 5 * (J 2 5 * J 26 130)) * (J 3 10 * J 1 10) = Pinf 1 2 * Pinf 10 10 * (J 52 130 * J 1 10 * J 4 10 - PowerSeries.X ^ 5 * (J 26 130 * J 3 10 * J 2 10)) := by
    linear_combination (-(J 52 130 * J 1 10)) * r1 + PowerSeries.X ^ 5 * J 26 130 * J 3 10 * r2
  have jA : J 130 390 = Pinf 130 130 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 390]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have jB : J 10 30 = Pinf 10 10 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 30]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have P := P3_16
  rw [jA, jB] at P
  have key : (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) * (Pinf 2 2 * Pinf 13 13) * Pinf 1 2 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10) =
      (S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) * (Pinf 26 26 * Pinf 1 1) * Pinf 13 26 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10) := by
    calc (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) * (Pinf 2 2 * Pinf 13 13) * Pinf 1 2 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10)
        = (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65)) * (J 39 130 * J 13 130) * (J 3 10 * J 1 10 * Pinf 10 10 * Pinf 1 2) := by
          linear_combination (Pinf 1 2 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10)) * hL
      _ = Pinf 13 26 * Pinf 130 130 * (J 4 10 * J 39 130 * J 26 130 + PowerSeries.X ^ 3 * (J 2 10 * J 13 130 * J 52 130)) * (J 3 10 * J 1 10 * Pinf 10 10 * Pinf 1 2) := by
          linear_combination (J 3 10 * J 1 10 * Pinf 10 10 * Pinf 1 2) * kL
      _ = Pinf 13 26 * Pinf 10 10 * Pinf 1 2 * (Pinf 10 10 * (J 13 130 * J 39 130) * (J 52 130 * J 1 10 * J 4 10 - PowerSeries.X ^ 5 * (J 26 130 * J 3 10 * J 2 10))) := by
          linear_combination (Pinf 13 26 * Pinf 10 10 * Pinf 1 2) * P
      _ = Pinf 13 26 * Pinf 10 10 * (J 13 130 * J 39 130) * ((J 52 130 * J 1 5 - PowerSeries.X ^ 5 * (J 2 5 * J 26 130)) * (J 3 10 * J 1 10)) := by
          linear_combination (-(Pinf 13 26 * Pinf 10 10 * (J 13 130 * J 39 130))) * kR
      _ = (S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) * (Pinf 26 26 * Pinf 1 1) * Pinf 13 26 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10) := by
          linear_combination (-(Pinf 13 26 * Pinf 10 10 * (J 13 130 * J 39 130) * (J 3 10 * J 1 10))) * hR
  have a1 := E1_split
  have a13 := congrArg (S 13) E1_split
  rw [map_mul, S_P' 13 1 1 le_rfl le_rfl (rfl : 13 = 13 * 1) (rfl : 13 = 13 * 1), S_P' 13 1 2 le_rfl (by norm_num) (rfl : 13 = 13 * 1) (rfl : 26 = 13 * 2),
    S_P' 13 2 2 (by norm_num) (by norm_num) (rfl : 26 = 13 * 2) (rfl : 26 = 13 * 2)] at a13
  have hZ : (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10) * Pinf 1 1 * Pinf 13 13 ≠ 0 := by
    simp only [J]
    refine mul_ne_zero (mul_ne_zero ?_ (Pinf_ne _ _ le_rfl le_rfl)) (Pinf_ne _ _ (by norm_num) (by norm_num))
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) (Pinf_ne _ _ (by norm_num) (by norm_num)) <;>
      exact mul_ne_zero (mul_ne_zero (Pinf_ne _ _ (by norm_num) (by norm_num)) (Pinf_ne _ _ (by norm_num) (by norm_num)))
        (Pinf_ne _ _ (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hZ
  linear_combination key + ((S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) * Pinf 13 13 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10)) * a1 - ((S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) * Pinf 1 1 * (J 39 130 * J 13 130 * J 3 10 * J 1 10 * Pinf 10 10)) * a13

end Forty
