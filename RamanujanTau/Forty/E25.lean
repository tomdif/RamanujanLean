/-
# Entry 3.25: `G(−q)G(q⁹) − q²H(−q)H(q⁹) = χ(−q)χ(q⁹)/χ(−q⁶)` (Bressoud)

The second proof of Berndt et al. (§28):
* Rogers' Theorem 4.5 is the exact cover `B = (1 1; −2 3)` of `f(q⁶,q¹²) f(−q)` (`L3_25`, Type I).
* The two braces collapse by the quintuple product at `c = −1` (as in Entry 3.30).
* The product forms `f(−q²)G(−q) = f(−q¹⁰)f(−q²,−q⁸)/f(q,q⁹)` and the analogue for `H(−q)` (`NgG_E2`, `NgH_E2`)
  finish the proof.
-/
import RamanujanTau.Forty.E13
import RamanujanTau.Forty.NgOdd

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num

private lemma hm3 : 1 ≤ 3 := by norm_num
private lemma hm18 : 1 ≤ 18 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm45 : 1 ≤ 45 := by norm_num

/-- Entry 3.25: `B = (1 1; -2 3)`, shifts `i (1, 0)`, `i ∈ {(-5), (-4), (-3), (-2), (-1)}`. -/
def B3_25 : ECS where
  b11 := 1
  b12 := 1
  b21 := (-2)
  b22 := 3
  r1 := 1
  r2 := 0
  I := {(-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 3 * n - (-5)) % 5 + (-5)), by simp only [mem_insert, mem_singleton]; omega,
    ((3 * (m - 1 * ((1 * m + 3 * n - (-5)) % 5 + (-5))) - 1 * (n - 0 * ((1 * m + 3 * n - (-5)) % 5 + (-5)))) / 5), ((1 * (n - 0 * ((1 * m + 3 * n - (-5)) % 5 + (-5))) - (-2) * (m - 1 * ((1 * m + 3 * n - (-5)) % 5 + (-5)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_25 : θ hm18 6 (-1) * θ hm3 1 1 = (θ hm30 13 (-1) * θ hm45 18 1) - (mono 1 1 * (θ hm30 7 (-1) * θ hm45 18 1)) - (mono 2 1 * (θ hm30 11 (-1) * θ hm45 9 1)) + (mono 5 1 * (θ hm30 1 (-1) * θ hm45 9 1)) := by
  have h := θθ_lattice hm18 hm3 hm30 hm45 6 1 (by norm_num : (-1 : ℂ) ≠ 0) one_ne_zero B3_25 rfl rfl
    (by norm_num [B3_25]) (by norm_num [B3_25]) (by norm_num [B3_25])
  simp only [B3_25] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfr1 hm45 18 (-1) (-18) (-1) (e := (-18)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm45 9 (-2) (-63) 1 (e := (-54)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 11 (-2) (-52) 1 (e := (-41)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 5 (-1) (-5) 1 (e := (-5)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 1 (-2) (by norm_num : (-1 : ℂ) ≠ 0) (-88) 1 (e := (-59)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 13 (-3) (by norm_num : (-1 : ℂ) ≠ 0) (-141) 1 (e := (-77)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 7 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-23) 1 (e := (-23)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm45 18 (-2) one_ne_zero (-99) 1 (e := (-72)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm45 9 (-1) one_ne_zero (-36) (-1) (e := (-36)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm45 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- `f(−q²)H(−q) · f(q³,q⁷) = f(−q¹⁰) f(−q⁴,−q⁶) f(−q³,−q⁷)` (product form). -/
lemma NgH_E2 : (Ng H * Pinf 2 2) * (J 6 20 * J 10 20) = Pinf 10 10 * J 4 10 * J 3 10 := by
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

/-- `f(−q²)G(−q) · f(q,q⁹) = f(−q¹⁰) f(−q²,−q⁸) f(−q,−q⁹)` (product form). -/
lemma NgG_E2 : (Ng G * Pinf 2 2) * (J 2 20 * J 10 20) = Pinf 10 10 * J 2 10 * J 1 10 := by
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

/-- `L3_25` with the two quintuple collapses. -/
theorem M3_25 : θ hm18 6 (-1) * θ hm3 1 1 * (θ hm10 3 (-1) * θ hm10 1 (-1)) =
    θ hm30 10 1 * (θ hm45 18 1 * θ hm10 3 (-1) * θ hm10 2 1 - mono 2 1 * (θ hm45 9 1 * θ hm10 1 (-1) * θ hm10 4 1)) := by
  have hLat := L3_25
  have Q3 := quintm hm10 hm30 rfl 3 19 29 10 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q4 := quintm hm10 hm30 rfl 1 13 23 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm30 11 19 (by norm_num), θ_reflm hm30 1 29 (by norm_num), θ_refl1 hm10 4 6 (by norm_num)] at Q3
  rw [θ_reflm hm30 7 23 (by norm_num)] at Q4
  have m1 : (mono 2 1 : L) * mono 3 1 = mono 5 1 := by rw [mono_mul]; norm_num
  linear_combination (θ hm10 3 (-1) * θ hm10 1 (-1)) * hLat
    + (θ hm45 18 1 * θ hm10 3 (-1)) * Q4 - (mono 2 1 * θ hm45 9 1 * θ hm10 1 (-1)) * Q3
    - (θ hm30 1 (-1) * θ hm45 9 1 * θ hm10 3 (-1) * θ hm10 1 (-1)) * m1

/-- the product form of `M3_25`. -/
theorem P3_25 : (J 12 36 * J 18 36) * J 1 3 * ((J 6 20 * J 10 20) * (J 2 20 * J 10 20)) =
    J 10 30 * J 6 18 * (J 18 45 * (J 6 20 * J 10 20) * J 1 10 * J 2 10
      - PowerSeries.X ^ 2 * (J 9 45 * (J 2 20 * J 10 20) * J 3 10 * J 4 10)) := by
  apply ι_inj
  have h := congrArg (· * (ι (J 6 18) * ι (J 3 10) * ι (J 1 10))) M3_25
  simp only at h
  have hb18 := θ_bar hm18 6 (by norm_num) (by norm_num)
  have hb3 := θ_bar hm10 3 (by norm_num) (by norm_num)
  have hb1 := θ_bar hm10 1 le_rfl (by norm_num)
  norm_num at hb18 hb3 hb1
  rw [θu' hm3 1 (e' := 1) (by norm_num) le_rfl (by norm_num), θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm45 18 (e' := 18) (by norm_num) (by norm_num) (by norm_num), θu' hm45 9 (e' := 9) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, ι_Xpow] at hb18 hb3 hb1 h ⊢
  push_cast at h ⊢
  linear_combination h - (ι (J 1 3) * (θ hm10 3 (-1) * ι (J 3 10)) * (θ hm10 1 (-1) * ι (J 1 10))) * hb18
    - (ι (J 1 3) * (ι (J 12 36) * ι (J 18 36)) * (θ hm10 1 (-1) * ι (J 1 10))) * hb3
    - (ι (J 1 3) * (ι (J 12 36) * ι (J 18 36)) * (ι (J 6 20) * ι (J 10 20))) * hb1
    + (ι (J 10 30) * ι (J 6 18) * ι (J 18 45) * ι (J 2 10) * ι (J 1 10)) * hb3
    - (ι (J 10 30) * ι (J 6 18) * mono 2 1 * ι (J 9 45) * ι (J 4 10) * ι (J 3 10)) * hb1

/-- **Entry 3.25** (Bressoud; Berndt et al. §28): `G(−q)G(q⁹) − q²H(−q)H(q⁹) = χ(−q)χ(q⁹)/χ(−q⁶)`. -/
theorem entry_3_25 : Ng G * S 9 G - PowerSeries.X ^ 2 * Ng H * S 9 H = chim 1 * chip 9 * Ring.inverse (chim 6) := by
  apply eq_mul_inv_of (isUnit_Pinf 6 12 (by norm_num) (by norm_num))
  have hc := chip_mul 9
  norm_num at hc
  have e1 := SG_E 9
  have e2 := SH_E 9
  norm_num at e1 e2
  have kG := NgG_E2
  have kH := NgH_E2
  have jB : J 10 30 = Pinf 10 10 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 30]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
  have P := P3_25
  rw [jB] at P
  have K : J 12 36 * J 18 36 * J 1 3 * (Pinf 6 12 * Pinf 9 18) = Pinf 1 2 * Pinf 18 36 * (J 6 18 * Pinf 2 2 * Pinf 9 9) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 36]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have W0 : J 6 18 * ((J 6 20 * J 10 20) * (J 2 20 * J 10 20)) * Pinf 2 2 * Pinf 9 9 * Pinf 9 18 ≠ 0 := by
    simp only [J]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ ?_)))
      (Pinf_ne _ _ (by norm_num) (by norm_num))) (Pinf_ne _ _ (by norm_num) (by norm_num))) (Pinf_ne _ _ (by norm_num) (by norm_num)) <;>
      exact mul_ne_zero (mul_ne_zero (Pinf_ne _ _ (by norm_num) (by norm_num)) (Pinf_ne _ _ (by norm_num) (by norm_num)))
        (Pinf_ne _ _ (by norm_num) (by norm_num))
  apply mul_left_cancel₀ W0
  simp only [chim, Nat.reduceMul]
  linear_combination (Pinf 6 12 * Pinf 9 18 * J 6 18 * Pinf 2 2 * ((J 6 20 * J 10 20) * (J 2 20 * J 10 20))) * Ng G * e1 - (Pinf 6 12 * Pinf 9 18 * J 6 18 * Pinf 2 2 * ((J 6 20 * J 10 20) * (J 2 20 * J 10 20))) * PowerSeries.X ^ 2 * Ng H * e2
    + (Pinf 6 12 * Pinf 9 18 * J 6 18 * J 18 45 * (J 6 20 * J 10 20)) * kG
    - (Pinf 6 12 * Pinf 9 18 * J 6 18 * PowerSeries.X ^ 2 * J 9 45 * (J 2 20 * J 10 20)) * kH
    - (Pinf 6 12 * Pinf 9 18) * P + ((J 6 20 * J 10 20) * (J 2 20 * J 10 20)) * K
    - (((J 6 20 * J 10 20) * (J 2 20 * J 10 20)) * Pinf 1 2 * J 6 18 * Pinf 2 2 * Pinf 9 9) * hc
end Forty
