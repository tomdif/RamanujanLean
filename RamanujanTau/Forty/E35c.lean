/-
# Entry 3.35: evaluations of the lattice identities of `E35b.lean` (`t = q`, `Q = q⁴⁷`)

* `Yo47_ι`: `Yo = q² f(−q⁴)f(−Q⁴) A(q²)`,      * `Ye47_ι`: `q² Ye = −f(−q⁴)f(−Q⁴) A(q⁴) B(−q²)`,
* `D5p47_ι`: `q² D5p = −f(−q²)f(−Q²) A(q²)`,   * `D5m47_ι`: `q² D5m = −f(−q²)f(−Q²) A(q) A(−q)`,
with Yesilyurt's `A(q) = H(q²)G(Q) − q⁹G(q²)H(Q)` and `B(q) = G(q)G(Q²) + q¹⁹H(q)H(Q²)`.
-/
import RamanujanTau.Forty.E35b

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "ψ" => RamanujanTau.Septic.ramF 1 3

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm470 : 1 ≤ 470 := by norm_num
private lemma hm940 : 1 ≤ 940 := by norm_num
private lemma hm2820 : 1 ≤ 2820 := by norm_num

private lemma mm (a b c : ℤ) (h : a + b = c) : (mono a 1 : L) * mono b 1 = mono c 1 := by
  rw [mono_mul, h]; norm_num

private lemma m0 : (mono 0 1 : L) = 1 := rfl

/-- Yesilyurt's `A(q) = H(q²)G(q⁴⁷) − q⁹G(q²)H(q⁴⁷)`. -/
noncomputable def A47 : PowerSeries ℤ := S 2 H * S 47 G - X ^ 9 * S 2 G * S 47 H
/-- Yesilyurt's `B(q) = G(q)G(q⁹⁴) + q¹⁹H(q)H(q⁹⁴)`. -/
noncomputable def B47 : PowerSeries ℤ := G * S 94 G + X ^ 19 * H * S 94 H

lemma J940_2820 : J 940 2820 = Pinf 940 940 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom 940 940 2820]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

theorem Yo47_ι : Yo47 = ι (X ^ 2 * Pinf 4 4 * Pinf 188 188 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H)) := by
  have h := Yo47_c
  rw [θu' hm940 94 (e' := 94) (by norm_num) (by norm_num) (by norm_num),
    θu' hm940 282 (e' := 282) (by norm_num) (by norm_num) (by norm_num),
    θu' hm2820 940 (e' := 940) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm940 188 (e' := 188) (by norm_num) (by norm_num) (by norm_num),
    θu' hm940 376 (e' := 376) (by norm_num) (by norm_num) (by norm_num)] at h
  have r1 := congrArg (S 94) R44a
  have r2 := congrArg (S 94) R44b
  simp only [map_mul, S_J' 94 2 10 (by norm_num) (by norm_num) (rfl : 188 = 94 * 2) (rfl : 940 = 94 * 10),
    S_J' 94 1 10 (by norm_num) (by norm_num) (rfl : 94 = 94 * 1) (rfl : 940 = 94 * 10),
    S_J' 94 4 10 (by norm_num) (by norm_num) (rfl : 376 = 94 * 4) (rfl : 940 = 94 * 10),
    S_J' 94 3 10 (by norm_num) (by norm_num) (rfl : 282 = 94 * 3) (rfl : 940 = 94 * 10),
    S_P' 94 10 10 (by norm_num) (by norm_num) (rfl : 940 = 94 * 10) (rfl : 940 = 94 * 10),
    S_P' 94 2 2 (by norm_num) (by norm_num) (rfl : 188 = 94 * 2) (rfl : 188 = 94 * 2)] at r1 r2
  have e1 := SG_E 4
  have e2 := SH_E 4
  norm_num at e1 e2
  have key : J 940 2820 * (X ^ 2 * (J 4 20 * J 188 940 * J 282 940) - X ^ 20 * (J 8 20 * J 376 940 * J 94 940)) =
      X ^ 2 * Pinf 4 4 * Pinf 188 188 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H) * (J 94 940 * J 282 940) := by
    rw [J940_2820, ← e1, ← e2]
    linear_combination (X ^ 2 * S 4 H * Pinf 4 4 * J 282 940) * r1 - (X ^ 20 * S 4 G * Pinf 4 4 * J 94 940) * r2
  have k2 := congrArg ι key
  simp only [map_mul, map_sub, ι_Xpow, Nat.cast_ofNat] at k2
  apply mul_right_cancel₀ (ι_ne29 (mul_ne_zero (J_ne29 94 940 (by norm_num) (by norm_num))
    (J_ne29 282 940 (by norm_num) (by norm_num))))
  rw [map_mul ι (J 94 940)]
  simp only [map_mul, map_sub, ι_Xpow, Nat.cast_ofNat]
  linear_combination h + k2

theorem Ye47_ι : mono 2 1 * Ye47 = -ι (Pinf 4 4 * Pinf 188 188 * (S 8 H * S 188 G - X ^ 36 * S 8 G * S 188 H) *
    (S 2 (Ng G) * S 188 G - X ^ 38 * S 2 (Ng H) * S 188 H)) := by
  have h := Ye47_c
  rw [θu' hm940 188 (e' := 188) (by norm_num) (by norm_num) (by norm_num),
    θu' hm940 376 (e' := 376) (by norm_num) (by norm_num) (by norm_num),
    θu' hm2820 940 (e' := 940) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm20 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num)] at h
  have g1 := SG_E 188
  have g2 := SH_E 188
  have gh := SGH_E 188
  norm_num at g1 g2 gh
  have a1 := congrArg (S 2) R46a
  have a2 := congrArg (S 2) R46b
  have a3 := congrArg (S 2) NgE33
  simp only [map_mul, map_add, S_S8 2 4, S_J' 2 3 10 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 20 = 2 * 10),
    S_J' 2 1 10 (by norm_num) (by norm_num) (rfl : 2 = 2 * 1) (rfl : 20 = 2 * 10),
    S_J' 2 5 10 (by norm_num) (by norm_num) (rfl : 10 = 2 * 5) (rfl : 20 = 2 * 10),
    S_P' 2 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 4 = 2 * 2), map_pow,
    show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _, Nat.reduceMul] at a1 a2 a3
  have key : J 940 2820 * (-(J 2 20 * J 376 940 * J 376 940) - X ^ 74 * (J 6 20 * J 188 940 * J 188 940)
      + X ^ 36 * (J 10 20 * J 188 940 * J 376 940)) =
      -(Pinf 4 4 * Pinf 188 188 * (S 8 H * S 188 G - X ^ 36 * S 8 G * S 188 H) *
        (S 2 (Ng G) * S 188 G - X ^ 38 * S 2 (Ng H) * S 188 H)) * (J 188 940 * J 376 940) := by
    rw [J940_2820, ← gh, ← g1, ← g2, a1, a2, ← a3]
    ring
  have k2 := congrArg ι key
  simp only [map_mul, map_add, map_sub, map_neg, ι_Xpow, Nat.cast_ofNat] at k2
  apply mul_right_cancel₀ (ι_ne29 (mul_ne_zero (J_ne29 188 940 (by norm_num) (by norm_num))
    (J_ne29 376 940 (by norm_num) (by norm_num))))
  rw [map_mul ι (J 188 940)]
  simp only [map_mul, map_add, map_sub, map_neg, ι_Xpow, Nat.cast_ofNat]
  linear_combination (mono 2 1) * h + k2
    - (ι (J 940 2820) * (ι (J 2 20) * ι (J 376 940) * ι (J 376 940))) * mm 2 (-2) 0 (by norm_num)
    - (ι (J 940 2820) * (ι (J 2 20) * ι (J 376 940) * ι (J 376 940))) * m0
    - (ι (J 940 2820) * (ι (J 6 20) * ι (J 188 940) * ι (J 188 940))) * mm 2 72 74 (by norm_num)
    + (ι (J 940 2820) * (ι (J 10 20) * ι (J 188 940) * ι (J 376 940))) * mm 2 34 36 (by norm_num)

theorem D5p47_ι : mono 2 1 * D5p47 = -ι (Pinf 2 2 * Pinf 94 94 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H)) := by
  have h := D5p47_c
  have b2 := θ_bar hm10 2 (by norm_num) (by norm_num)
  have b4 := θ_bar hm10 4 (by norm_num) (by norm_num)
  norm_num at b2 b4
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm470 188 (e' := 188) (by norm_num) (by norm_num) (by norm_num),
    θu' hm470 94 (e' := 94) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num)] at h
  have e1 := SG_E 4
  have e2 := SH_E 4
  have e3 := SG_E 94
  have e4 := SH_E 94
  norm_num at e1 e2 e3 e4
  have k := K1
  have h' : mono 2 1 * D5p47 * ((θ hm10 4 (-1) * ι (J 4 10)) * (θ hm10 2 (-1) * ι (J 2 10))) = ι (J 10 30) *
      (-(ι (J 188 470) * ι (J 8 10) * (θ hm10 2 (-1) * ι (J 2 10)) * ι (J 4 10))
        + mono 18 1 * (ι (J 94 470) * ι (J 4 10) * (θ hm10 4 (-1) * ι (J 4 10)) * ι (J 2 10))) := by
    linear_combination (mono 2 1 * ι (J 4 10) * ι (J 2 10)) * h
      - (ι (J 10 30) * ι (J 188 470) * ι (J 8 10) * θ hm10 2 (-1) * ι (J 2 10) * ι (J 4 10)) * mm 2 (-2) 0 (by norm_num)
      - (ι (J 10 30) * ι (J 188 470) * ι (J 8 10) * θ hm10 2 (-1) * ι (J 2 10) * ι (J 4 10)) * m0
      + (ι (J 10 30) * ι (J 94 470) * ι (J 4 10) * θ hm10 4 (-1) * ι (J 4 10) * ι (J 2 10)) * mm 2 16 18 (by norm_num)
  rw [b4, b2] at h'
  have key : J 10 30 * (-(J 188 470 * J 8 10 * (J 4 20 * J 10 20) * J 4 10)
      + X ^ 18 * (J 94 470 * J 4 10 * (J 8 20 * J 10 20) * J 2 10)) =
      -(Pinf 2 2 * Pinf 94 94 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H)) * ((J 8 20 * J 10 20) * (J 4 20 * J 10 20)) := by
    apply mul_right_cancel₀ (Pinf_ne 4 4 (by norm_num) (by norm_num))
    rw [J10_30, J8_10, ← e1, ← e2, ← e3, ← e4] at *
    linear_combination (Pinf 94 94 * Pinf 4 4 * J 10 20 * (X ^ 18 * S 94 H * S 4 G - S 94 G * S 4 H)) * k
  have k2 := congrArg ι key
  simp only [map_mul, map_add, map_neg, map_sub, ι_Xpow, Nat.cast_ofNat] at k2
  have hne : ι (J 8 20) * ι (J 10 20) * (ι (J 4 20) * ι (J 10 20)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 8 20 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 10 20 (by norm_num) (by norm_num))))
      (mul_ne_zero (ι_ne29 (J_ne29 4 20 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 10 20 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, map_neg, map_sub, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

lemma Ng_A47 : Ng A47 = S 2 H * S 47 (Ng G) + X ^ 9 * S 2 G * S 47 (Ng H) := by
  simp only [A47, map_sub, map_mul, map_pow, Ng_S_ev 2 (by norm_num), Ng_S_odd8 47 (by decide), Ng_X]
  ring

theorem D5m47_ι : mono 2 1 * D5m47 = -ι (Pinf 2 2 * Pinf 94 94 * A47 * Ng A47) := by
  have h := D5m47_c
  rw [θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num)] at h
  have c1 := θ_bar hm470 188 (by norm_num) (by norm_num)
  have c2 := θ_bar hm470 94 (by norm_num) (by norm_num)
  have c0 := θ_bar0 hm470
  norm_num at c1 c2 c0
  have h' : mono 2 1 * D5m47 * (ι (J 4 10) * ι (J 2 10)) * (ι (J 188 470) * ι (J 94 470) * ι (Pinf 470 940)) = ι (J 10 30) *
      (-((θ hm470 188 (-1) * ι (J 188 470)) * ι (J 8 10) * ι (J 2 10) * ι (J 94 470) * ι (Pinf 470 940))
        + mono 18 1 * ((θ hm470 94 (-1) * ι (J 94 470)) * ι (J 4 10) * ι (J 4 10) * ι (J 188 470) * ι (Pinf 470 940))
        - mono 56 1 * ((θ hm470 0 (-1) * ι (Pinf 470 940)) * ι (J 2 10) * ι (J 4 10) * ι (J 188 470) * ι (J 94 470))) := by
    linear_combination (mono 2 1 * ι (J 188 470) * ι (J 94 470) * ι (Pinf 470 940)) * h
      - (ι (J 10 30) * θ hm470 188 (-1) * ι (J 188 470) * ι (J 8 10) * ι (J 2 10) * ι (J 94 470) * ι (Pinf 470 940)) * mm 2 (-2) 0 (by norm_num)
      - (ι (J 10 30) * θ hm470 188 (-1) * ι (J 188 470) * ι (J 8 10) * ι (J 2 10) * ι (J 94 470) * ι (Pinf 470 940)) * m0
      + (ι (J 10 30) * θ hm470 94 (-1) * ι (J 94 470) * ι (J 4 10) * ι (J 4 10) * ι (J 188 470) * ι (Pinf 470 940)) * mm 2 16 18 (by norm_num)
      - (ι (J 10 30) * θ hm470 0 (-1) * ι (Pinf 470 940) * ι (J 2 10) * ι (J 4 10) * ι (J 188 470) * ι (J 94 470)) * mm 2 54 56 (by norm_num)
  rw [c1, c2, c0] at h'
  have G47 := congrArg (S 47) GNgG
  have H47 := congrArg (S 47) HNgH
  have E47 := congrArg (S 47) E21c
  have p470 := congrArg (S 470) psi_mul
  simp only [map_mul, map_sub, map_ofNat, map_pow, S_S8 47 10, show (S 47) X = X ^ 47 from RankProof.Ea_X 47 _,
    S_J' 47 4 10 (by norm_num) (by norm_num) (rfl : 188 = 47 * 4) (rfl : 470 = 47 * 10),
    S_J' 47 2 10 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 470 = 47 * 10),
    S_J' 47 8 20 (by norm_num) (by norm_num) (rfl : 376 = 47 * 8) (rfl : 940 = 47 * 20),
    S_J' 47 4 20 (by norm_num) (by norm_num) (rfl : 188 = 47 * 4) (rfl : 940 = 47 * 20),
    S_J' 47 10 20 (by norm_num) (by norm_num) (rfl : 470 = 47 * 10) (rfl : 940 = 47 * 20),
    S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2),
    S_P' 470 1 2 (by norm_num) (by norm_num) (rfl : 470 = 470 * 1) (rfl : 940 = 470 * 2),
    S_P' 470 2 2 (by norm_num) (by norm_num) (rfl : 940 = 470 * 2) (rfl : 940 = 470 * 2), Nat.reduceMul] at G47 H47 E47 p470
  have e1 := SG_E 2
  have e2 := SH_E 2
  have sgh := SGH_E 2
  norm_num at e1 e2 sgh
  have key : J 10 30 * (-(J 376 940 * J 470 940 * J 8 10 * J 2 10 * J 94 470 * Pinf 470 940)
      + X ^ 18 * (J 188 940 * J 470 940 * J 4 10 * J 4 10 * J 188 470 * Pinf 470 940)
      - X ^ 56 * (2 * Pinf 940 940 * J 2 10 * J 4 10 * J 188 470 * J 94 470)) =
      -(Pinf 2 2 * Pinf 94 94 * (S 2 H * S 47 G - X ^ 9 * S 2 G * S 47 H) *
        (S 2 H * S 47 (Ng G) + X ^ 9 * S 2 G * S 47 (Ng H))) *
        (J 4 10 * J 2 10 * (J 188 470 * J 94 470 * Pinf 470 940)) := by
    rw [J10_30, J8_10, ← e1, ← e2, ← sgh]
    linear_combination
      (S 2 G * S 2 H ^ 3 * Pinf 2 2 ^ 3 * J 94 470 * Pinf 470 940) * G47
      - (X ^ 18 * S 2 G ^ 3 * S 2 H * Pinf 2 2 ^ 3 * J 188 470 * Pinf 470 940) * H47
      + (X ^ 9 * Pinf 2 2 ^ 3 * S 2 G ^ 2 * S 2 H ^ 2 * J 188 470 * J 94 470 * Pinf 470 940) * E47
      + (2 * X ^ 56 * Pinf 2 2 ^ 3 * S 2 G ^ 2 * S 2 H ^ 2 * J 188 470 * J 94 470) * p470
  have k2 := congrArg ι key
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, ι_Xpow, Nat.cast_ofNat] at k2
  rw [Ng_A47, A47]
  have hne : ι (J 4 10) * ι (J 2 10) * (ι (J 188 470) * ι (J 94 470) * ι (Pinf 470 940)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 4 10 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 2 10 (by norm_num) (by norm_num))))
      (mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 188 470 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 94 470 (by norm_num) (by norm_num))))
        (ι_ne29 (Pinf_ne 470 940 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, map_sub, map_neg, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

end Forty
