/-
# Entry 3.35: Yesilyurt's product formula `A(q)B(q) = (q² + χ(q)χ(q⁴⁷))(1 + 2q⁴/(χ(−q²)χ(−q⁹⁴)))`

With `A = H(q²)G(q⁴⁷) − q⁹G(q²)H(q⁴⁷)`, `B = G(q)G(q⁹⁴) + q¹⁹H(q)H(q⁹⁴)` (`E35c.lean`), `u = χ(q)χ(q⁴⁷)`,
`w = χ(−q²)χ(−q⁹⁴)`:
* `E1_47` (Yesilyurt (5.6)): `f(−q)f(−Q) A(q) = f(−q²)f(−Q²) (A(q²)B(−q) − q²A(q))`, from `L47p`;
* `E2_47`: `f(−q²)f(−Q²) A(q)A(−q) = A(q²) (f(−q²)f(−Q²) + 2q⁴ f(−q⁴)f(−Q⁴))`, from `L47m − L47p` (the identity of
  Yesilyurt's closing remark, with `q⁴` in place of his misprinted `q²`);
* `entry_3_35_AB`: `A(q)B(q) = (q² + u)(1 + 2q⁴/w)` (his (5.16) in the form of his closing remark).
Entry 3.35 itself is equivalent to this together with the degree-47 modular equation (his (5.24)); see
`docs/FORTY_IDENTITIES.md`.
-/
import RamanujanTau.Forty.E35c
import RamanujanTau.Forty.E29
import RamanujanTau.Forty.E20

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

lemma S2_A47 : S 2 A47 = S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H := by
  simp only [A47, map_sub, map_mul, map_pow, S_S8 2 2, S_S8 2 47, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  ring

lemma Ng_B47 : Ng B47 = Ng G * S 94 G - X ^ 19 * Ng H * S 94 H := by
  simp only [B47, map_add, map_mul, map_pow, Ng_S_ev 94 (by norm_num), Ng_X]
  ring

lemma cc_A47 : constantCoeff A47 = 1 := by
  simp only [A47, map_sub, map_mul, map_pow, constantCoeff_X, cc_S, cc_G, cc_H]
  norm_num

lemma A47_ne : S 2 A47 ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [cc_S, cc_A47, map_zero] at this
  exact one_ne_zero this

private lemma two_mono_ne : (mono 2 1 : L) ≠ 0 := by
  simp [mono]

/-- Yesilyurt (5.6), cleared. -/
theorem E1_47 : Pinf 1 1 * Pinf 47 47 * A47 =
    Pinf 2 2 * Pinf 94 94 * (S 2 A47 * Ng B47) - X ^ 2 * (Pinf 2 2 * Pinf 94 94 * A47) := by
  have hP := congrArg (mono 2 1 * ·) D5p47_eq
  simp only [mul_add] at hP
  rw [D5p47_ι, Ye47_ι, Yo47_ι] at hP
  have hP' : ι (Pinf 2 2 * Pinf 94 94 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H)) =
      ι (Pinf 4 4 * Pinf 188 188 * (S 8 H * S 188 G - X ^ 36 * S 8 G * S 188 H) *
        (S 2 (Ng G) * S 188 G - X ^ 38 * S 2 (Ng H) * S 188 H)
        - X ^ 4 * Pinf 4 4 * Pinf 188 188 * (S 4 H * S 94 G - X ^ 18 * S 4 G * S 94 H)) := by
    simp only [map_mul, map_sub, ι_Xpow, Nat.cast_ofNat] at hP ⊢
    have m : (mono 2 1 : L) ^ 2 = mono 4 1 := by rw [sq, mono_mul]; norm_num
    linear_combination -hP - (ι (Pinf 4 4) * ι (Pinf 188 188) * (ι (S 4 H) * ι (S 94 G) - mono 18 1 * ι (S 4 G) * ι (S 94 H))) * m
  have h := ι_inj hP'
  apply S_inj 2
  simp only [map_mul, map_sub, S_P' 2 1 1 le_rfl le_rfl (rfl : 2 = 2 * 1) (rfl : 2 = 2 * 1),
    S_P' 2 47 47 (by norm_num) (by norm_num) (rfl : 94 = 2 * 47) (rfl : 94 = 2 * 47),
    S_P' 2 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 4 = 2 * 2),
    S_P' 2 94 94 (by norm_num) (by norm_num) (rfl : 188 = 2 * 94) (rfl : 188 = 2 * 94),
    Ng_B47, S2_A47, map_add, map_pow, S_S8 2 4, S_S8 2 94, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    Nat.reduceMul]
  linear_combination h

/-- `f(−q²)f(−Q²) A(q)A(−q) = A(q²)(f(−q²)f(−Q²) + 2q⁴ f(−q⁴)f(−Q⁴))`. -/
theorem E2_47 : Pinf 2 2 * Pinf 94 94 * A47 * Ng A47 =
    S 2 A47 * (Pinf 2 2 * Pinf 94 94 + 2 * X ^ 4 * (Pinf 4 4 * Pinf 188 188)) := by
  have hP := congrArg (mono 2 1 * ·) D5p47_eq
  have hM := congrArg (mono 2 1 * ·) D5m47_eq
  simp only [mul_add, mul_sub] at hP hM
  rw [D5p47_ι, Ye47_ι, Yo47_ι] at hP
  rw [D5m47_ι, Ye47_ι, Yo47_ι] at hM
  have m : (mono 2 1 : L) ^ 2 = mono 4 1 := by rw [sq, mono_mul]; norm_num
  have key : ι (Pinf 2 2 * Pinf 94 94 * A47 * Ng A47) =
      ι (S 2 A47 * (Pinf 2 2 * Pinf 94 94 + 2 * X ^ 4 * (Pinf 4 4 * Pinf 188 188))) := by
    rw [S2_A47]
    simp only [map_mul, map_sub, map_add, map_ofNat, ι_Xpow, Nat.cast_ofNat] at hP hM ⊢
    linear_combination hP - hM
      + 2 * (ι (Pinf 4 4) * ι (Pinf 188 188) * (ι (S 4 H) * ι (S 94 G) - mono 18 1 * ι (S 4 G) * ι (S 94 H))) * m
  exact ι_inj key

lemma Ng_P4747 : Ng (Pinf 47 47) = Pinf 94 94 * chip 47 := by
  have h := Ng_S_odd8 47 (by decide) (Pinf 1 1)
  rw [S_Pinf 47 1 1 le_rfl le_rfl, Ng_E1, map_mul, S_Pinf 47 2 2 (by norm_num) (by norm_num),
    show S 47 (chip 1) = chip 47 by rw [chip, S_one]; rfl] at h
  exact h

/-- Yesilyurt's product formula for Entry 3.35:
`{G(q)G(q⁹⁴) + q¹⁹H(q)H(q⁹⁴)}{G(q⁴⁷)H(q²) − q⁹G(q²)H(q⁴⁷)} = (q² + χ(q)χ(q⁴⁷))(1 + 2q⁴/(χ(−q²)χ(−q⁹⁴)))`. -/
theorem entry_3_35_AB : (G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H) =
    (X ^ 2 + chip 1 * chip 47) * (1 + 2 * X ^ 4 * Ring.inverse (chim 2 * chim 94)) := by
  have e1 := E1_47
  have ne1 := congrArg Ng e1
  simp only [map_mul, map_sub, map_pow, Ng_Ng, Ng_X, Ng_E1, Ng_P4747, Ng_S_ev 2 (by norm_num),
    Ng_Pinf_even 1 1 le_rfl le_rfl, Ng_Pinf_even 47 47 (by norm_num) (by norm_num)] at ne1
  simp only [Nat.reduceMul] at ne1
  have e2 := E2_47
  have a2 : Pinf 2 2 = Pinf 2 4 * Pinf 4 4 := by
    have h := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at h
    norm_num at h
    exact h
  have a94 : Pinf 94 94 = Pinf 94 188 * Pinf 188 188 := by
    have h := congrArg (S 47) a2
    simp only [S_P' 47 2 2 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 94 = 47 * 2),
      S_P' 47 2 4 (by norm_num) (by norm_num) (rfl : 94 = 47 * 2) (rfl : 188 = 47 * 4),
      S_P' 47 4 4 (by norm_num) (by norm_num) (rfl : 188 = 47 * 4) (rfl : 188 = 47 * 4), map_mul] at h
    exact h
  simp only [chim, Nat.reduceMul]
  set A := A47 with hA
  set B := B47 with hB
  set u := chip 1 * chip 47 with hu
  set w := Pinf 2 4 * Pinf 94 188 with hw
  have hD : Pinf 2 2 * Pinf 94 94 ≠ 0 := mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 94 94 (by norm_num) (by norm_num))
  have st2 : S 2 A * B = Ng A * (u + X ^ 2) := by
    apply mul_left_cancel₀ hD
    linear_combination -ne1
  have st3 : Pinf 2 2 * Pinf 94 94 * (A * B) = (Pinf 2 2 * Pinf 94 94 + 2 * X ^ 4 * (Pinf 4 4 * Pinf 188 188)) * (u + X ^ 2) := by
    apply mul_left_cancel₀ A47_ne
    linear_combination (Pinf 2 2 * Pinf 94 94 * A) * st2 + (u + X ^ 2) * e2
  have st4 : w * (A * B) = (w + 2 * X ^ 4) * (u + X ^ 2) := by
    apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 4 4 (by norm_num) (by norm_num)) (Pinf_ne 188 188 (by norm_num) (by norm_num)))
    rw [a2, a94] at st3
    linear_combination st3
  have hwu : IsUnit w := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).mul (isUnit_Pinf 94 188 (by norm_num) (by norm_num))
  have iw := Ring.mul_inverse_cancel _ hwu
  apply mul_left_cancel₀ hwu.ne_zero
  rw [show (G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H) = B * A by
    rw [hA, hB, A47, B47]; ring]
  linear_combination st4 - 2 * X ^ 4 * (u + X ^ 2) * iw

end Forty
