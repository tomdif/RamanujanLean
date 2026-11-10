/-
# Entry 3.28(ii): evaluation of the lattice identities of `E28b.lean`

* `E28p`: `f(−q⁸)(φ(−Q⁴)ψ(−q²) − q⁴ψ(−Q²)φ(−q⁴)) = f(−q²)f(−Q²) V(q²) ψ(−q²)` (Yesilyurt (3.13) at `q²`),
* `E28m`: `f(−q⁸)(φ(−Q⁴)ψ(−q²) + q⁴ψ(−Q²)φ(−q⁴)) = f(−q²)f(−Q²) V(q)V(−q) ψ(−q²)` (his (3.21)),
with `Q = q¹⁷`, `V(q) = G(q)G(Q²) + q⁷H(q)H(Q²)`.
-/
import RamanujanTau.Forty.E28b

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "ψ" => RamanujanTau.Septic.ramF 1 3

private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm24 : 1 ≤ 24 := by norm_num
private lemma hm136 : 1 ≤ 136 := by norm_num
private lemma hm170 : 1 ≤ 170 := by norm_num
private lemma hm510 : 1 ≤ 510 := by norm_num

/-- `V(q) = G(q)G(q³⁴) + q⁷H(q)H(q³⁴)`. -/
noncomputable def V28 : PowerSeries ℤ := G * S 34 G + X ^ 7 * H * S 34 H

lemma J8_24 : J 8 24 = Pinf 8 8 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom 8 8 24]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J170_510 : J 170 510 = Pinf 170 170 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom 170 170 510]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J136_170 : J 136 170 = J 34 170 := by simp only [J, Nat.reduceSub]; ring

theorem A4p_ι : A4p * ι (J 2 8) = ι (Pinf 8 8 * (J 68 136 * J 2 8 - X ^ 4 * (J 34 136 * J 4 8))) := by
  have h := A4p_c
  rw [θu' hm8 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm8 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm24 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm136 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num),
    θu' hm136 34 (e' := 34) (by norm_num) (by norm_num) (by norm_num), J8_24] at h
  simp only [map_mul, map_sub, ι_Xpow, Nat.cast_ofNat]
  linear_combination h

theorem A4m_ι : A4m * ι (J 2 8) = ι (Pinf 8 8 * (J 68 136 * J 2 8 + X ^ 4 * (J 34 136 * J 4 8))) := by
  have h := A4m_c
  rw [θu' hm8 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm8 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm24 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm136 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num),
    θu' hm136 34 (e' := 34) (by norm_num) (by norm_num) (by norm_num), J8_24] at h
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat]
  linear_combination h

/-- `B5p = f(−q²) f(−Q²) V(q²)`. -/
theorem B5p_ι : B5p = ι (Pinf 2 2 * Pinf 34 34 * (S 2 G * S 68 G + X ^ 14 * S 2 H * S 68 H)) := by
  have h := B5p_c
  have b34 := θ_bar hm170 34 (by norm_num) (by norm_num)
  have b68 := θ_bar hm170 68 (by norm_num) (by norm_num)
  norm_num at b34 b68
  rw [θu' hm510 170 (e' := 170) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm170 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num),
    θu' hm170 136 (e' := 136) (by norm_num) (by norm_num) (by norm_num)] at h
  have e1 := SG_E 2
  have e2 := SH_E 2
  have e3 := SG_E 68
  have e4 := SH_E 68
  norm_num at e1 e2 e3 e4
  have k := congrArg (S 17) K1
  simp only [map_mul, S_J' 17 4 10 (by norm_num) (by norm_num) (rfl : 68 = 17 * 4) (rfl : 170 = 17 * 10),
    S_J' 17 2 10 (by norm_num) (by norm_num) (rfl : 34 = 17 * 2) (rfl : 170 = 17 * 10),
    S_J' 17 8 20 (by norm_num) (by norm_num) (rfl : 136 = 17 * 8) (rfl : 340 = 17 * 20),
    S_J' 17 4 20 (by norm_num) (by norm_num) (rfl : 68 = 17 * 4) (rfl : 340 = 17 * 20),
    S_J' 17 10 20 (by norm_num) (by norm_num) (rfl : 170 = 17 * 10) (rfl : 340 = 17 * 20),
    S_P' 17 10 10 (by norm_num) (by norm_num) (rfl : 170 = 17 * 10) (rfl : 170 = 17 * 10),
    S_P' 17 4 4 (by norm_num) (by norm_num) (rfl : 68 = 17 * 4) (rfl : 68 = 17 * 4),
    S_P' 17 2 2 (by norm_num) (by norm_num) (rfl : 34 = 17 * 2) (rfl : 34 = 17 * 2)] at k
  have h' : B5p * ((θ hm170 34 (-1) * ι (J 34 170)) * (θ hm170 68 (-1) * ι (J 68 170))) = ι (J 170 510) *
      (ι (J 4 10) * ι (J 68 170) * (θ hm170 68 (-1) * ι (J 68 170)) * ι (J 34 170)
        + mono 14 1 * (ι (J 2 10) * ι (J 136 170) * (θ hm170 34 (-1) * ι (J 34 170)) * ι (J 68 170))) := by
    linear_combination (ι (J 34 170) * ι (J 68 170)) * h
  rw [b34, b68] at h'
  have key : J 170 510 * (J 4 10 * J 68 170 * (J 136 340 * J 170 340) * J 34 170
      + X ^ 14 * (J 2 10 * J 136 170 * (J 68 340 * J 170 340) * J 68 170)) =
      Pinf 2 2 * Pinf 34 34 * (S 2 G * S 68 G + X ^ 14 * S 2 H * S 68 H) *
        ((J 68 340 * J 170 340) * (J 136 340 * J 170 340)) := by
    apply mul_right_cancel₀ (Pinf_ne 68 68 (by norm_num) (by norm_num))
    rw [J170_510, J136_170, ← e1, ← e2, ← e3, ← e4] at *
    linear_combination (Pinf 2 2 * J 170 340 * Pinf 68 68 * (S 2 G * S 68 G + X ^ 14 * S 2 H * S 68 H)) * k
  have k2 := congrArg ι key
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat] at k2
  have hne : ι (J 68 340) * ι (J 170 340) * (ι (J 136 340) * ι (J 170 340)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 68 340 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 170 340 (by norm_num) (by norm_num))))
      (mul_ne_zero (ι_ne29 (J_ne29 136 340 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 170 340 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

lemma Ng_V28 : Ng V28 = Ng G * S 34 G - X ^ 7 * Ng H * S 34 H := by
  simp only [V28, map_add, map_mul, map_pow, Ng_S_ev 34 (by norm_num), Ng_X]
  ring

/-- `B5m = f(−q²) f(−Q²) V(q) V(−q)`. -/
theorem B5m_ι : B5m = ι (Pinf 2 2 * Pinf 34 34 * V28 * Ng V28) := by
  have h := B5m_c
  rw [θu' hm510 170 (e' := 170) (by norm_num) (by norm_num) (by norm_num),
    θu' hm170 34 (e' := 34) (by norm_num) (by norm_num) (by norm_num),
    θu' hm170 68 (e' := 68) (by norm_num) (by norm_num) (by norm_num),
    θu' hm170 136 (e' := 136) (by norm_num) (by norm_num) (by norm_num)] at h
  have c4 := θ_bar hm10 4 (by norm_num) (by norm_num)
  have c2 := θ_bar hm10 2 (by norm_num) (by norm_num)
  have c0 := θ_bar0 hm10
  norm_num at c4 c2 c0
  have h' : B5m * (ι (J 34 170) * ι (J 68 170)) * (ι (J 4 10) * ι (J 2 10) * ι (Pinf 10 20)) = ι (J 170 510) *
      ((θ hm10 4 (-1) * ι (J 4 10)) * ι (J 68 170) * ι (J 68 170) * ι (J 2 10) * ι (Pinf 10 20)
        - mono 14 1 * ((θ hm10 2 (-1) * ι (J 2 10)) * ι (J 136 170) * ι (J 34 170) * ι (J 4 10) * ι (Pinf 10 20))
        - mono 8 1 * ((θ hm10 0 (-1) * ι (Pinf 10 20)) * ι (J 34 170) * ι (J 68 170) * ι (J 4 10) * ι (J 2 10))) := by
    linear_combination (ι (J 4 10) * ι (J 2 10) * ι (Pinf 10 20)) * h
  rw [c4, c2, c0] at h'
  have g1 := GNgG
  have g2 := HNgH
  have g3 := E21c
  have p10 := congrArg (S 10) psi_mul
  simp only [map_mul, S_P' 10 1 2 (by norm_num) (by norm_num) (rfl : 10 = 10 * 1) (rfl : 20 = 10 * 2),
    S_P' 10 2 2 (by norm_num) (by norm_num) (rfl : 20 = 10 * 2) (rfl : 20 = 10 * 2)] at p10
  have e1 := SG_E 34
  have e2 := SH_E 34
  have sgh := SGH_E 34
  norm_num at e1 e2 sgh
  have key : J 170 510 * (J 8 20 * J 10 20 * J 68 170 * J 68 170 * J 2 10 * Pinf 10 20
      - X ^ 14 * (J 4 20 * J 10 20 * J 136 170 * J 34 170 * J 4 10 * Pinf 10 20)
      - X ^ 8 * (2 * Pinf 20 20 * J 34 170 * J 68 170 * J 4 10 * J 2 10)) =
      Pinf 2 2 * Pinf 34 34 * (G * S 34 G + X ^ 7 * H * S 34 H) * (Ng G * S 34 G - X ^ 7 * Ng H * S 34 H) *
        (J 34 170 * J 68 170 * (J 4 10 * J 2 10 * Pinf 10 20)) := by
    rw [J170_510, J136_170, ← e1, ← e2, ← sgh]
    linear_combination
      (-(S 34 G ^ 3 * S 34 H * Pinf 34 34 ^ 3 * J 2 10 * Pinf 10 20)) * g1
      + (X ^ 14 * S 34 G * S 34 H ^ 3 * Pinf 34 34 ^ 3 * J 4 10 * Pinf 10 20) * g2
      + (X ^ 7 * Pinf 34 34 ^ 3 * S 34 G ^ 2 * S 34 H ^ 2 * J 4 10 * J 2 10 * Pinf 10 20) * g3
      + (2 * X ^ 8 * Pinf 34 34 ^ 3 * S 34 G ^ 2 * S 34 H ^ 2 * J 4 10 * J 2 10) * p10
  have k2 := congrArg ι key
  simp only [map_mul, map_add, map_sub, map_ofNat, ι_Xpow, Nat.cast_ofNat] at k2
  rw [Ng_V28, V28]
  have hne : ι (J 34 170) * ι (J 68 170) * (ι (J 4 10) * ι (J 2 10) * ι (Pinf 10 20)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 34 170 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 68 170 (by norm_num) (by norm_num))))
      (mul_ne_zero (mul_ne_zero (ι_ne29 (J_ne29 4 10 (by norm_num) (by norm_num))) (ι_ne29 (J_ne29 2 10 (by norm_num) (by norm_num))))
        (ι_ne29 (Pinf_ne 10 20 (by norm_num) (by norm_num))))
  apply mul_right_cancel₀ hne
  simp only [map_mul, map_add, map_sub, ι_Xpow, Nat.cast_ofNat]
  linear_combination h' + k2

/-- Yesilyurt (3.13) at `q²`, cleared. -/
theorem E28p : Pinf 8 8 * (J 68 136 * J 2 8 - X ^ 4 * (J 34 136 * J 4 8)) =
    Pinf 2 2 * Pinf 34 34 * (S 2 G * S 68 G + X ^ 14 * S 2 H * S 68 H) * J 2 8 := by
  have h := A4p_ι
  rw [A4p_eq, B5p_ι, ← map_mul] at h
  exact (ι_inj h).symm

/-- Yesilyurt (3.21), cleared. -/
theorem E28m : Pinf 8 8 * (J 68 136 * J 2 8 + X ^ 4 * (J 34 136 * J 4 8)) =
    Pinf 2 2 * Pinf 34 34 * V28 * Ng V28 * J 2 8 := by
  have h := A4m_ι
  rw [A4m_eq, B5m_ι, ← map_mul] at h
  exact (ι_inj h).symm

end Forty
